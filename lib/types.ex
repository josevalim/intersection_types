defmodule Types do
  @moduledoc """
  Type inference and checking for Elixir.
  """

  alias Inspect.Algebra, as: A

  @doc """
  Convert the types AST to an algebra document.
  """
  def types_to_algebra(types) do
    types_to_algebra(types, %{counter: 0, vars: %{}}) |> elem(0)
  end

  defp types_to_algebra(types, state) do
    {types, state} = Enum.map_reduce(types, state, &type_to_algebra/2)
    {A.group(A.fold_doc(types, &A.glue(A.concat(&1, " |"), &2))), state}
  end

  # {:value, val}
  # {:fn, [clauses], arity}
  # {:tuple, args, arity}
  # {:var, var_ctx, var_key}
  # {:intersection, left, right} (appears only on the left side)
  # :integer
  # :atom

  defp type_to_algebra({:value, val}, state) do
    {inspect(val), state}
  end
  defp type_to_algebra({:tuple, args, _arity}, state) do
    {args, state} = args_to_algebra(args, state)
    {A.surround("{", args, "}"), state}
  end
  defp type_to_algebra({:fn, clauses, _arity}, state) do
    {clauses, state} = clauses_to_algebra(clauses, state)
    {A.surround("(", clauses, ")"), state}
  end
  defp type_to_algebra({:var, _, var_counter}, %{vars: vars, counter: counter} = state) do
    case vars do
      %{^var_counter => letter} ->
        {letter, state}
      %{} ->
        letter = counter_to_letter(counter)
        vars = Map.put(vars, var_counter, letter)
        {letter, %{state | vars: vars, counter: counter + 1}}
    end
  end
  defp type_to_algebra({:intersection, left, right}, state) do
    {left_doc, state} = types_to_algebra(left, state)
    {right_doc, state} = types_to_algebra(right, state)
    left = maybe_surround(left_doc, left)
    right = maybe_surround(right_doc, right)
    {A.glue(A.concat(left, " ^^^"), right), state}
  end

  defp type_to_algebra(:atom, state), do: {"atom()", state}
  defp type_to_algebra(:integer, state), do: {"integer()", state}
  
  defp args_to_algebra(args, state) do
    {args, state} = Enum.map_reduce(args, state, &types_to_algebra/2)
    {A.fold_doc(args, &A.glue(A.concat(&1, ","), &2)), state}
  end

  defp clauses_to_algebra(clauses, state) do
    {clauses, state} =
      Enum.map_reduce(clauses, state, fn {head, body, _}, state ->
        {head, state} = args_to_algebra(head, state)
        {body, state} = types_to_algebra(body, state)
        {A.nest(A.glue(A.concat(head, " ->"), body), 2), state}
      end)
    {A.fold_doc(clauses, &A.glue(A.concat(&1, ";"), &2)), state}
  end

  defp maybe_surround(doc, [_]), do: doc
  defp maybe_surround(doc, _), do: A.surround("(", doc, ")")

  defp counter_to_letter(counter) do
    div = div(counter, 26)
    rem = rem(counter, 26)

    if div > 0 do
      <<?a + rem, counter_to_letter(div) :: binary>>
    else
      <<?a + rem>>
    end
  end

  ## Patterns
  # 1. adding types/patterns to receive
  # 2. mixing typed with non-typed
  # 3. the cost of having duplicate syntax

  ## Function annotations
  # 1. Annotations may have multiple clauses. Each clause must have at least one matching implementation.
  # 2. Should we force a explicit type on fn true -> true; _ -> x end? If so, what to do on catch all?

  ## Guards
  # Must perform exhaustion check based on patterns
  # Must perform exhaustion check for base types (integers, atoms, floats, etc)
  # Pattern matches {a, a} also require an exaustion check

  ## State helpers

  # The :vars map keeps all Elixir variables and their types
  # The :match map keeps all Elixir variables defined in a match
  # The :inferred map keeps track of all inferred types (they have a counter)
  # The :rewrite map keeps track of all counters that must be rewritten (for finding recursive calls)
  # The :rank map keeps variables defined in the first rank
  @state %{vars: %{}, match: %{}, inferred: %{}, rewrite: %{}, counter: 0, rank: nil}

  defp replace_vars(state, %{vars: vars}) do
    %{state | vars: vars}
  end

  defp lift_vars(%{vars: vars1} = state, %{vars: vars2}) do
    %{state | vars: Map.merge(vars2, vars1)}
  end

  ## Forbidden
  # [foo | bar] (developers must use cons(...) to avoid ambiguity)

  ## Built-in Patterns
  # pattern number() :: integer() | float()

  ## Built-in Types
  # type list(a) :: empty_list() | cons(a, list(a))
  # type improper_list(a) :: empty_list() | cons(a, list(a) | a)

  ## Implemented Patterns
  # pattern boolean() :: true | false
  # pattern atom()
  # pattern integer()

  ## Literals
  # integer
  # atom
  # tuples

  ## Representation
  # {:value, val}
  # {:fn, [clauses], arity}
  # {:defn, [clauses], arity}
  # {:tuple, args, arity}
  # {:var, var_ctx, var_key}
  # {:intersection, left, right} (appears only on the left side)
  # :integer
  # :atom

  # TODO: Use inline_list_funcs for performance.
  # TODO: Implement generic type traversal functions.

  @doc """
  Converts the given Type AST to its inner type.
  """
  def ast_to_types(ast, state \\ @state)

  def ast_to_types({:boolean, _, []}, state) do
    ok([{:value, true}, {:value, false}], state)
  end
  def ast_to_types({:integer, _, []}, state) do
    ok([:integer], state)
  end
  def ast_to_types({:atom, _, []}, state) do
    ok([:atom], state)
  end
  def ast_to_types(other, state) do
    literal(other, state, &ast_to_types/2)
  end

  @doc """
  Unifies the types on left and right.

  All of the types on the right must match at least one type
  on the left. Internally we keep track of the following variables:

    * lvars - variables already inferred for the left side.
      It always starts as an empty map.
    * rvars - variables already inferred for the right side.
    * type_lvars - variables inferred for the left side for
      each type on the right. Starts as lvars.
    * type_lvars - variables inferred for the right side for
      each type on the right. Starts as rvars.
    * acc_rvars - variables inferred for the right side from
      the caller loop.

  Any variable found during unification must intersect with
  whatever variable found on the proper `?vars`. For example,
  if a variable is found on the right side, it must intersect
  with any inferred value in `rvars`.

  Unification works by pinning each specific type on the `right`
  and finding a `left` type that matches. If such type exists
  and variables are involved, `type_?vars` will be properly
  updated and be set as the main `?vars` once we move to the
  next type.

  `acc_rvars` is only updated by this function, never read.
  `acc_rvars` keeps inference information across the caller
  loop. For example, if we are unifying against multiple clauses,
  `acc_rvars` will keep unifying information for all clauses.

  Notice there is no such thing as `acc_lvars` since it always
  means an inner scope (that's not true for matches but in such
  cases they are explicitly merged into `acc_rvars` afterwards).
  """
  # TODO: Include error reason every time unification fails.
  def unify(left, right, rvars, acc_rvars) do
    unify(left, right, %{}, rvars, %{}, rvars, acc_rvars)
  end

  defp unify(left, right, lvars, rvars, temp_lvars, temp_rvars, acc_rvars) do
    unify(left, right, lvars, rvars, temp_lvars, temp_rvars, acc_rvars, :equal, [])
  end

  defp unify([left | lefties], righties, lvars, rvars,
             type_lvars, type_rvars, acc_rvars, kind, matched) do
    unify(left, righties, lvars, rvars, type_lvars, type_rvars,
          acc_rvars, lefties, kind, matched, [])
  end
  defp unify([], _righties, _lvars, _rvars,
             type_lvars, type_rvars, acc_rvars, kind, matched) do
    {kind, matched, type_lvars, type_rvars, acc_rvars}
  end

  defp unify(left, [right | righties], lvars, rvars, type_lvars, type_rvars,
             acc_rvars, lefties, kind, matched, unmatched) do
    case unify_each(left, right, lvars, rvars, type_lvars, type_rvars, acc_rvars) do
      {:equal, _equal, type_lvars, type_rvars, acc_rvars} ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_rvars, lefties, kind, [right | matched], unmatched)
      {:subset, subset, type_lvars, type_rvars, acc_rvars} ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_rvars, lefties, unify_kind(:subset, kind), [subset | matched], [right | unmatched])
      :disjoint ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_rvars, lefties, :disjoint, matched, [right | unmatched])
    end
  end
  defp unify(_left, [], _lvars, _rvars,
             type_lvars, type_rvars, acc_rvars, lefties, kind, matched, righties) do
    unify(lefties, righties, type_lvars, type_rvars,
          type_lvars, type_rvars, acc_rvars, kind, matched)
  end

  defp unify_kind(:disjoint, _), do: :disjoint
  defp unify_kind(_, :disjoint), do: :disjoint
  defp unify_kind(:subset, :equal), do: :subset
  defp unify_kind(:equal, :subset), do: :subset
  defp unify_kind(type, type), do: type

  # Once an intersection is found, we need to solve it by expanding
  # the function into an intersection as described in:
  # "Expansion: the Crucial Mechanism for Type Inference with Intersection Types"
  # Sébastien Carlier, J. B. Wells (2005)
  defp unify_each({:intersection, inter_left, inter_right}, {:fn, clauses, arity} = right,
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    {left_clauses, right_clauses} = unify_expansion(clauses, [], [])
    with {:equal, _, type_lvars, type_rvars, acc_rvars} <-
           unify(inter_left, [{:fn, left_clauses, arity}], lvars, rvars, type_lvars, type_rvars, acc_rvars),
         {:equal, _, type_lvars, type_rvars, acc_rvars} <-
           unify(inter_right, [{:fn, right_clauses, arity}], type_lvars, type_rvars, type_lvars, type_rvars, acc_rvars),
         {:ok, type_rvars} <-
           unify_expansion_intersection(clauses, type_rvars) do
      {:equal, right, type_lvars, type_rvars, acc_rvars}
    else
      _ -> :disjoint
    end
  end

  defp unify_each({:fn, clauses, arity}, {:intersection, inter_left, inter_right} = right,
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    {left_clauses, right_clauses} = unify_expansion(clauses, [], [])

    with {:equal, _, type_lvars, type_rvars, acc_rvars} <-
           unify([{:fn, left_clauses, arity}], inter_left, lvars, rvars, type_lvars, type_rvars, acc_rvars),
         {:equal, _, type_lvars, type_rvars, acc_rvars} <-
           unify([{:fn, right_clauses, arity}], inter_right, type_lvars, type_rvars, type_lvars, type_rvars, acc_rvars),
         {:ok, type_lvars} <-
           unify_expansion_intersection(clauses, type_lvars) do
      {:equal, right, type_lvars, type_rvars, acc_rvars}
    else
      _ -> :disjoint
    end
  end

  # intersections can only be compared to arrows (functions).
  defp unify_each({:intersection, _, _}, _,
                  _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars) do
    :disjoint
  end
  defp unify_each(_, {:intersection, _, _},
                  _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars) do
    :disjoint
  end

  defp unify_each({:var, _, key1} = left, {:var, _, key2} = right,
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    case Map.get(lvars, key1, []) do
      [] ->
        {:equal,
         right,
         Map.update(type_lvars, key1, [right], &(&1 ++ [right])),
         type_rvars,
         Map.put(acc_rvars, key2, Map.get(type_rvars, key2, []))}
      _ ->
        with {types, added, removed} <- unify_var(rvars, key2, [left]) do
          {:equal,
           right,
           type_lvars,
           Map.update(type_rvars, key2, types, &((&1 -- removed) |> union(added))),
           Map.update(acc_rvars, key2, types, &((&1 -- removed) |> union(added)))}
        end
    end
  end

  defp unify_each({:var, _, key}, right,
                  lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    with {types, added, removed} <- unify_var(lvars, key, [right]) do
      {:equal,
       right,
       Map.update(type_lvars, key, types, &((&1 -- removed) |> union(added))),
       type_rvars,
       acc_rvars}
    end
  end

  defp unify_each(left, {:var, _, key} = right,
                  _lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    with {types, added, removed} <- unify_var(rvars, key, [left]) do
      {:equal,
       right,
       type_lvars,
       Map.update(type_rvars, key, types, &((&1 -- removed) |> union(added))),
       Map.update(acc_rvars, key, types, &((&1 -- removed) |> union(added)))}
    end
  end

  defp unify_each(type, type, _lvars, _rvars, type_lvars, type_rvars, acc_rvars),
    do: {:equal, type, type_lvars, type_rvars, acc_rvars}

  defp unify_each(:atom, {:value, atom} = right,
                  _lvars, _rvars, type_lvars, type_rvars, acc_rvars) when is_atom(atom),
    do: {:equal, right, type_lvars, type_rvars, acc_rvars}

  defp unify_each({:value, atom} = left, :atom,
                  _lvars, _rvars, type_lvars, type_rvars, acc_rvars) when is_atom(atom),
    do: {:subset, left, type_lvars, type_rvars, acc_rvars}

  defp unify_each({:fn, lefties, arity}, {:fn, righties, arity},
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_fn(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars)
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    with {kind, args, type_lvars, type_rvars, acc_rvars} <-
           unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars) do
      {kind, {:tuple, args, arity}, type_lvars, type_rvars, acc_rvars}
    end
  end

  defp unify_each(_left, _right, _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars),
    do: :disjoint

  defp unify_var(vars, key, types) do
    case Map.get(vars, key, []) do
      [] ->
        {types, types, []}
      existing ->
        case intersection(existing, types) do
          {[], _added, _remove} -> :disjoint
          {types, added, removed} -> {types, added, removed}
        end
    end
  end

  defp unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars, :equal, [])
  end

  defp unify_args([left | lefties], [right | righties],
                  lvars, rvars, type_lvars, type_rvars, acc_rvars, acc_kind, acc_matched) do
    case unify(left, right, lvars, rvars, type_lvars, type_rvars, acc_rvars) do
      {:disjoint, _, _, _, _} ->
        :disjoint
      {kind, matched, type_lvars, type_rvars, acc_rvars} ->
        unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars,
                   unify_kind(kind, acc_kind), [matched | acc_matched])
    end
  end
  defp unify_args([], [], _lvars, _rvars, type_lvars, type_rvars, acc_rvars, kind, acc_matched) do
    {kind, :lists.reverse(acc_matched), type_lvars, type_rvars, acc_rvars}
  end

  defp unify_fn([{left_head, left_body, _} | lefties], righties,
                lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_fn(left_head, left_body, righties, lefties, righties,
             lvars, rvars, type_lvars, type_rvars, acc_rvars, false)
  end
  defp unify_fn([], righties, _lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    {:equal, righties, type_lvars, type_rvars, acc_rvars}
  end

  defp unify_fn(left_head, left_body, [{right_head, right_body, right_free} | clauses],
                lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars, matched?) do
    # TODO: matched
    with {kind, _, temp_lvars, temp_rvars, temp_acc} when kind != :disjoint <-
           unify_args(left_head, right_head, lvars, rvars, type_lvars, type_rvars, acc_rvars),
         right_body =
           bind(right_body, temp_rvars, type_rvars),
         {:equal, _, temp_lvars, temp_rvars, temp_acc} <-
           unify(left_body, right_body, lvars, temp_rvars, temp_lvars, temp_rvars, temp_acc) do
      type_rvars = Map.drop(temp_rvars, right_free)
      acc_rvars = Map.drop(temp_acc, right_free)
      unify_fn(left_head, left_body, clauses, lefties, righties,
               lvars, rvars, temp_lvars, type_rvars, acc_rvars, true)
    else
      _ -> unify_fn(left_head, left_body, clauses, lefties, righties,
                    lvars, rvars, type_lvars, type_rvars, acc_rvars, matched?)
    end
  end
  defp unify_fn(_, _, [], lefties, righties,
                lvars, rvars, type_lvars, type_rvars, acc_rvars, true) do
    unify_fn(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars)
  end
  defp unify_fn(_, _, [], _lefties, _righties,
                _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars, false) do
    :disjoint
  end

  defp unify_expansion([{head, body, free} | clauses], left_acc, right_acc) do
    {left_free, left_bind} = generalize_vars(free, :left)
    {right_free, right_bind} = generalize_vars(free, :right)
    left = {bind_args(head, left_bind), bind(body, left_bind), left_free}
    right = {bind_args(head, right_bind), bind(body, right_bind), right_free}
    unify_expansion(clauses, [left | left_acc], [right | right_acc])
  end
  defp unify_expansion([], left_acc, right_acc) do
    {:lists.reverse(left_acc), :lists.reverse(right_acc)}
  end

  defp unify_expansion_intersection([{_, _, free} | clauses], vars) do
    unify_expansion_intersection(free, clauses, vars)
  end
  defp unify_expansion_intersection([], vars) do
    {:ok, vars}
  end

  defp unify_expansion_intersection([var | free], clauses, vars) do
    {left, vars} = Map.pop(vars, {:left, var})
    {right, vars} = Map.pop(vars, {:right, var})

    cond do
      left && right ->
        case intersection(left, right) do
          {[], _, _} -> :error
          {types, _, _} -> unify_expansion_intersection(free, clauses, Map.put(vars, var, types))
        end
      left ->
        unify_expansion_intersection(free, clauses, Map.put(vars, var, left))
      right ->
        unify_expansion_intersection(free, clauses, Map.put(vars, var, right))
      true ->
        unify_expansion_intersection(free, clauses, vars)
    end
  end
  defp unify_expansion_intersection([], clauses, vars) do
    unify_expansion_intersection(clauses, vars)
  end

  @doc """
  Binds the variables to their types.

  A set of variables to not be replaced can be given, useful
  to guarantee anonymous functions only interpolate variables
  introduced by themselves.
  """
  def bind(types, vars, preserve \\ %{})

  def bind(types, vars, _preserve) when vars == %{} do
    types
  end
  def bind(types, vars, preserve) do
    :lists.reverse(bind_each(types, [], vars, preserve))
  end

  defp bind_each([{:fn, clauses, arity} | types], acc, vars, preserve) do
    clauses =
      for {head, body, free} <- clauses do
        {bind_args(head, vars, preserve), bind(body, vars, preserve), free}
      end
    bind_each(types, [{:fn, clauses, arity} | acc], vars, preserve)
  end
  defp bind_each([{:var, _, key} = type | types], acc, vars, preserve) do
    case Map.get(preserve, key, []) do
      [] ->
        case Map.get(vars, key, []) do
          {:recursive, existing} ->
            # TODO: Convert types to strings when such is supported.
            raise "type checker found undetected recursive definition " <>
                  "when binding #{inspect type} to #{inspect existing}"
          [] ->
            bind_each(types, [type | acc], vars, preserve)
          existing ->
            existing = bind_each(existing, [], Map.put(vars, key, {:recursive, existing}), preserve)
            bind_each(types, union(existing, acc), vars, preserve)
        end
      _ ->
        bind_each(types, [type | acc], vars, preserve)
    end
  end
  defp bind_each([{:tuple, args, arity} | types], acc, vars, preserve) do
    bind_each(types, [{:tuple, bind_args(args, vars, preserve), arity} | acc], vars, preserve)
  end
  defp bind_each([{:intersection, left, right} | types], acc, vars, preserve) do
    left = bind(left, vars, preserve)
    right = bind(right, vars, preserve)
    bind_each(types, [{:intersection, left, right} | acc], vars, preserve)
  end
  defp bind_each([type | types], acc, vars, preserve) do
    bind_each(types, [type | acc], vars, preserve)
  end
  defp bind_each([], acc, _vars, _preserve) do
    acc
  end

  @doc """
  Binds a list of arguments.
  """
  def bind_args(args, vars, preserve \\ %{}) do
    Enum.map(args, &bind(&1, vars, preserve))
  end

  @doc """
  Computes the union of two union types.
  """
  def union(lefties, []), do: lefties
  def union([], righties), do: righties
  def union(lefties, righties), do: union(lefties, righties, [])

  defp union([left | lefties], righties, acc) do
    union(left, righties, lefties, [], acc)
  end
  defp union([], righties, acc) do
    :lists.reverse(acc, righties)
  end

  defp union(left, [right | righties], temp_left, temp_right, acc) do
    case qualify(left, right) do
      :disjoint -> union(left, righties, temp_left, [right | temp_right], acc)
      :subset -> union(temp_left, :lists.reverse(temp_right, [right | righties]), acc)
      _ -> union(temp_left, :lists.reverse(temp_right, righties), [left | acc])
    end
  end
  defp union(left, [], temp_left, temp_right, acc) do
    union(temp_left, :lists.reverse(temp_right), [left | acc])
  end

  @doc """
  Computes the intersection between two union types.

  It returns which items were added and removed from the left side.
  """
  def intersection(lefties, righties) do
    intersection(lefties, righties, [], [], [])
  end

  defp intersection([left | lefties], righties, acc, added, removed) do
    intersection(left, righties, lefties, righties, acc, added, removed)
  end
  defp intersection([], _righties, acc, added, removed) do
    {acc, :lists.reverse(added), removed}
  end

  defp intersection(left, [head | tail], lefties, righties, acc, added, removed) do
    case intersection_type(left, head) do
      {:replace, type} -> intersection(lefties, righties, [type | acc], [type | added], [left | removed])
      :keep -> intersection(lefties, righties, [left | acc], added, removed)
      :none -> intersection(left, tail, lefties, righties, acc, added, removed)
    end
  end
  defp intersection(left, [], lefties, righties, acc, added, removed) do
    intersection(lefties, righties, acc, added, [left | removed])
  end

  defp intersection_type({:tuple, args1, arity}, {:tuple, args2, arity}) do
    case intersection_args(args1, args2, [], :keep) do
      {:replace, args} -> {:replace, {:tuple, args, arity}}
      other -> other
    end
  end
  defp intersection_type(left, right) do
    case qualify(left, right) do
      :disjoint -> :none
      :superset -> {:replace, right}
      _ -> :keep
    end
  end

  defp intersection_args([left | lefties], [right | righties], acc, kind) do
    case intersection(left, right) do
      {[], _, _} ->
        :none
      {intersection, [], []} when kind == :keep ->
        intersection_args(lefties, righties, [intersection | acc], :keep)
      {intersection, _, _} ->
        intersection_args(lefties, righties, [intersection | acc], :replace)
    end
  end
  defp intersection_args([], [], _acc, :keep), do: :keep
  defp intersection_args([], [], acc, :replace), do: {:replace, :lists.reverse(acc)}

  # Qualifies base types.
  # Composite types need to be handled on the parent
  defp qualify(type, type), do: :equal

  defp qualify(:atom, {:value, atom}) when is_atom(atom), do: :superset
  defp qualify({:value, atom}, :atom) when is_atom(atom), do: :subset

  defp qualify({:tuple, args1, arity}, {:tuple, args2, arity}) do
    qualify_args(args1, args2, :equal)
  end

  defp qualify(_, _), do: :disjoint

  defp qualify_args([left | lefties], [right | righties], :equal) do
    case qualify_left_right(:lists.sort(left), :lists.sort(right)) do
      :equal -> qualify_args(lefties, righties, :equal)
      kind -> qualify_args([left | lefties], [right | righties], kind)
    end
  end
  defp qualify_args([left | lefties], [right | righties], :superset) do
    if qualify_superset?(left, right) do
      qualify_args(lefties, righties, :superset)
    else
      :disjoint
    end
  end
  defp qualify_args([left | lefties], [right | righties], :subset) do
    if qualify_superset?(right, left) do
      qualify_args(lefties, righties, :subset)
    else
      :disjoint
    end
  end
  defp qualify_args(_, _, :disjoint) do
    :disjoint
  end
  defp qualify_args([], [], kind) do
    kind
  end

  defp qualify_left_right([left | lefties], [right | righties]) do
    case qualify(left, right) do
      :equal -> qualify_left_right(lefties, righties)
      kind -> kind
    end
  end
  defp qualify_left_right([], []), do: :equal
  defp qualify_left_right([], _), do: :subset
  defp qualify_left_right(_, []), do: :superset

  defp qualify_superset?(lefties, righties) do
    Enum.all?(righties, fn right ->
      Enum.any?(lefties, fn left ->
        qualify(left, right) in [:superset, :equal]
      end)
    end)
  end

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, @state)
  end

  defp of({var, meta, ctx}, %{vars: vars, rewrite: rewrite} = state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, [{:var, _, var_counter}] = types} ->
        case rewrite do
          %{^var_counter => {_, types}} ->
            ok(types, put_in(state.rewrite[var_counter], {true, types}))
          %{} ->
            ok(types, state)
        end
      {:ok, types} ->
        ok(types, state)
      :error ->
        error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, state) do
    with {:ok, clauses, state} <- of_clauses(clauses, state) do
      ok([{:fn, clauses, 1}], state)
    end
  end

  defp of({:__block__, _meta, args}, state) do
    of_block(args, state)
  end

  defp of({:=, meta, [left, right]}, state) do
    with {:ok, right, right_state} <- of(right, state),
         {:ok, left, left_state} <- of_pattern(left, replace_vars(right_state, state)) do
      state = lift_vars(left_state, right_state)
      %{inferred: inferred, vars: vars, match: match} = state

      case of_match(left, right, inferred, vars, match) do
        {:ok, acc_vars, acc_inferred, acc_body} ->
          ok(acc_body, %{state | inferred: acc_inferred, vars: acc_vars})
        :error ->
          error(meta, {:disjoint_match, left, right})
      end
    end
  end

  # TODO: Support multiple args
  # TODO: Support call merging
  defp of({{:., _, [fun]}, meta, args}, state) do
    with {:ok, fun_types, fun_state} <- of(fun, state) do
      state = replace_vars(fun_state, state)
      arity = length(args)
      of_apply(fun_types, arity, meta, args, state, [], fun_state)
    end
  end

  defp of(value, state) do
    literal(value, state, &of/2)
  end

  ## Apply

  defp of_apply([{:fn, clauses, arity} | types], arity, meta, args, state, acc, fun_state) do
    with {:ok, return, state} <- of_fn_apply(clauses, meta, args, state),
         do: of_apply(types, arity, meta, args, state, union(acc, return), fun_state)
  end
  defp of_apply([{:var, var_ctx, var_counter} | types], arity, meta, args, state, acc, fun_state) do
    with {:ok, return, state} <- of_var_apply(var_ctx, var_counter, meta, args, arity, state),
         do: of_apply(types, arity, meta, args, state, union(acc, return), fun_state)
  end
  defp of_apply([fun_type | _], arity, meta, _args, _state, _acc, _fun_state) do
    error(meta, {:invalid_fn, fun_type, arity})
  end
  defp of_apply([], _arity, _meta, _args, state, acc, fun_state) do
    {:ok, acc, lift_vars(state, fun_state)}
  end

  ### Var apply

  defp of_var_apply(var_ctx, var_counter, meta, [arg], arity, state) do
    %{counter: recur_counter, inferred: inferred, rank: rank, rewrite: rewrite} = state
    previous_rewrite = Map.get(rewrite, var_counter)
    recur = [{:var, var_ctx, recur_counter}]

    # Change what the current variable points to. In case we infer a type for
    # it during the arguments, we cannot just take them as is because they may
    # be recursive types. Therefore we use the intersection operator described in
    # "What are principal typings and what are they good for?", Trevor Jim (1996)
    state =
      %{state | counter: recur_counter + 1,
                inferred: Map.put(inferred, recur_counter, []),
                rewrite: Map.put_new(rewrite, var_counter, {false, recur})}

    with {:ok, arg_types, state} <- of(arg, state) do
      %{inferred: inferred, counter: counter, rewrite: rewrite} = state
      recur_types = Map.fetch!(inferred, recur_counter)

      {inferred, intersection} =
        case rewrite do
          %{^var_counter => {true, _}} when recur_types != [] ->
            {inferred, recur_types}
          %{^var_counter => {true, _}} ->
            {inferred, recur}
          %{} ->
            {Map.delete(inferred, recur_counter), nil}
        end

      return = [{:var, {:return, Elixir}, counter}]
      rewrite = if previous_rewrite, do: rewrite, else: Map.delete(rewrite, var_counter)

      types_return_or_error =
        case of_var_apply_unify(var_counter, arg_types, counter, return, arity, inferred, intersection) do
          {:match, types, return} ->
            {types, return}
          {:nomatch, types} ->
            of_var_apply_clauses(types, arity, {[arg_types], return, [counter]})
        end

      cond do
        types_return_or_error == :error ->
          error(meta, {:invalid_fn, [{:var, var_ctx, var_counter}], arity})
        intersection && of_var_apply_invalid_rank?(rank, var_ctx, var_counter) ->
          error(meta, :rank2_restricted)
        true ->
          {types, return} = types_return_or_error

          types =
            if intersection do
              [{:intersection, intersection, types}]
            else
              types
            end

          inferred = Map.put(inferred, var_counter, types)
          ok(return, %{state | inferred: inferred, rewrite: rewrite, counter: counter + 1})
      end
    end
  end

  defp of_var_apply_invalid_rank?(rank, var_ctx, var_counter) do
    Map.get(rank, var_ctx) != [{:var, var_ctx, var_counter}]
  end

  defp of_var_apply_unify(key, arg, counter, return, arity, inferred, intersection) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], arity}]}
      existing when is_nil(intersection) ->
        fun = [{:fn, [{[arg], return, [counter]}], arity}]

        case unify(fun, existing, inferred, inferred) do
          {_, [_ | _] = matched, lvars, _, _} ->
            {:match, matched, bind(return, lvars)}
          _ ->
            {:nomatch, existing}
        end
      existing ->
        {:nomatch, existing}
    end
  end

  defp of_var_apply_clauses(types, arity, clause) do
    of_var_apply_clauses(types, arity, clause, [])
  end

  defp of_var_apply_clauses([type | types], arity, clause, acc) do
    case of_var_apply_each_clause(type, arity, clause) do
      {:ok, type} -> of_var_apply_clauses(types, arity, clause, [type | acc])
      :error -> of_var_apply_clauses(types, arity, clause, acc)
    end
  end
  defp of_var_apply_clauses([], _arity, _clause, []) do
    :error
  end
  defp of_var_apply_clauses([], _arity, {_, return, _}, acc) do
    {:lists.reverse(acc), return}
  end

  defp of_var_apply_each_clause({:fn, clauses, arity}, arity, clause) do
    {:ok, {:fn, [clause | clauses], arity}}
  end
  defp of_var_apply_each_clause({:intersection, left, right}, arity, clause) do
    case {of_var_apply_clauses(left, arity, clause), of_var_apply_clauses(right, arity, clause)} do
      {{left, _}, {right, _}} -> {:ok, {:intersection, left, right}}
      {:error, {right, _}} -> {:ok, {:intersection, left, right}}
      {{left, _}, :error} -> {:ok, {:intersection, left, right}}
      {:error, :error} -> :error
    end
  end
  defp of_var_apply_each_clause(_, _arity, _clause) do
    :error
  end

  ### Fn Apply

  defp of_fn_apply(clauses, meta, [arg], state) do
    with {:ok, arg_types, state} <- of(arg, state) do
      %{inferred: inferred} = state

      case of_fn_apply_each(clauses, arg_types, inferred, arg_types, inferred, []) do
        {:ok, acc_inferred, acc_body} ->
          ok(acc_body, %{state | inferred: acc_inferred})
        {:error, pending} ->
          error(meta, {:disjoint_apply, pending, clauses, arg_types})
      end
    end
  end

  # If we have matched all arguments and we haven't inferred anything new,
  # it means they are literals and there is no need for an exhaustive search.
  defp of_fn_apply_each(_clauses, _arg, inferred, [], inferred, acc_body) do
    {:ok, inferred, acc_body}
  end
  defp of_fn_apply_each([{head, body, free} | clauses], arg, inferred, acc_arg, acc_inferred, acc_body) do
    {_, bind} = generalize_vars(free, :let)
    [head] = bind_args(head, bind)
    body = bind(body, bind)

    with {_, [_ | _] = matched, lvars, _, rvars} <- unify(head, arg, inferred, acc_inferred) do
      acc_body = union(acc_body, bind(body, lvars))
      of_fn_apply_each(clauses, arg, inferred, acc_arg -- matched, rvars, acc_body)
    else
      _ -> of_fn_apply_each(clauses, arg, inferred, acc_arg, acc_inferred, acc_body)
    end
  end
  defp of_fn_apply_each([], _arg, _inferred, [], acc_inferred, acc_body) do
    {:ok, acc_inferred, acc_body}
  end
  defp of_fn_apply_each([], _arg, _inferred, pending, _acc_inferred, _acc_body) do
    {:error, pending}
  end

  ## Matching

  # All of the possible types returned on the right side
  # must be matched on the left side. We must also unify
  # values on the right side with expressions on the left.
  # For example, the type:
  #
  #     fn z ->
  #       {:ok, x} = (fn y -> {y, :error} end).(z)
  #       {z, x}
  #     end
  #
  # Should infer that:
  #
  #     x is :error
  #     y is :ok
  #     z is :ok
  #
  # And the function must return {:ok, :error}.
  defp of_match(left, right, inferred, vars, match) do
    with {:equal, _, lvars, _, rvars} <- unify(left, right, inferred, inferred) do
      {lvars, rvars} = of_match_vars(Map.to_list(match), lvars, vars, rvars)
      {:ok, lvars, rvars, bind(right, rvars)}
    else
      _ -> :error
    end
  end

  defp of_match_vars([{var_ctx, [{_, _, counter}] = types} | matches], lvars, vars, inferred) do
    of_match_vars(matches, lvars,
                  Map.put(vars, var_ctx, bind(types, lvars)),
                  Map.delete(inferred, counter))
  end
  defp of_match_vars([], _lvars, vars, inferred) do
    {vars, inferred}
  end

  ## Clauses

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  defp of_clauses(clauses, state) do
    of_clauses(clauses, state, [], state)
  end

  defp of_clauses([{:->, _, [[arg], body]} | clauses],
                   %{inferred: preserve, rank: rank} = state, acc_clauses, acc_state) do
    with {:ok, head, %{match: match, vars: vars} = acc_state} <- of_pattern(arg, acc_state),
         acc_state = %{acc_state | vars: Map.merge(match, vars), rank: rank || match},
         {:ok, body, %{inferred: inferred} = acc_state} <- of(body, acc_state) do
      head = bind_args([head], inferred, preserve)
      body = bind(body, inferred, preserve)
      free_variables = free_variables(preserve, inferred)
      inferred = Map.drop(inferred, free_variables)
      acc_state = replace_vars(%{acc_state | inferred: inferred, rank: rank}, state)
      of_clauses(clauses, state, [{head, body, free_variables} | acc_clauses], acc_state)
    end
  end
  defp of_clauses([], _state, acc_clauses, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_state}
  end

  defp free_variables(preserve, inferred) do
    inferred = Enum.reduce(preserve, inferred, fn {k, _}, acc -> Map.delete(acc, k) end)
    for {k, []} <- inferred, do: k
  end

  ## Blocks

  defp of_block([arg], state) do
    of(arg, state)
  end
  defp of_block([arg | args], state) do
    case of(arg, state) do
      {:ok, _, state} -> of_block(args, state)
      {:error, _, _} = error -> error
    end
  end

  ## Patterns

  defp of_pattern(ast, state) do
    of_pattern_each(ast, %{state | match: %{}})
  end

  defp of_pattern_each({:::, meta, [{var, _, ctx}, type_ast]}, state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    with {:ok, type, state} <- ast_to_types(type_ast, state) do
      of_pattern_bound_var(meta, {var, ctx}, type, state)
    end
  end
  defp of_pattern_each({var, meta, ctx}, state) when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    of_pattern_var(meta, {var, ctx}, state)
  end
  defp of_pattern_each({:::, meta, [_, _]} = ann, _vars) do
    error(meta, {:invalid_annotation, ann})
  end
  defp of_pattern_each(other, vars) do
    literal(other, vars, &of_pattern_each/2)
  end

  defp of_pattern_var(_meta, var_ctx, %{match: match, counter: counter, inferred: inferred} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, type} ->
        ok(type, state)
      :error ->
        types = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, types)
        inferred = Map.put(inferred, counter, [])
        ok(types, %{state | match: match, counter: counter + 1, inferred: inferred})
    end
  end

  defp of_pattern_bound_var(meta, var_ctx, type, %{match: match} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, ^type} ->
        ok(type, state)
      {:ok, other} ->
        error(meta, {:bound_var, var_ctx, other, type})
      :error ->
        match = Map.put(match, var_ctx, type)
        ok(type, %{state | match: match})
    end
  end

  ## Helpers

  defp literal(value, state, _fun) when is_integer(value) do
    ok([:integer], state)
  end

  defp literal(value, state, _fun) when is_atom(value) do
    ok([{:value, value}], state)
  end
  defp literal({left, right}, state, fun) do
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      ok([{:tuple, args, arity}], state)
    end
  end
  defp literal({:{}, _, args}, state, fun) do
    with {:ok, args, arity, state} <- args(args, state, fun) do
      ok([{:tuple, args, arity}], state)
    end
  end
  defp literal(other, _state, _fun) do
    error([], {:unknown_pattern, other})
  end

  defp args(args, state, fun) do
    args(args, [], 0, state, state, fun)
  end

  defp args([arg | args], acc_args, acc_count, acc_state, state, fun) do
    case fun.(arg, replace_vars(acc_state, state)) do
      {:ok, arg, arg_state} ->
        args(args, [arg | acc_args], acc_count + 1, lift_vars(arg_state, acc_state), state, fun)
      {:error, _, _} = error ->
        error
    end
  end
  defp args([], acc_args, acc_count, acc_state, _state, _fun) do
    {:ok, :lists.reverse(acc_args), acc_count, acc_state}
  end

  # This is generalization used by intersection and let-polymorhism.
  # It works by going through all free variables in a function and
  # giving them a new binding.
  defp generalize_vars(free, kind) do
    generalize_vars(free, kind, [], %{})
  end

  defp generalize_vars([name | names], kind, vars, bind) do
    kinded = {kind, name}
    bind = Map.put(bind, name, [{:var, {:gen, Elixir}, kinded}])
    generalize_vars(names, kind, [kinded | vars], bind)
  end
  defp generalize_vars([], _kind, vars, bind) do
    {:lists.reverse(vars), bind}
  end

  @compile {:inline, ok: 2, error: 2}

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
