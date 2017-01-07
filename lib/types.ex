defmodule Types do
  @moduledoc """
  Type inference and checking for Elixir.
  """

  alias Inspect.Algebra, as: A

  @doc """
  Convert the types AST to an algebra document.
  """
  def types_to_algebra(types) do
    types_to_algebra(types, %{counter: 0, vars: %{}, rewrite: %{}}) |> elem(0)
  end

  defp types_to_algebra(types, state) do
    {types, state} = Enum.map_reduce(types, state, &type_to_algebra/2)
    {A.group(A.fold_doc(types, &A.glue(A.concat(&1, " |"), &2))), state}
  end

  # {:value, val}
  # {:fn, [clauses], arity}
  # {:tuple, args, arity}
  # {:var, var_ctx, var_key}
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
  defp type_to_algebra({:var, _, var_counter} = var,
                       %{vars: vars, counter: counter, rewrite: rewrite} = state) do
    [{:var, _, var_counter}] = Map.get(rewrite, var_counter, [var])
    case vars do
      %{^var_counter => letter} ->
        {letter, state}
      %{} ->
        letter = counter_to_letter(counter)
        vars = Map.put(vars, var_counter, letter)
        {letter, %{state | vars: vars, counter: counter + 1}}
    end
  end

  defp type_to_algebra(:atom, state), do: {"atom()", state}
  defp type_to_algebra(:integer, state), do: {"integer()", state}

  defp args_to_algebra(args, state) do
    {args, state} = Enum.map_reduce(args, state, &types_to_algebra/2)
    {A.fold_doc(args, &A.glue(A.concat(&1, ","), &2)), state}
  end

  defp clauses_to_algebra(clauses, %{rewrite: rewrite} = state) do
    {clauses, state} =
      Enum.map_reduce(clauses, state, fn {head, body, fun_rewrite, _}, state ->
        state = %{state | rewrite: Map.merge(rewrite, fun_rewrite)}
        {head, state} = args_to_algebra(head, state)
        {body, state} = types_to_algebra(body, state)
        {A.nest(A.glue(A.concat(head, " ->"), body), 2), %{state | rewrite: rewrite}}
      end)
    {A.fold_doc(clauses, &A.glue(A.concat(&1, ";"), &2)), state}
  end

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
  @state %{vars: %{}, match: %{}, inferred: %{}, counter: 0}

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

    * rewrite - variables to be rewritten during unification.
    * vars - variables already inferred.
    * type_vars - variables inferred for each type on the right. Starts as vars.
    * acc_vars - variables inferred for from the caller loop.

  Any variable found during unification must intersect with
  whatever variable found on the proper `*vars`. For example,
  if a variable is found on the right side, it must intersect
  with any inferred value in `vars`.

  Unification works by pinning each specific type on the `right`
  and finding a `left` type that matches. If such type exists
  and variables are involved, `type_*vars` will be properly
  updated and be set as the main `*vars` once we move to the
  next type.

  `acc_vars` is only updated by this function, never read.
  `acc_vars` keeps inference information across the caller
  loop. For example, if we are unifying against multiple clauses,
  `acc_vars` will keep unifying information for all clauses.
  """
  # TODO: Include error reason every time unification fails.
  def unify(left, right, rewrite, vars, acc_vars) do
    unify(left, right, rewrite, vars, vars, acc_vars)
  end

  defp unify(left, right, rewrite, vars, temp_vars, acc_vars) do
    unify(left, right, rewrite, vars, temp_vars, acc_vars, :match, [])
  end

  defp unify([left | lefties], righties, rewrite, vars, type_vars, acc_vars, kind, matched) do
    unify(left, righties, rewrite, vars, type_vars, acc_vars, lefties, kind, matched, [])
  end
  defp unify([], _righties, _rewrite, _vars, type_vars, acc_vars, kind, matched) do
    {kind, matched, type_vars, acc_vars}
  end

  defp unify(left, [right | righties], rewrite, vars, type_vars,
             acc_vars, lefties, kind, matched, unmatched) do
    case unify_each(left, right, rewrite, vars, type_vars, acc_vars) do
      {:match, _equal, type_vars, acc_vars} ->
        unify(left, righties, rewrite, vars, type_vars,
              acc_vars, lefties, kind, [right | matched], unmatched)
      {:subset, subset, type_vars, acc_vars} ->
        unify(left, righties, rewrite, vars, type_vars,
              acc_vars, lefties, unify_min(:subset, kind), [subset | matched], [right | unmatched])
      :disjoint ->
        unify(left, righties, rewrite, vars, type_vars,
              acc_vars, lefties, :disjoint, matched, [right | unmatched])
    end
  end
  defp unify(_left, [], rewrite, _vars, type_vars, acc_vars, lefties, kind, matched, righties) do
    unify(lefties, righties, rewrite, type_vars, type_vars, acc_vars, kind, matched)
  end

  defp unify_min(:disjoint, _), do: :disjoint
  defp unify_min(_, :disjoint), do: :disjoint
  defp unify_min(:subset, _), do: :subset
  defp unify_min(_, :subset), do: :subset
  defp unify_min(_, _), do: :match

  defp unify_each({:var, _, key1} = left, {:var, _, key2} = right,
                  rewrite, vars, type_vars, acc_vars) do
    [{:var, _, key1}] = Map.get(rewrite, key1, [left])
    [{:var, _, key2}] = Map.get(rewrite, key2, [right])

    case {Map.get(vars, key1, []), Map.get(vars, key2, [])} do
      {[], _} ->
        acc_vars = Map.put(acc_vars, key2, Map.get(type_vars, key2, []))
        {:match,
         right,
         Map.update(type_vars, key1, [right], &union(&1, [right])),
         Map.update(acc_vars, key1, [right], &union(&1, [right]))}
      {_, []} ->
        acc_vars = Map.put(acc_vars, key1, Map.get(type_vars, key1, []))
        {:match,
         right,
         Map.update(type_vars, key2, [left], &union(&1, [left])),
         Map.update(acc_vars, key2, [left], &union(&1, [left]))}
      {left_value, right_value} ->
        with {_, [_ | _] = match, type_vars, acc_vars} <-
               unify(left_value, right_value, rewrite, vars, type_vars, acc_vars) do
          {:match,
           right,
           Map.update(type_vars, key2, match, &union(&1 -- right_value, match)),
           Map.update(acc_vars, key2, match, &union(&1 -- right_value, match))}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_each({:var, _, key} = left, right, rewrite, vars, type_vars, acc_vars) do
    unify_var(key, left, right, rewrite, vars, type_vars, acc_vars)
  end

  defp unify_each(left, {:var, _, key} = right, rewrite, vars, type_vars, acc_vars) do
    unify_var(key, right, left, rewrite, vars, type_vars, acc_vars)
  end

  defp unify_each({:fn, lefties, arity}, {:fn, righties, arity},
                  rewrite, vars, type_vars, acc_vars) do
    unify_fn(lefties, righties, rewrite, vars, type_vars, acc_vars)
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  rewrite, vars, type_vars, acc_vars) do
    with {kind, args, type_vars, acc_vars} <-
           unify_args(lefties, righties, rewrite, vars, type_vars, acc_vars) do
      {kind, {:tuple, args, arity}, type_vars, acc_vars}
    end
  end

  defp unify_each(left, right, _rewrite, _vars, type_vars, acc_vars) do
    case qualify(left, right, %{}) do
      {:equal, _} -> {:match, right, type_vars, acc_vars}
      {:superset, _} -> {:match, right, type_vars, acc_vars}
      {:subset, _} -> {:subset, left, type_vars, acc_vars}
      {:disjoint, _} -> :disjoint
    end
  end

  defp unify_args(lefties, righties, rewrite, vars, type_vars, acc_vars) do
    unify_args(lefties, righties, rewrite, vars, type_vars, acc_vars, :match, [])
  end

  defp unify_args([left | lefties], [right | righties],
                  rewrite, vars, type_vars, acc_vars, acc_kind, acc_matched) do
    case unify(left, right, rewrite, vars, type_vars, acc_vars) do
      {:disjoint, _, _, _} ->
        :disjoint
      {kind, matched, type_vars, acc_vars} ->
        unify_args(lefties, righties, rewrite, vars, type_vars, acc_vars,
                   unify_min(kind, acc_kind), [matched | acc_matched])
    end
  end
  defp unify_args([], [], _rewrite, _vars, type_vars, acc_vars, kind, acc_matched) do
    {kind, :lists.reverse(acc_matched), type_vars, acc_vars}
  end

  defp unify_var(key, var, type, rewrite, vars, type_vars, acc_vars) do
    [{:var, _, key}] = Map.get(rewrite, key, [var])

    case Map.get(vars, key, []) do
      [] ->
        {:match,
         type,
         Map.update(type_vars, key, [type], &union(&1, [type])),
         Map.update(acc_vars, key, [type], &union(&1, [type]))}
      value ->
        with {_, [_ | _] = match, type_vars, acc_vars} <-
               unify(value, [type], rewrite, vars, type_vars, acc_vars) do
          {:match,
           type,
           Map.update(type_vars, key, match, &union(&1 -- value, match)),
           Map.update(acc_vars, key, match, &union(&1 -- value, match))}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_fn([{left_head, left_body, _, _} | lefties], righties,
                rewrite, vars, type_vars, acc_vars) do
    # FREE: left_free
    unify_fn(left_head, left_body, righties, lefties, righties,
             rewrite, vars, type_vars, acc_vars, false)
  end
  defp unify_fn([], righties, _rewrite, _vars, type_vars, acc_vars) do
    {:match, righties, type_vars, acc_vars}
  end

  defp unify_fn(left_head, left_body, [{right_head, right_body, _, right_inferred} | clauses],
                lefties, righties, rewrite, vars, type_vars, acc_vars, matched?) do
    # FREE: right_free
    with {kind, _, temp_vars, temp_acc} when kind != :disjoint <-
           unify_args(left_head, right_head, rewrite, vars, type_vars, acc_vars),
         right_body =
           bind(right_body, temp_vars, type_vars),
         {:match, _, temp_vars, temp_acc} <-
           unify(left_body, right_body, rewrite, temp_vars, temp_vars, temp_acc) do
      type_vars = Map.drop(temp_vars, Map.keys(right_inferred))
      acc_vars = Map.drop(temp_acc, Map.keys(right_inferred))
      unify_fn(left_head, left_body, clauses, lefties, righties,
               rewrite, vars, type_vars, acc_vars, true)
    else
      _ -> unify_fn(left_head, left_body, clauses, lefties, righties,
                    rewrite, vars, type_vars, acc_vars, matched?)
    end
  end
  defp unify_fn(_, _, [], lefties, righties, rewrite, _vars, type_vars, acc_vars, true) do
    unify_fn(lefties, righties, rewrite, type_vars, type_vars, acc_vars)
  end
  defp unify_fn(_, _, [], _lefties, _righties, _rewrite, _vars, _type_vars, _acc_vars, false) do
    :disjoint
  end

  @doc """
  Binds the variables to their types.

  A set of variables to not be replaced can be given, useful
  to guarantee anonymous functions only interpolate variables
  introduced by themselves.
  """
  def bind(types, vars, preserve \\ %{}) do
    :lists.reverse(bind_each(types, [], vars, preserve))
  end

  defp bind_each([{:fn, clauses, arity} | types], acc, vars, preserve) do
    clauses =
      for {head, body, rewrite, inferred} <- clauses do
        vars = Map.merge(vars, inferred)
        {bind_args(head, vars, preserve), bind(body, vars, preserve), rewrite, inferred}
      end
    bind_each(types, [{:fn, clauses, arity} | acc], vars, preserve)
  end
  defp bind_each([{:var, _, key} = type | types], acc, vars, preserve) do
    case Map.get(preserve, key, []) do
      [] ->
        case Map.get(vars, key, []) do
          {:recursive, existing} ->
            raise "type checker found undetected recursive definition " <>
                  "when binding #{inspect type} to #{inspect existing}"
          [] ->
            bind_each(types, [type | acc], vars, preserve)
          existing ->
            # TODO: union only works with bind if variables are guaranteed
            # to stay at the end, so we need to support such on unify.
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
  defp bind_each([type | types], acc, vars, preserve) do
    bind_each(types, [type | acc], vars, preserve)
  end
  defp bind_each([], acc, _vars, _preserve) do
    acc
  end

  defp bind_args(args, vars, preserve) do
    Enum.map(args, &bind(&1, vars, preserve))
  end

  @doc """
  Traverses types in a postwalk fashion with the given state and function.
  """
  def traverse(types, state, fun) do
    traverse(types, [], state, fun)
  end

  defp traverse([{:fn, clauses, arity} | types], acc, state, fun) do
    {clauses, state} =
      Enum.map_reduce(clauses, state, fn {head, body, rewrite, inferred}, state ->
        {head, state} = traverse_args(head, state, fun)
        {body, state} = traverse(body, state, fun)
        {{head, body, rewrite, inferred}, state}
      end)
    traverse_apply({:fn, clauses, arity}, types, acc, state, fun)
  end
  defp traverse([{:tuple, args, arity} | types], acc, state, fun) do
    {args, state} = traverse_args(args, state, fun)
    traverse_apply({:tuple, args, arity}, types, acc, state, fun)
  end
  defp traverse([type | types], acc, state, fun) do
    traverse_apply(type, types, acc, state, fun)
  end
  defp traverse([], acc, state, _fun) do
    {:lists.reverse(acc), state}
  end

  defp traverse_apply(type, types, acc, state, fun) do
    case fun.(type, state) do
      {:ok, type, state} -> traverse(types, [type | acc], state, fun)
      {:union, extra, state} -> traverse(types, union(extra, acc), state, fun)
    end
  end

  defp traverse_args(args, state, fun) do
    Enum.map_reduce(args, state, &traverse(&1, [], &2, fun))
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
    case qualify(left, right, %{}) do
      {:disjoint, _} -> union(left, righties, temp_left, [right | temp_right], acc)
      {:subset, _} -> union(temp_left, :lists.reverse(temp_right, [right | righties]), acc)
      {_, _} -> union(temp_left, :lists.reverse(temp_right, righties), [left | acc])
    end
  end
  defp union(left, [], temp_left, temp_right, acc) do
    union(temp_left, :lists.reverse(temp_right), [left | acc])
  end

  # Qualifies base types.
  defp qualify(type, type, vars), do: {:equal, vars}

  defp qualify({:var, _, left_counter}, {:var, _, right_counter}, vars) do
    left_key = {:left, left_counter}
    right_key = {:right, right_counter}
    case vars do
      %{^left_key => right_value, ^right_key => left_value} ->
        left_value = left_value || left_counter
        right_value = right_value || right_counter
        vars = %{vars | left_key => right_value, right_key => left_value}
        if left_value == left_counter and right_value == right_counter do
          {:equal, vars}
        else
          {:disjoint, vars}
        end
      %{} ->
        {:disjoint, vars}
    end
  end

  defp qualify({:fn, left, arity}, {:fn, right, arity}, vars) do
    qualify_fn(left, right, vars, :equal)
  end

  defp qualify(:atom, {:value, atom}, vars) when is_atom(atom), do: {:superset, vars}
  defp qualify({:value, atom}, :atom, vars) when is_atom(atom), do: {:subset, vars}

  defp qualify({:tuple, args1, arity}, {:tuple, args2, arity}, vars) do
    qualify_args(args1, args2, vars, :equal)
  end

  defp qualify(_, _, vars), do: {:disjoint, vars}

  defp qualify_args([left | lefties], [right | righties], vars, :equal) do
    case qualify_look_ahead(:lists.sort(left), :lists.sort(right), vars) do
      {:equal, vars} -> qualify_args(lefties, righties, vars, :equal)
      {kind, vars} -> qualify_args([left | lefties], [right | righties], vars, kind)
    end
  end
  defp qualify_args([left | lefties], [right | righties], vars, :superset) do
    if vars = qualify_set(left, right, vars, :superset) do
      qualify_args(lefties, righties, vars, :superset)
    else
      {:disjoint, vars}
    end
  end
  defp qualify_args([left | lefties], [right | righties], vars, :subset) do
    if vars = qualify_set(left, right, vars, :subset) do
      qualify_args(lefties, righties, vars, :subset)
    else
      {:disjoint, vars}
    end
  end
  defp qualify_args(_, _, vars, :disjoint) do
    {:disjoint, vars}
  end
  defp qualify_args([], [], vars, kind) do
    {kind, vars}
  end

  defp qualify_look_ahead([left | lefties], [right | righties], vars) do
    case qualify(left, right, vars) do
      {:equal, vars} -> qualify_look_ahead(lefties, righties, vars)
      {kind, vars} -> {kind, vars}
    end
  end
  defp qualify_look_ahead([], [], vars), do: {:equal, vars}
  defp qualify_look_ahead([], _, vars), do: {:subset, vars}
  defp qualify_look_ahead(_, [], vars), do: {:superset, vars}

  defp qualify_set(lefties, [right | righties], vars, kind) do
    qualify_set(lefties, right, lefties, righties, vars, kind)
  end
  defp qualify_set(_lefties, [], vars, _kind) do
    vars
  end

  defp qualify_set([type | types], right, lefties, righties, vars, kind) do
    case qualify(type, right, vars) do
      {^kind, vars} -> qualify_set(lefties, righties, vars, kind)
      {:equal, vars} -> qualify_set(lefties, righties, vars, kind)
      {_, _} -> qualify_set(types, right, lefties, righties, vars, kind)
    end
  end
  defp qualify_set([], _right, _lefties, _righties, _vars, _kind) do
    nil
  end

  defp qualify_fn([{left_head, left_body, _, left_inferred} | lefties], righties, vars, kind) do
    # FREE: left_free
    left_vars = Enum.reduce(Map.keys(left_inferred), vars, &Map.put(&2, {:left, &1}, nil))

    # FREE: right_free
    row =
      for {right_head, right_body, _, right_inferred} <- righties do
        vars = Enum.reduce(Map.keys(right_inferred), left_vars, &Map.put(&2, {:right, &1}, nil))
        qualify_args([left_body | left_head], [right_body | right_head], vars, :equal) |> elem(0)
      end

    case qualify_fn(row, kind, false) do
      :disjoint -> {:disjoint, vars}
      kind -> qualify_fn(lefties, righties, vars, kind)
    end
  end
  defp qualify_fn([], _righties, vars, kind) do
    {kind, vars}
  end

  defp qualify_fn([:disjoint | row], kind, matched?), do: qualify_fn(row, kind, matched?)
  defp qualify_fn([kind | row], :equal, _matched?), do: qualify_fn(row, kind, true)
  defp qualify_fn([kind | row], kind, _matched?), do: qualify_fn(row, kind, true)
  defp qualify_fn([_ | _], _, _matched?), do: :disjoint
  defp qualify_fn([], _kind, false), do: :disjoint
  defp qualify_fn([], kind, true), do: kind

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, @state)
  end

  defp of({var, meta, ctx}, %{vars: vars, counter: counter} = state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, types} ->
        {types, {vars, counter}} = traverse(types, {vars, counter}, &of_var/2)
        ok(types, %{state | vars: vars, counter: counter})
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
    with {:ok, fun, fun_state} <- of(fun, state),
         {:ok, args, arity, state} <- args(args, replace_vars(fun_state, state), &of/2) do
      of_apply(fun, arity, meta, args, state, [], fun_state)
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

  defp of_var_apply(var_ctx, var_counter, meta, [arg_types], arity, state) do
    %{inferred: inferred, counter: counter} = state
    return = [{:var, var_ctx, counter}]

    if of_var_apply_has_counter?([arg_types], var_counter) do
      error(meta, {:recursive_fn, [{:var, var_ctx, var_counter}], arg_types, arity})
    else
      case of_var_apply_unify(var_counter, [arg_types], arity, inferred) do
        {:match, types, return} ->
          inferred =
            inferred
            |> Map.put(counter, [])
            |> Map.put(var_counter, types)
          ok(return, %{state | inferred: inferred})
        {:nomatch, []} ->
          :error
        {:nomatch, types} ->
          types =
            for {:fn, clauses, arity} <- types do
              {:fn, of_var_apply_clauses(clauses, [arg_types], return), arity}
            end

          inferred =
            inferred
            |> Map.put(counter, [])
            |> Map.put(var_counter, types)

          ok(return, %{state | inferred: inferred, counter: counter + 1})
      end
    end
  end

  defp of_var_apply_has_counter?(types, var_counter) do
    traverse_args(types, false, fn
      {:var, _, ^var_counter} = type, false -> {:ok, type, true}
      type, found? -> {:ok, type, found?}
    end) |> elem(1)
  end

  defp of_var_apply_unify(key, args, arity, inferred) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], arity}]}
      existing ->
        funs = for {:fn, _, ^arity} = fun <- existing, do: fun

        return =
          Enum.reduce(funs, [], fn {:fn, clauses, _}, sum ->
            Enum.reduce(clauses, sum, fn
              {^args, return, _, _}, sum -> union(sum, return)
              {_, _, _, _}, sum -> sum
            end)
          end)

        case return do
          [] -> {:nomatch, funs}
          _ -> {:match, funs, return}
        end
    end
  end

  defp of_var_apply_clauses(clauses, args, return) do
    {pre, pos} =
      Enum.split_while(clauses, fn {head, _, _, _} ->
        qualify_args(head, args, %{}, :equal) |> elem(0) != :superset
      end)
    pre ++ [{args, return, %{}, %{}} | pos]
  end

  ### Fn Apply

  defp of_fn_apply(clauses, meta, [arg_types], state) do
    %{inferred: inferred} = state

    case of_fn_apply_each(clauses, arg_types, inferred, arg_types, inferred, []) do
      {:ok, acc_inferred, acc_body} ->
        ok(acc_body, %{state | inferred: acc_inferred})
      {:error, pending} ->
        error(meta, {:disjoint_apply, pending, clauses, arg_types})
    end
  end

  # If we have matched all arguments and we haven't inferred anything new,
  # it means they are literals and there is no need for an exhaustive search.
  defp of_fn_apply_each(_clauses, _arg, inferred, [], inferred, acc_body) do
    {:ok, inferred, acc_body}
  end
  defp of_fn_apply_each([{[head], body, rewrite, vars} | clauses],
                        arg, inferred, acc_arg, acc_inferred, acc_body) do
    with {_, [_ | _] = matched, _, acc_inferred} <-
           unify(head, arg, rewrite, Map.merge(inferred, vars), Map.merge(acc_inferred, vars)) do
      acc_body = union(acc_body, bind(body, rewrite, %{}))
      of_fn_apply_each(clauses, arg, inferred, acc_arg -- matched, acc_inferred, acc_body)
    else
      _ ->
        of_fn_apply_each(clauses, arg, inferred, acc_arg, acc_inferred, acc_body)
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
    with {:match, _, _, match_inferred} <- unify(left, right, %{}, inferred, inferred) do
      {vars, inferred} = of_match_vars(Map.to_list(match), vars, match_inferred)
      {:ok, vars, inferred, right}
    else
      _ -> :error
    end
  end

  defp of_match_vars([{var_ctx, [{_, _, counter}]} | matches], vars, inferred) do
    of_match_vars(matches,
                  Map.put(vars, var_ctx, Map.fetch!(inferred, counter)),
                  Map.delete(inferred, counter))
  end
  defp of_match_vars([], vars, inferred) do
    {vars, inferred}
  end

  ## Clauses

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  defp of_clauses(clauses, state) do
    of_clauses(clauses, state, [], state)
  end

  defp of_clauses([{:->, _, [[arg], body]} | clauses],
                   %{inferred: preserve} = state, acc_clauses, acc_state) do
    with {:ok, head, %{match: match, vars: vars} = acc_state} <- of_pattern(arg, acc_state),
         acc_state = %{acc_state | vars: Map.merge(match, vars)},
         {:ok, body, %{inferred: inferred} = acc_state} <- of(body, acc_state) do
      acc_state = replace_vars(acc_state, state)
      {inferred, clause_inferred} = Map.split(inferred, Map.keys(preserve))
      acc_state = %{acc_state | inferred: inferred}
      of_clauses(clauses, state, [{[head], body, %{}, clause_inferred} | acc_clauses], acc_state)
    end
  end
  defp of_clauses([], _state, acc_clauses, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_state}
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

  ## Vars

  defp of_var({:fn, clauses, arity}, {vars, counter}) do
    {clauses, counter} =
      Enum.map_reduce(clauses, counter, fn {head, body, _, inferred}, counter ->
        # FREE: free
        rewrite = generalize_vars(Map.keys(inferred), counter, %{})
        {{head, body, rewrite, inferred}, counter + 1}
      end)
    {:ok, {:fn, clauses, arity}, {vars, counter}}
  end
  defp of_var(type, acc) do
    {:ok, type, acc}
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

  defp of_pattern_var(_meta, var_ctx, state) do
    %{match: match, counter: counter, inferred: inferred} = state

    case Map.fetch(match, var_ctx) do
      {:ok, type} ->
        ok(type, state)
      :error ->
        inferred = Map.put(inferred, counter, [])
        return = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, return)
        ok(return, %{state | match: match, counter: counter + 1, inferred: inferred})
    end
  end

  defp of_pattern_bound_var(meta, var_ctx, types, state) do
    %{match: match, counter: counter, inferred: inferred} = state
    case Map.fetch(match, var_ctx) do
      {:ok, ^types} ->
        ok(types, state)
      {:ok, other} ->
        error(meta, {:bound_var, var_ctx, other, types})
      :error ->
        inferred = Map.put(inferred, counter, types)
        return = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, return)
        ok(return, %{state | match: match, counter: counter + 1, inferred: inferred})
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

  # FREE: free
  defp generalize_vars([name | names], kind, bind) do
    bind = Map.put(bind, name, [{:var, {:gen, Elixir}, {kind, name}}])
    generalize_vars(names, kind, bind)
  end
  defp generalize_vars([], _kind, bind) do
    bind
  end

  @compile {:inline, ok: 2, error: 2}

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
