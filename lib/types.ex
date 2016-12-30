defmodule Types do
  @moduledoc """
  A type checker for Elixir.

  The type system builds on top of Elixir patterns and
  values to describe types.

  The type system exists around two constructs:

    1. Patterns are non-recursive types that may be used by
       both typed and untyped code

    2. Types may be recursive and used exclusively by typed code

  We will look into those constructs below.

  ## Patterns

  Patterns are non-recursive types made of values and other
  patterns. For example, the built-in boolean pattern may be
  defined as follows:

      pattern boolean() :: true | false

  A pattern can be used as types on typed code:

      deftyped Strict do
        def strict_or(boolean(), boolean()) :: boolean()
        def strict_or(true, true), do: true
        def strict_or(true, false), do: true
        def strict_or(false, true), do: true
        def strict_or(false, false), do: false
      end

  As well as patterns on non-typed code:

      defmodule App do
        def value_accepted?(accept :: boolean()) do
          # ...
        end
      end

  ## Types

  Types are constructs build on top of values, patterns or other
  types which may be recursive. Since types are recursive, they can
  only be effectively checked statically. For example, the built-in
  type `list(a)` is defined recursively as:

      type list(a) :: empty_list() | cons(a, list(a))

  """

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

  @doc """
  Converts the given Type AST to its inner type.
  """
  def ast_to_type(ast, state \\ @state)

  def ast_to_type({:boolean, _, []}, state) do
    ok([{:value, true}, {:value, false}], state)
  end
  def ast_to_type({:integer, _, []}, state) do
    ok([:integer], state)
  end
  def ast_to_type({:atom, _, []}, state) do
    ok([:atom], state)
  end
  def ast_to_type(other, state) do
    literal(other, state, &ast_to_type/2)
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
    unify(left, right, %{}, rvars, %{}, rvars, acc_rvars, [])
  end

  defp unify([left | lefties], righties, lvars, rvars,
             type_lvars, type_rvars, acc_rvars, matched) do
    unify(left, righties, lvars, rvars, type_lvars, type_rvars,
          acc_rvars, lefties, matched, [])
  end
  defp unify([], unmatched, _lvars, _rvars,
             type_lvars, type_rvars, acc_rvars, matched) do
    {type_lvars, type_rvars, acc_rvars, matched, unmatched}
  end

  defp unify(left, [right | righties], lvars, rvars, type_lvars, type_rvars,
             acc_rvars, lefties, matched, unmatched) do
    case unify_each(left, right, lvars, rvars, type_lvars, type_rvars, acc_rvars) do
      {type_lvars, type_rvars, acc_rvars} ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_rvars, lefties, [right | matched], unmatched)
      :error ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_rvars, lefties, matched, [right | unmatched])
    end
  end
  defp unify(_left, [], _lvars, _rvars,
             type_lvars, type_rvars, acc_rvars, lefties, matched, righties) do
    unify(lefties, righties, type_lvars, type_rvars,
          type_lvars, type_rvars, acc_rvars, matched)
  end

  defp unify_each({:var, _, key1}, {:var, _, key2} = right,
                  lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    with {types, added, removed} <- unify_var(lvars, key1, [right]) do
      {Map.update(type_lvars, key1, types, &((&1 -- removed) ++ added)),
       type_rvars,
       Map.put(acc_rvars, key2, Map.fetch!(type_rvars, key2))}
    end
  end

  defp unify_each({:var, _, key}, right,
                  lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    with {types, added, removed} <- unify_var(lvars, key, [right]) do
      {Map.update(type_lvars, key, types, &((&1 -- removed) ++ added)),
       type_rvars,
       acc_rvars}
    end
  end

  defp unify_each(left, {:var, _, key},
                  _lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    with {types, added, removed} <- unify_var(rvars, key, [left]) do
      {type_lvars,
       Map.update(type_rvars, key, types, &((&1 -- removed) ++ added)),
       Map.update(acc_rvars, key, types, &((&1 -- removed) ++ added))}
    end
  end

  defp unify_each(type, type, _lvars, _rvars, type_lvars, type_rvars, acc_rvars),
    do: {type_lvars, type_rvars, acc_rvars}

  defp unify_each(:atom, {:value, atom},
                  _lvars, _rvars, type_lvars, type_rvars, acc_rvars) when is_atom(atom),
    do: {type_lvars, type_rvars, acc_rvars}

  defp unify_each({:fn, lefties, arity}, {:fn, righties, arity},
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_fn(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars)
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars)
  end

  defp unify_each(_left, _right, _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars),
    do: :error

  defp unify_var(vars, key, types) do
    case Map.get(vars, key, []) do
      [] ->
        {types, types, []}
      existing ->
        case intersection(existing, types) do
          {[], _added, _remove} -> :error
          {types, added, removed} -> {types, added, removed}
        end
    end
  end

  defp unify_args([left | lefties], [right | righties],
                  lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    case unify(left, right, lvars, rvars, type_lvars, type_rvars, acc_rvars, []) do
      {type_lvars, type_rvars, acc_rvars, _, []} ->
        unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_rvars)
      {_, _, _, _, _} ->
        :error
    end
  end
  defp unify_args([], [], _lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    {type_lvars, type_rvars, acc_rvars}
  end

  defp unify_fn([{left_head, left_body} | lefties], righties,
                lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    unify_fn(left_head, left_body, righties, lefties, righties,
             lvars, rvars, type_lvars, type_rvars, acc_rvars)
  end
  defp unify_fn([], _righties, _lvars, _rvars, type_lvars, type_rvars, acc_rvars) do
    {type_lvars, type_rvars, acc_rvars}
  end

  defp unify_fn(left_head, left_body, [{right_head, right_body} | clauses], lefties, righties,
                lvars, rvars, type_lvars, type_rvars, acc_rvars) do
    with {temp_lvars, temp_rvars, temp_acc} <-
           unify_args(left_head, right_head, lvars, rvars, type_lvars, type_rvars, acc_rvars),
         {temp_lvars, temp_rvars, temp_acc, _, []} <-
           unify(left_body, bind(right_body, temp_rvars, type_rvars), temp_lvars, temp_rvars, temp_lvars, temp_rvars, temp_acc, []) do
      type_rvars = preserve_inferred(type_rvars, temp_rvars)
      acc_rvars = preserve_inferred(acc_rvars, temp_acc)
      unify_fn(lefties, righties, lvars, rvars, temp_lvars, type_rvars, acc_rvars)
    else
      _ -> unify_fn(left_head, left_body, clauses, lefties, righties,
                    lvars, rvars, type_lvars, type_rvars, acc_rvars)
    end
  end
  defp unify_fn(_, _, [], _lefties, _righties, _lvars, _rvars, _type_lvars, _type_rvars, _acc_rvars) do
    :error
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
      for {head, body} <- clauses do
        {bind_args(head, vars, preserve), bind(body, vars, preserve)}
      end
    bind_each(types, [{:fn, clauses, arity} | acc], vars, preserve)
  end
  defp bind_each([{:var, _, key} = type | types], acc, vars, preserve) do
    case Map.get(preserve, key, []) do
      [] ->
        case Map.get(vars, key, []) do
          [] ->
            bind_each(types, [type | acc], vars, preserve)
          existing ->
            bind_each(types, union(bind_each(existing, [], vars, preserve), acc), vars, preserve)
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

  defp of({var, meta, ctx}, %{vars: vars} = state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, types} -> ok(types, state)
      :error -> error(meta, {:unbound_var, var, ctx})
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
  defp of({{:., _, [fun]}, meta, [arg] = args}, state) do
    with {:ok, fun_type, fun_state} <- of(fun, state),
         {:ok, arg_types, arg_state} <- of(arg, replace_vars(fun_state, state)) do
      arity = length(args)
      state = lift_vars(arg_state, fun_state)

      # TODO: Generalize matching to support multiple functions
      case fun_type do
        [{:fn, clauses, ^arity}] ->
          %{inferred: inferred} = state

          case of_apply(clauses, arg_types, inferred, arg_types, inferred, []) do
            {:ok, acc_inferred, acc_body} ->
              ok(acc_body, %{state | inferred: acc_inferred})
            {:error, pending} ->
              error(meta, {:disjoint_apply, pending, clauses, arg_types})
          end
        [{:var, _, var_key}] ->
          %{counter: counter, inferred: inferred} = state

          case of_var_apply(var_key, arg_types, arity, inferred) do
            {:match, types, return} ->
              inferred = Map.put(inferred, var_key, types)
              ok(return, %{state | inferred: inferred})
            {:nomatch, types} ->
              return = [{:var, {:var, Elixir}, counter}]
              types =
                for {:fn, clauses, arity} <- types do
                  {:fn, [{[arg_types], return} | clauses], arity}
                end
              inferred =
                inferred
                |> Map.put(var_key, types)
                |> Map.put(counter, [])
              ok(return, %{state | inferred: inferred, counter: counter + 1})
            :error ->
              error(meta, {:invalid_fn, fun_type, arity})
          end
        _ ->
          error(meta, {:invalid_fn, fun_type, arity})
      end
    end
  end

  defp of(value, state) do
    literal(value, state, &of/2)
  end

  ## Apply

  defp of_var_apply(key, arg, arity, inferred) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], arity}]}
      existing ->
        case for({:fn, _clauses, ^arity} = type <- existing, do: type) do
          [] ->
            :error
          types ->
            # TODO: Use of_apply
            return =
              for {:fn, clauses, _arity} <- types,
                  {[head], body} <- clauses,
                  body <- of_var_apply_body(head, body, arg, inferred),
                  do: body
            if return == [], do: {:nomatch, types}, else: {:match, types, return}
        end
    end
  end

  # TODO: Use of_apply
  defp of_var_apply_body(head, body, arg, inferred) do
    case unify(head, arg, inferred, inferred) do
      {lvars, _, _, _, []} -> bind(body, lvars)
      {_, _, _, _, _} -> []
    end
  end

  defp of_apply([{[head], body} | clauses], arg, inferred, acc_arg, acc_inferred, acc_body) do
    with {lvars, _, rvars, [_ | _] = matched, _} <- unify(head, arg, inferred, acc_inferred) do
      acc_body = union(acc_body, bind(body, lvars))
      of_apply(clauses, arg, inferred, acc_arg -- matched, rvars, acc_body)
    else
      _ -> of_apply(clauses, arg, inferred, acc_arg, acc_inferred, acc_body)
    end
  end
  defp of_apply([], _arg, _inferred, [], acc_inferred, acc_body) do
    {:ok, acc_inferred, acc_body}
  end
  defp of_apply([], _arg, _inferred, pending, _acc_inferred, _acc_body) do
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
    with {lvars, _, rvars, _, []} <- unify(left, right, inferred, inferred) do
      lvars =
        Enum.reduce(match, vars, fn {var_ctx, types}, acc ->
          Map.put(acc, var_ctx, bind(types, lvars))
        end)
      {:ok, lvars, rvars, bind(right, inferred)}
    else
      _ -> :error
    end
  end

  ## Clauses

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  defp of_clauses(clauses, state) do
    of_clauses(clauses, state, [], state)
  end

  defp of_clauses([{:->, _, [[arg], body]} | clauses], %{inferred: preserve} = state, acc_clauses, acc_state) do
    with {:ok, head, %{match: match, vars: vars} = acc_state} <- of_pattern(arg, acc_state),
         acc_state = %{acc_state | vars: Map.merge(match, vars)},
         {:ok, body, %{inferred: inferred} = acc_state} <- of(body, acc_state) do
      head = bind_args([head], inferred, preserve)
      body = bind(body, inferred, preserve)
      preserve = preserve_inferred(preserve, inferred)
      acc_state = replace_vars(%{acc_state | inferred: preserve}, state)
      of_clauses(clauses, state, [{head, body} | acc_clauses], acc_state)
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

  ## Patterns

  defp of_pattern(ast, state) do
    of_pattern_each(ast, %{state | match: %{}})
  end

  defp of_pattern_each({:::, meta, [{var, _, ctx}, type_ast]}, state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    with {:ok, type, state} <- ast_to_type(type_ast, state) do
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

  # Keep only the variables we already knew about.
  defp preserve_inferred(preserve, latest) do
    Enum.reduce(preserve, preserve, fn {i, _}, acc ->
      Map.put(acc, i, Map.fetch!(latest, i))
    end)
  end

  @compile {:inline, ok: 2, error: 2}

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
