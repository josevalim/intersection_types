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
  # {:var, var_ctx, counter}
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

  All of the types on the right must match at least one type on the left.
  """
  def unify(left, right, lvars, rvars, acc_lvars, acc_rvars) do
    unify(left, right, lvars, rvars, lvars, rvars, acc_lvars, acc_rvars, [])
  end

  defp unify([left | lefties], righties, lvars, rvars,
             type_lvars, type_rvars, acc_lvars, acc_rvars, matched) do
    unify(left, righties, lvars, rvars, type_lvars, type_rvars,
          acc_lvars, acc_rvars, lefties, matched, [])
  end
  defp unify([], unmatched, _lvars, _rvars,
             type_lvars, type_rvars, acc_lvars, acc_rvars, matched) do
    {type_lvars, type_rvars, acc_lvars, acc_rvars, matched, unmatched}
  end

  defp unify(left, [right | righties], lvars, rvars, type_lvars, type_rvars,
             acc_lvars, acc_rvars, lefties, matched, unmatched) do
    case unify_each(left, right, lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
      {type_lvars, type_rvars, acc_lvars, acc_rvars} ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_lvars, acc_rvars, lefties, [right | matched], unmatched)
      :error ->
        unify(left, righties, lvars, rvars, type_lvars, type_rvars,
              acc_lvars, acc_rvars, lefties, matched, [right | unmatched])
    end
  end
  defp unify(_left, [], _lvars, _rvars,
             type_lvars, type_rvars, acc_lvars, acc_rvars, lefties, matched, righties) do
    unify(lefties, righties, type_lvars, type_rvars,
          type_lvars, type_rvars, acc_lvars, acc_rvars, matched)
  end

  defp unify_each({:var, _, c1}, {:var, _, c2} = right,
                  lvars, _rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    with {type_lvars, acc_lvars} <- unify_var(lvars, type_lvars, acc_lvars, c1, [right]) do
      {type_lvars, Map.delete(type_rvars, c2), acc_lvars, Map.delete(acc_rvars, c2)}
    end
  end

  defp unify_each({:var, _, counter}, right,
                  lvars, _rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    with {type_lvars, acc_lvars} <- unify_var(lvars, type_lvars, acc_lvars, counter, [right]),
         do: {type_lvars, type_rvars, acc_lvars, acc_rvars}
  end

  defp unify_each(left, {:var, _, counter},
                  _lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    with {type_rvars, acc_rvars} <- unify_var(rvars, type_rvars, acc_rvars, counter, [left]),
         do: {type_lvars, type_rvars, acc_lvars, acc_rvars}
  end

  defp unify_each(type, type, _lvars, _rvars, type_lvars, type_rvars, acc_lvars, acc_rvars),
    do: {type_lvars, type_rvars, acc_lvars, acc_rvars}

  defp unify_each(:atom, {:value, atom},
                  _lvars, _rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) when is_atom(atom),
    do: {type_lvars, type_rvars, acc_lvars, acc_rvars}

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars)
  end

  defp unify_each(_left, _right, _lvars, _rvars, _type_lvars, _type_rvars, _acc_lvars, _acc_rvars),
    do: :error

  defp unify_var(vars, type_vars, acc_vars, key, types) do
    case vars do
      %{^key => existing} ->
        case intersection(existing, types) do
          [] ->
            :error
          types ->
            {Map.update(type_vars, key, types, &union(&1, types)),
             Map.update(acc_vars, key, types, &union(&1, types))}
        end
      %{} ->
        {Map.update(type_vars, key, types, &union(&1, types)),
         Map.update(acc_vars, key, types, &union(&1, types))}
    end
  end

  defp unify_args([left | lefties], [right | righties],
                  lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    case unify(left, right, lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars, []) do
      {type_lvars, type_rvars, acc_lvars, acc_rvars, _, []} ->
        unify_args(lefties, righties, lvars, rvars, type_lvars, type_rvars, acc_lvars, acc_rvars)
      {_, _, _, _, _, _} ->
        :error
    end
  end
  defp unify_args([], [], _lvars, _rvars, type_lvars, type_rvars, acc_lvars, acc_rvars) do
    {type_lvars, type_rvars, acc_lvars, acc_rvars}
  end

  @doc """
  Binds the variables to their types.
  """
  def bind(types, vars)

  def bind(types, vars) when vars == %{} do
    types
  end
  def bind(types, vars) do
    bind_each(types, [], vars)
  end

  defp bind_each([{:fn, clauses, arity} | types], acc, vars) do
    clauses =
      for {head, body} <- clauses do
        {bind_args(head, vars), bind(body, vars)}
      end
    bind_each(types, [{:fn, clauses, arity} | acc], vars)
  end
  defp bind_each([{:var, _, counter} = type | types], acc, vars) do
    case vars do
      %{^counter => existing} ->
        bind_each(types, union(bind_each(existing, [], vars), acc), vars)
      %{} ->
        bind_each(types, [type | acc], vars)
    end
  end
  defp bind_each([{:tuple, args, arity} | types], acc, vars) do
    bind_each(types, [{:tuple, bind_args(args, vars), arity} | acc], vars)
  end
  defp bind_each([type | types], acc, vars) do
    bind_each(types, [type | acc], vars)
  end
  defp bind_each([], acc, _vars) do
    acc
  end

  defp bind_args(args, vars) do
    Enum.map(args, &bind(&1, vars))
  end

  @doc """
  Computes the union of two union types.
  """
  def union(left, []), do: left
  def union([], right), do: right
  def union(left, right), do: Enum.reduce(left, right, &union_left_right/2)

  defp union_left_right(left, [right | righties]) do
    case union_type(left, right) do
      {:ok, type} -> [type | righties]
      :error -> [right | union_left_right(left, righties)]
    end
  end
  defp union_left_right(left, []) do
    [left]
  end

  defp union_type(left, right) do
    case qualify(left, right) do
      :disjoint -> :error
      :superset -> {:ok, left}
      :subset -> {:ok, right}
      :equal -> {:ok, left}
    end
  end

  @doc """
  Computes the intersection between two union types.
  """
  def intersection(lefties, righties) do
    intersection(lefties, righties, [])
  end

  defp intersection([left | lefties], righties, acc) do
    intersection(left, righties, lefties, righties, acc)
  end
  defp intersection([], _righties, acc) do
    :lists.reverse(acc)
  end

  defp intersection(left, [head | tail], lefties, righties, acc) do
    case intersection_type(left, head) do
      {:ok, type} -> intersection(lefties, righties, [type | acc])
      :error -> intersection(left, tail, lefties, righties, acc)
    end
  end
  defp intersection(_left, [], lefties, righties, acc) do
    intersection(lefties, righties, acc)
  end

  defp intersection_type({:tuple, args1, arity}, {:tuple, args2, arity}) do
    case intersection_args(args1, args2, []) do
      {:ok, args} -> {:ok, {:tuple, args, arity}}
      :error -> :error
    end
  end
  defp intersection_type(left, right) do
    case qualify(left, right) do
      :disjoint -> :error
      :superset -> {:ok, right}
      :subset -> {:ok, left}
      :equal -> {:ok, left}
    end
  end

  defp intersection_args([left | lefties], [right | righties], acc) do
    case intersection(left, right) do
      [] -> :error
      intersection -> intersection_args(lefties, righties, [intersection | acc])
    end
  end
  defp intersection_args([], [], acc) do
    {:ok, :lists.reverse(acc)}
  end

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
      %{inferred: inferred} = state

      case of_match(left, right, inferred) do
        {:ok, acc_inferred, acc_body} ->
          ok(acc_body, %{state | inferred: Map.merge(inferred, acc_inferred)})
        :error ->
          error(meta, {:disjoint_match, left, right})
      end
    end
  end

  # TODO: Support multiple args
  # TODO: Support call merging
  defp of({{:., _, [fun]}, meta, args}, state) do
    with {:ok, fun_type, fun_state} <- of(fun, state) do
      arity = length(args)

      case fun_type do
        [{:fn, clauses, ^arity}] ->
          [arg] = args
          with {:ok, arg_types, arg_state} <- of(arg, replace_vars(fun_state, state)) do
            state = lift_vars(arg_state, fun_state)
            %{inferred: inferred} = state

            case of_apply(clauses, arg_types, inferred, arg_types, inferred, []) do
              {:ok, acc_inferred, acc_body} ->
                ok(acc_body, %{state | inferred: acc_inferred})
              {:error, pending} ->
                error(meta, {:disjoint_apply, pending, clauses, arg_types})
            end
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

  defp of_apply([{[head], body} | clauses], arg, inferred, acc_arg, acc_inferred, acc_body) do
    with {lvars, _, _, acc_inferred, [_ | _] = matched, _} <- unify(head, arg, %{}, inferred, %{}, acc_inferred) do
      acc_body = union(acc_body, bind(body, lvars))
      of_apply(clauses, arg, inferred, acc_arg -- matched, acc_inferred, acc_body)
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

  # TODO: Remove acc_inferred
  defp of_match(left, right, inferred) do
    with {lvars, _, _, inferred, _, []} <- unify(left, right, %{}, inferred, %{}, inferred) do
      inferred =
        Enum.reduce(lvars, inferred, fn {k, v}, acc ->
          Map.update(acc, k, v, &union(&1, v))
        end)
      {:ok, inferred, bind(right, inferred)}
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

  defp of_clauses([{:->, _, [[arg], body]} | clauses], state, acc_clauses, acc_state) do
    with {:ok, head, acc_state} <- of_pattern(arg, acc_state),
         {:ok, body, %{inferred: inferred} = acc_state} <- of(body, acc_state),
         do: of_clauses(clauses, state,
                        [{bind_args([head], inferred), bind(body, inferred)} | acc_clauses],
                        replace_vars(acc_state, state))
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
    case of_pattern_each(ast, %{state | match: %{}}) do
      {:ok, types, %{vars: vars, match: match} = state} ->
        ok(types, %{state | vars: Map.merge(vars, match), match: %{}})
      {:error, _, _} = error ->
        error
    end
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

  defp of_pattern_var(_meta, var_ctx, %{match: match, counter: counter} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, type} ->
        ok(type, state)
      :error ->
        types = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, types)
        ok(types, %{state | match: match, counter: counter + 1})
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

  @compile {:inline, ok: 2, error: 2}

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
