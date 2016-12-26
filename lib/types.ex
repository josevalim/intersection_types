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
  # 1. A variable on the right side must appear on all unions on the left side.
  # 2. Annotations may have multiple clauses. Each clause must have at least one matching implementation.
  # 3. Mixing variables with non-variables. Currently we don't allow unions with non variables.

  ## Guards
  # Must perform exhaustion check based on patterns
  # Must perform exhaustion check for base types (integers, atoms, floats, etc)
  # Pattern matches {a, a} also require an exaustion check

  ## State helpers

  @state %{vars: %{}, match: %{}, counter: 0}

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
  # {:fn, clauses, arity}
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
  """
  def unify(left, right) do
    unify(left, right, %{}, %{})
  end

  # TODO: Test me (use qualify tests)
  # TODO: Add right side unification once we figure out how to store those.
  defp unify([{:var, _, counter}], right, lvars, rvars) do
    case lvars do
      %{^counter => _existing} ->
        # TODO: Implement me
        raise "implement merging with disjoint check"
      %{} ->
        {:ok, Map.put(lvars, counter, right), rvars}
    end
  end

  defp unify([left | lefties], righties, lvars, rvars) do
    unify_left_right(left, righties, {lefties, righties}, lvars, rvars)
  end
  defp unify([], _righties, lvars, rvars) do
    {:ok, lvars, rvars}
  end

  defp unify_left_right(left, [right | righties], pair, lvars, rvars) do
    case unify_each(left, right, lvars, rvars) do
      {:ok, lvars, rvars} -> unify_left_right(left, righties, pair, lvars, rvars)
      {:error, _} = error -> error
    end
  end
  defp unify_left_right(_left, [], {lefties, righties}, lvars, rvars) do
    unify(lefties, righties, lvars, rvars)
  end

  defp unify_each(type, type, lvars, rvars),
    do: {:ok, lvars, rvars}

  defp unify_each(:atom, {:value, atom}, lvars, rvars) when is_atom(atom),
    do: {:ok, lvars, rvars}

  defp unify_each(:integer, {:value, int}, lvars, rvars) when is_integer(int),
    do: {:ok, lvars, rvars}

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity}, lvars, rvars) do
    case unify_args(lefties, righties, 0, lvars, rvars) do
      {:ok, _, _} = ok ->
        ok
      {:error, pos, reason} ->
        {:error, {:tuple, lefties, righties, arity, pos, reason}}
    end
  end

  defp unify_each(left, right, _lvars, _rvars),
    do: {:error, {:match, left, right}}

  defp unify_args([left | lefties], [right | righties], pos, lvars, rvars) do
    case unify(left, right, lvars, rvars) do
      {:ok, lvars, rvars} -> unify_args(lefties, righties, pos + 1, lvars, rvars)
      {:error, reason} -> {:error, pos, reason}
    end
  end
  defp unify_args([], [], _pos, lvars, rvars), do: {:ok, lvars, rvars}

  @doc """
  Binds the variables retrieved during unification.
  """
  def bind(types, vars) when vars == %{} do
    types
  end
  def bind(types, vars) do
    Enum.map(types, &bind_each(&1, vars))
  end

  defp bind_each({:var, _, counter}, vars) do
    Map.fetch!(vars, counter)
  end
  defp bind_each({:tuple, args, arity}, vars) do
    {:tuple, bind_args(args, vars), arity}
  end
  defp bind_each({:fn, clauses, arity}, vars) do
    clauses = Enum.map(clauses, fn {head, body} -> {bind_args(head, vars), bind(body, vars)} end)
    {:fn, clauses, arity}
  end
  defp bind_each(other, _vars) do
    other
  end

  defp bind_args(args, vars) do
    Enum.map(args, &bind(&1, vars))
  end

  @doc """
  Binds and merges the types, but only if there are variables.

  This is an optimization to avoid merging if all types are
  going to be exactly the same.
  """
  def bind_and_merge(sum, _types, vars) when vars == %{}, do: sum
  def bind_and_merge(sum, types, vars), do: merge(sum, bind(types, vars))

  @doc """
  Merges two union types.
  """
  def merge(left, []), do: left
  def merge([], right), do: right
  def merge(left, right), do: Enum.reduce(left, right, &merge_left_right/2)

  defp merge_left_right(left, [right | righties]) do
    case merge_each(left, right) do
      {:ok, type} -> [type | righties]
      :error -> [right | merge_left_right(left, righties)]
    end
  end
  defp merge_left_right(left, []) do
    [left]
  end

  defp merge_each(type, type), do: {:ok, type}

  defp merge_each(:integer, {:value, int}) when is_integer(int), do: {:ok, :integer}
  defp merge_each({:value, int}, :integer) when is_integer(int), do: {:ok, :integer}
  defp merge_each(:atom, {:value, atom}) when is_atom(atom), do: {:ok, :atom}
  defp merge_each({:value, atom}, :atom) when is_atom(atom), do: {:ok, :atom}

  defp merge_each({:tuple, args1, arity}, {:tuple, args2, arity}) do
    case merge_args(args1, args2, [], false) do
      {:ok, args} -> {:ok, {:tuple, args, arity}}
      :error -> :error
    end
  end

  defp merge_each(_, _), do: :error

  defp merge_args([left | lefties], [right | righties], acc, changed?) do
    left = Enum.sort(left)
    right = Enum.sort(right)
    case left == right do
      false when changed? -> :error
      false -> merge_args(lefties, righties, [merge(left, right) | acc], true)
      true -> merge_args(lefties, righties, [left | acc], changed?)
    end
  end
  defp merge_args([], [], acc, _changed?) do
    {:ok, Enum.reverse(acc)}
  end

  @doc """
  Fetches the type from a pattern.
  """
  def pattern_to_type(ast, state \\ @state) do
    case pattern(ast, %{state | match: %{}}) do
      {:ok, type, %{vars: vars, match: match} = state} ->
        {:ok, type, %{state | vars: Map.merge(vars, match), match: %{}}}
      {:error, _, _} = error ->
        error
    end
  end

  defp pattern({:::, meta, [{var, _, ctx}, type_ast]}, state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    with {:ok, type, state} <- ast_to_type(type_ast, state) do
      pattern_bound_var(meta, {var, ctx}, type, state)
    end
  end

  # TODO: Add tests for a
  # TODO: Add tests for {a, a}
  # TODO: Add tests for {a::boolean(), a}
  defp pattern({var, meta, ctx}, state) when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    pattern_var(meta, {var, ctx}, state)
  end

  defp pattern({:::, meta, [_, _]} = ann, _vars) do
    error(meta, {:invalid_annotation, ann})
  end

  defp pattern(other, vars) do
    literal(other, vars, &pattern/2)
  end

  defp pattern_var(_meta, var_ctx, %{counter: counter, match: match} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, type} ->
        ok(type, state)
      :error ->
        counter = counter + 1
        type = {:var, var_ctx, counter}
        match = Map.put(match, var_ctx, type)
        ok(type, %{state | match: match, counter: counter})
    end
  end

  defp pattern_bound_var(meta, var_ctx, type, %{match: match} = state) do
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

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, @state)
  end

  defp of({var, meta, ctx}, %{vars: vars} = state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, type} -> ok(type, state)
      :error -> error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, state) do
    with {:ok, clauses} <- of_clauses(clauses, state) do
      ok([{:fn, :lists.reverse(clauses), 1}], state)
    end
  end

  defp of({:__block__, _meta, args}, state) do
    of_block(args, state)
  end

  defp of({:=, _, [{var, _, ctx}, right]}, state) when is_atom(var) and is_atom(ctx) do
    # TODO: Properly process left side and merge state
    with {:ok, type, %{vars: vars} = state} <- of(right, state) do
      vars = Map.put(vars, {var, ctx}, type)
      ok(type, %{state | vars: vars})
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
          with {:ok, arg_type, arg_state} <- of(arg, replace_vars(fun_state, state)) do
            case of_apply(clauses, arg_type, [], []) do
              {:ok, body} -> ok(body, lift_vars(arg_state, fun_state))
              {:error, error} -> error(meta, {:disjoint_fn, error})
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

  defp of_apply([{[head], body} | clauses], arg, sum, errors) do
    case of_apply_clause(arg, head, body, body) do
      {:ok, body} -> of_apply(clauses, arg, merge(sum, body), errors)
      {:error, error} -> of_apply(clauses, arg, sum, [error | errors])
    end
  end
  defp of_apply([], _arg, [], errors) do
    {:error, errors}
  end
  defp of_apply([], _arg, sum, _errors) do
    {:ok, sum}
  end

  # TODO: Test use of bind and merge
  # TODO: Document the logic behind this function with bind, unify and merge
  defp of_apply_clause([type | types], head, body, sum) do
    case unify(head, [type]) do
      {:ok, vars, _} -> of_apply_clause(types, head, body, bind_and_merge(sum, body, vars))
      {:error, _} = error -> error
    end
  end
  defp of_apply_clause([], _head, _body, sum) do
    {:ok, sum}
  end

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  # TODO: Remove Enum.reduce
  # TODO: Keep the state because of the counter
  defp of_clauses(clauses, state) do
    Enum.reduce(clauses, {:ok, []}, fn
      {:->, _, [[arg], body]}, {:ok, clauses} ->
        with {:ok, head, state} <- pattern_to_type(arg, state),
             {:ok, body, _state} <- of(body, state),
             do: {:ok, [{[head], body} | clauses]}

      _, {:error, _, _} = error ->
        error
    end)
  end

  defp of_block([arg], state) do
    of(arg, state)
  end
  defp of_block([arg | args], state) do
    case of(arg, state) do
      {:ok, _, state} -> of_block(args, state)
      {:error, _, _} = error -> error
    end
  end

  ## Helpers

  # TODO: Remove integers from values and convert to ":integer"
  defp literal(value, state, _fun) when is_integer(value) or is_atom(value) do
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
    {:ok, Enum.reverse(acc_args), acc_count, acc_state}
  end

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
