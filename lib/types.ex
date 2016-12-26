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
  # 2. May have multiple clauses. Each clause must have at least one matching implementation.

  ## Guards
  # Must perform exhaustion check
  # Pattern matches {a, a} also require an exaustion check

  ## State helpers

  @state %{vars: %{}}

  defp merge_state(%{vars: vars1} = state, %{vars: vars2}) do
    %{state | vars: Map.merge(vars1, vars2)}
  end

  @doc """
  Converts the given AST to its inner type.
  """

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
  # :integer
  # :atom

  def ast_to_type(ast) do
    ast_to_type(ast, @state)
  end

  defp ast_to_type({:boolean, _, []}, state) do
    ok([{:value, true}, {:value, false}], state)
  end
  defp ast_to_type({:integer, _, []}, state) do
    ok([:integer], state)
  end
  defp ast_to_type({:atom, _, []}, state) do
    ok([:atom], state)
  end
  defp ast_to_type(other, state) do
    literal(other, state, &ast_to_type/2)
  end

  @doc """
  Unifies the types on left and right.
  """
  def unify(left, right) do
    unify(left, right, %{})
  end

  # TODO: Test me (use qualify tests)
  # TODO: Add right side unification once we figure out how to store those.
  defp unify([{:var, counter}], right, vars) do
    unify_var(vars, counter, right)
  end

  defp unify(lefties, righties, vars) do
    # TODO: Remove Enum.reduce
    Enum.reduce(righties, {:ok, vars}, fn right, acc ->
      Enum.reduce(lefties, acc, fn
        left, {:ok, vars} ->
          unify_each(left, right, vars)
        _, {:error, _} = error ->
          error
      end)
    end)
  end

  defp unify_each(type, type, vars), do: {:ok, vars}
  defp unify_each(:atom, {:value, atom}, vars) when is_atom(atom), do: {:ok, vars}
  defp unify_each(:integer, {:value, int}, vars) when is_integer(int), do: {:ok, vars}
  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity}, vars) do
    case unify_args(lefties, righties, vars, 0) do
      {:ok, _} = ok ->
        ok
      {:error, pos, reason} ->
        {:error, {:tuple, lefties, righties, arity, pos, reason}}
    end
  end
  defp unify_each(left, right, _vars) do
    {:error, {:match, left, right}}
  end

  defp unify_var(vars, counter, types) do
    case vars do
      %{^counter => _existing} ->
        # TODO: Implement me
        raise "implement merging with disjoint check"
      %{} ->
        {:ok, Map.put(vars, counter, types)}
    end
  end

  defp unify_args([left | lefties], [right | righties], pos, vars) do
    case unify(left, right, vars) do
      {:ok, vars} -> unify_args(lefties, righties, pos + 1, vars)
      {:error, reason} -> {:error, pos, reason}
    end
  end
  defp unify_args([], [], _pos, vars), do: {:ok, vars}

  @doc """
  Binds the variables retrieved during unification.
  """
  def bind(types, vars) when vars == %{} do
    types
  end
  def bind(types, vars) do
    Enum.map(types, &bind_each(&1, vars))
  end

  defp bind_each({:var, counter}, vars) do
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
  Converts the given pattern to a type.
  """
  def pattern_to_type(ast) do
    pattern_to_type(ast, @state)
  end

  defp pattern_to_type(ast, %{vars: backup} = state) do
    with {:ok, type, state} <- pattern_to_type(ast, backup, put_in(state.vars, %{})) do
      {:ok, type, update_in(state.vars, &Map.merge(backup, &1))}
    end
  end

  defp pattern_to_type({:::, meta, [{var, _, ctx}, type_ast]},
                       _backup, state) when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    with {:ok, type, state} <- ast_to_type(type_ast, state) do
      pattern_var(meta, {var, ctx}, type, state)
    end
  end

  defp pattern_to_type({:::, meta, [_, _]} = ann, _backup, _vars) do
    error(meta, {:invalid_annotation, ann})
  end

  defp pattern_to_type(other, backup, vars) do
    literal(other, vars, &pattern_to_type(&1, backup, &2))
  end

  defp pattern_var(meta, var_ctx, type, %{vars: vars} = state) do
    # TODO: What if type is exactly the same?
    case Map.fetch(vars, var_ctx) do
      {:ok, other} ->
        error(meta, {:bound_var, var_ctx, other, type})
      :error ->
        vars = Map.put(vars, var_ctx, type)
        ok(type, %{state | vars: vars})
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
    # TODO: Remove Enum.reduce
    Enum.reduce(args, {:ok, nil, state}, fn arg, acc ->
      with {:ok, _, state} <- acc, do: of(arg, state)
    end)
  end

  defp of({:=, _, [{var, _, ctx}, right]}, state) when is_atom(var) and is_atom(ctx) do
    # TODO: Properly process left side and merge state
    with {:ok, type, %{vars: vars} = state} <- of(right, state) do
      vars = Map.put(vars, {var, ctx}, type)
      ok(type, %{state | vars: vars})
    end
  end

  # TODO: Support multiple args
  defp of({{:., _, [fun]}, meta, args}, state) do
    with {:ok, fun_type, fun_state} <- of(fun, state) do
      arity = length(args)

      case fun_type do
        [{:fn, clauses, ^arity}] ->
          [arg] = args
          with {:ok, arg_type, arg_state} <- of(arg, state) do
            case of_apply(clauses, arg_type, [], []) do
              {:ok, body} -> ok(body, merge_state(fun_state, arg_state))
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

  defp of_apply_clause([type | types], head, body, sum) do
    # TODO: Test use of bind and merge
    case unify(head, [type]) do
      {:ok, vars} -> of_apply_clause(types, head, body, bind_and_merge(sum, body, vars))
      {:error, _} = error -> error
    end
  end
  defp of_apply_clause([], _head, _body, sum) do
    {:ok, sum}
  end

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  # TODO: Remove Enum.reduce
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

  ## Helpers

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
    # TODO: Remove Enum.reduce
    ok_error =
      Enum.reduce(args, {:ok, [], 0, state}, fn arg, acc ->
        with {:ok, acc_args, acc_count, acc_state} <- acc,
             {:ok, arg, arg_state} <- fun.(arg, state),
             do: {:ok, [arg | acc_args], acc_count + 1, merge_state(acc_state, arg_state)}
      end)

    case ok_error do
      {:ok, args, arity, state} ->
        {:ok, Enum.reverse(args), arity, state}
      {:error, _, _} = error ->
        error
    end
  end

  defp ok(type, vars) when is_list(type) do
    {:ok, type, vars}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
