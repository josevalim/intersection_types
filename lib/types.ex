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
  # pattern boolean() :: true | false
  # pattern number() :: integer() | float()
  # pattern atom()
  # pattern integer()

  ## Built-in Types
  # type list(a) :: empty_list() | cons(a, list(a))
  # type improper_list(a) :: empty_list() | cons(a, list(a) | a)

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
  Qualifies the relationship between two strict types from left to right.
  """
  def qualify(type, type), do: :equal

  def qualify(:integer, {:value, int}) when is_integer(int), do: :superset
  def qualify({:value, int}, :integer) when is_integer(int), do: :subset

  def qualify(:atom, {:value, atom}) when is_atom(atom), do: :superset
  def qualify({:value, atom}, :atom) when is_atom(atom), do: :subset

  def qualify(_, _), do: :disjoint

  @doc """
  Returns true if the union type on the left contains the strict one on the right.
  """
  def contains?(lefties, right) do
    Enum.any?(lefties, fn left ->
      case qualify(left, right) do
        :superset -> true
        :equal -> true
        _ -> false
      end
    end)
  end

  @doc """
  Merges two union types.
  """
  def merge(left, []), do: left
  def merge([], right), do: right
  def merge(left, right), do: Enum.reduce(left, right, &merge_each/2)

  defp merge_each(left, [right | righties]) do
    case qualify(left, right) do
      :disjoint -> [right | merge_each(left, righties)]
      :superset -> [left | righties]
      :subset -> [right | righties]
      :equal -> [right | righties]
    end
  end
  defp merge_each(left, []) do
    [left]
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
                       _backup, state) when is_atom(var) and is_atom(ctx) do
    with {:ok, type, state} <- ast_to_type(type_ast, state) do
      bind_var(meta, {var, ctx}, type, state)
    end
  end

  defp pattern_to_type({:::, meta, [_, _]} = ann, _backup, _vars) do
    error(meta, {:invalid_pattern_annotation, ann})
  end

  defp pattern_to_type(other, backup, vars) do
    literal(other, vars, &pattern_to_type(&1, backup, &2))
  end

  defp bind_var(meta, var_ctx, type, %{vars: vars} = state) do
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

  defp of({var, meta, ctx}, %{vars: vars} = state) when is_atom(var) and is_atom(ctx) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, type} -> ok(type, state)
      :error -> error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, state) do
    with {:ok, clauses} <- clauses(clauses, state) do
      ok([{:fn, :lists.reverse(clauses), 1}], state)
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
            case fn_apply(clauses, arg_type) do
              {[], type} -> ok(type, merge_state(fun_state, arg_state))
              {pending, _} -> error(meta, {:disjoint_fn, fun_type, pending})
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

  ## of/2 helpers

  defp fn_apply(clauses, arg) do
    Enum.reduce(clauses, {arg, []}, fn {head, body}, {pending, sum} ->
      case Enum.filter(arg, &contains?(head, &1)) do
        [] -> {pending, sum}
        unified -> {pending -- unified, merge(sum, body)}
      end
    end)
  end

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  defp clauses(clauses, state) do
    Enum.reduce(clauses, {:ok, []}, fn
      {:->, _, [[arg], body]}, {:ok, clauses} ->
        with {:ok, head, state} <- pattern_to_type(arg, state),
             {:ok, body, _state} <- of(body, state),
             do: {:ok, [{head, body} | clauses]}

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
      ok({:tuple, args, arity}, state)
    end
  end
  defp literal({:{}, _, args}, state, fun) do
    with {:ok, args, arity, state} <- args(args, state, fun) do
      ok({:tuple, args, arity}, state)
    end
  end
  defp literal(other, _state, _fun) do
    error([], {:unknown_pattern, other})
  end

  defp args(args, state, fun) do
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
