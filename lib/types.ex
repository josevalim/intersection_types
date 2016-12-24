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
  # :integer
  # :atom

  def ast_to_type({:boolean, _, []}) do
    ok([{:value, true}, {:value, false}])
  end
  def ast_to_type({:integer, _, []}) do
    ok([:integer])
  end
  def ast_to_type({:atom, _, []}) do
    ok([:atom])
  end

  @doc """
  Returns true if the given term is a type value.
  """
  def value?(value) when is_integer(value) or is_atom(value), do: true
  def value?(_), do: false

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
      :superset -> [left | righties]
      :subset -> [right | righties]
      :equal -> [right | righties]
      :disjoint -> [right | merge_each(left, righties)]
    end
  end
  defp merge_each(left, []) do
    [left]
  end

  @doc """
  Converts the given pattern to a type.
  """
  def pattern_to_type({:::, meta, [{var, _, ctx}, type_ast]}, vars) when is_atom(var) and is_atom(ctx) do
    with {:ok, type} <- ast_to_type(type_ast) do
      bind_var(meta, {var, ctx}, type, vars)
    end
  end

  def pattern_to_type({:::, meta, [_, _]} = ann, _vars) do
    error(meta, {:invalid_pattern_annotation, ann})
  end

  def pattern_to_type(other, vars) do
    if value?(other) do
      ok([{:value, other}], vars)
    else
      error([], {:unknown_pattern, other})
    end
  end

  defp bind_var(meta, var_ctx, type, vars) do
    case Map.fetch(vars, var_ctx) do
      {:ok, other} -> error(meta, {:bound_var, var_ctx, other, type})
      :error -> ok(type, Map.put(vars, var_ctx, type))
    end
  end

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, %{})
  end

  defp of({var, meta, ctx}, vars) when is_atom(var) and is_atom(ctx) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, type} -> ok(type)
      :error -> error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, vars) do
    with {:ok, clauses} <- clauses(clauses, vars) do
      ok([{:fn, :lists.reverse(clauses), 1}])
    end
  end

  # TODO: Support multiple args
  defp of({{:., _, [fun]}, meta, args}, vars) do
    with {:ok, fun_type} <- of(fun, vars) do
      arity = length(args)

      case fun_type do
        [{:fn, clauses, ^arity}] ->
          [arg] = args
          with {:ok, arg_type} <- of(arg, vars) do
            case fn_apply(clauses, arg_type) do
              {[], type} -> ok(type)
              {pending, _} -> error(meta, {:disjoint_fn, fun_type, pending})
            end
          end
        _ ->
          error(meta, {:invalid_fn, fun_type, arity})
      end
    end
  end

  defp of(value, _types) do
    if value?(value) do
      ok([{:value, value}])
    else
      error([], {:unknown_expr, value})
    end
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
  defp clauses(clauses, vars) do
    Enum.reduce(clauses, {:ok, []}, fn
      {:->, _, [[arg], body]}, {:ok, clauses} ->
        with {:ok, head, pattern_vars} <- pattern_to_type(arg, %{}),
             {:ok, body} <- of(body, Map.merge(vars, pattern_vars)),
             do: {:ok, [{head, body} | clauses]}

      _, {:error, meta, args} ->
        {:error, meta, args}
    end)
  end

  ## Helpers

  defp ok(type) when is_list(type) do
    {:ok, type}
  end

  defp ok(type, vars) when is_list(type) do
    {:ok, type, vars}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end
end
