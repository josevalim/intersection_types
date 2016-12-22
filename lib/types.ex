defmodule Types do
  @moduledoc """
  A type checker for Elixir ASTs.

  ## References

    * Types and Programming Languages, Benjamin C. Pierce

  ## TODO

    * Inference
    * Overload
    * Type syntax

  """

  def of(expr) do
    of(expr, %{})
  end

  defp of(bool, _types) when is_boolean(bool) do
    {:ok, :boolean}
  end

  defp of(integer, _types) when is_integer(integer) do
    {:ok, :integer}
  end

  defp of({:if, meta, [arg, [do: do_clause, else: else_clause]]}, types) do
    with {:ok, arg_type} <- of(arg, types),
         {:ok, do_type} <- of(do_clause, types),
         {:ok, else_type} <- of(else_clause, types) do
      cond do
        arg_type != :boolean ->
          error(meta, {:if_conditional, arg_type})
        do_type != else_type ->
          error(meta, {:if_branches, do_type, else_type})
        true ->
          ok(do_type)
      end
    end
  end

  defp of({var, meta, ctx}, types) when is_atom(var) and is_atom(ctx) do
    case Map.fetch(types, {var, ctx}) do
      {:ok, type} -> ok(type)
      :error -> error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, [{:->, _, [[{:::, _, [{var, _, ctx}, type]}], body]}]}, types) when is_atom(var) and is_atom(ctx) do
    types = Map.put(types, {var, ctx}, type)
    with {:ok, body_type} <- of(body, types) do
      ok({:fn, {[type], body_type}})
    end
  end

  defp of({{:., _, [fun]}, meta, [arg]}, types) do
    with {:ok, fun_type} <- of(fun, types),
         {:ok, arg_type} <- of(arg, types) do
      case fun_type do
        {:fn, {[^arg_type], body_type}} ->
          ok(body_type)
        {:fn, {[other_type], _body_type}} ->
          error(meta, {:fn_arg, other_type, arg_type})
        _ ->
          error(meta, {:fn_app, fun_type})
      end
    end
  end

  defp ok(type) do
    {:ok, type}
  end

  defp error(meta, args) do
    {:error, args, meta}
  end
end
