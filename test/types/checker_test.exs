defmodule Types.CheckerTest do
  use ExUnit.Case, async: true

  defmacro expr!(expr) do
    {expr, _} = :elixir_expand.expand(expr, __CALLER__)
    quote do
      {:ok, types, _} = Types.Checker.expr(unquote(expr), Types.Checker.init)
      types
    end
  end

  describe "basic types" do
    test "is inferred for integers" do
      assert expr!(0) == [:integer]
    end
  end
end
