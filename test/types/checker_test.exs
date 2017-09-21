defmodule Types.CheckerTest do
  use ExUnit.Case, async: true

  defmacro expr!(expr) do
    {expr, _} = :elixir_expand.expand(expr, __CALLER__)
    quote do
      {_expr, types, _} = Types.Checker.expr(unquote(expr), Types.Checker.init)
      types |> Types.Union.to_iodata() |> IO.iodata_to_binary()
    end
  end

  describe "basic types" do
    test "is inferred for integers" do
      assert expr!(0) == "integer()"
    end

    test "is inferred for atoms" do
      assert expr!(:foo) == ":foo"
    end
  end
end
