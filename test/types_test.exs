defmodule TypesTest do
  use ExUnit.Case, async: true

  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  describe "of/1" do
    test "booleans" do
      assert {:ok, [{:value, [true]}]} = quoted_of(true)
      assert {:ok, [{:value, [false]}]} = quoted_of(false)
    end

    test "functions" do
      assert {:ok, [{:fn, [[
               {[{:boolean, []}], [{:boolean, []}]}
             ], 1]}]} =
             quoted_of(fn bool :: boolean() -> bool end)

      assert {:ok, [{:fn, [[
               {[{:value, [false]}], [{:value, [true]}]},
               {[{:value, [true]}], [{:value, [false]}]}
             ], 1]}]} =
             quoted_of(fn false -> true; true -> false end)
    end

    test "function calls" do
      assert {:ok, [{:value, [true]}]} =
             quoted_of((fn false -> true; true -> false end).(false))

      assert {:ok, [{:value, [false]}]} =
             quoted_of((fn false -> true; true -> false end).(true))
    end
  end
end
