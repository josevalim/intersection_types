defmodule TypesTest do
  use ExUnit.Case, async: true
  import Types

  describe "value?/1" do
    test "accepts integers" do
      assert value?(true)
      assert value?(false)
    end

    test "accepts atoms" do
      assert value?(:foo)
      assert value?(true)
      assert value?(false)
      assert value?(nil)
    end
  end

  defmacro quoted_qualify(left, right) do
    with {:ok, [left], _} <- pattern_to_type(left, %{}),
         {:ok, [right], _} <- pattern_to_type(right, %{}) do
      quote do
        qualify(unquote(Macro.escape(left)), unquote(Macro.escape(right)))
      end
    else
      _ ->
        quote do
          assert {:ok, [_], _} = pattern_to_type(unquote(Macro.escape(left)), %{})
          assert {:ok, [_], _} = pattern_to_type(unquote(Macro.escape(right)), %{})
        end
    end
  end

  describe "qualify/2" do
    test "superset and subset" do
      assert quoted_qualify(x :: integer(), 1) == :superset
      assert quoted_qualify(1, x :: integer()) == :subset

      assert quoted_qualify(x :: atom(), :foo) == :superset
      assert quoted_qualify(:foo, x :: atom()) == :subset

      assert quoted_qualify(x :: atom(), true) == :superset
      assert quoted_qualify(true, x :: atom()) == :subset
    end

    test "equal" do
      assert quoted_qualify(x :: integer(), x :: integer()) == :equal
      assert quoted_qualify(:foo, :foo) == :equal
      assert quoted_qualify(1, 1) == :equal
    end

    test "disjoint" do
      assert quoted_qualify(1, 0) == :disjoint
      assert quoted_qualify(0, 1) == :disjoint

      assert quoted_qualify(x :: atom(), 1) == :disjoint
      assert quoted_qualify(1, x :: atom()) == :disjoint

      assert quoted_qualify(x :: integer(), :foo) == :disjoint
      assert quoted_qualify(:foo, x :: integer()) == :disjoint
    end
  end

  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  describe "of/1" do
    test "booleans" do
      assert {:ok, [{:value, true}]} = quoted_of(true)
      assert {:ok, [{:value, false}]} = quoted_of(false)
    end

    test "functions" do
      assert {:ok, [{:fn, [
               {[{:value, true}, {:value, false}], [{:value, true}, {:value, false}]}
             ], 1}]} =
             quoted_of(fn bool :: boolean() -> bool end)

      assert {:ok, [{:fn, [
               {[{:value, false}], [{:value, true}]},
               {[{:value, true}], [{:value, false}]}
             ], 1}]} =
             quoted_of(fn false -> true; true -> false end)
    end

    test "function calls" do
      assert {:ok, [{:value, true}]} =
             quoted_of((fn false -> true; true -> false end).(false))

      assert {:ok, [{:value, false}]} =
             quoted_of((fn false -> true; true -> false end).(true))
    end
  end
end
