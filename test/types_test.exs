defmodule TypesTest do
  use ExUnit.Case, async: true
  import Types

  # defmacro quoted_qualify(left, right) do
  #   with {:ok, [left], _} <- pattern_to_type(left),
  #        {:ok, [right], _} <- pattern_to_type(right) do
  #     quote do
  #       qualify(unquote(Macro.escape(left)), unquote(Macro.escape(right)))
  #     end
  #   else
  #     _ ->
  #       quote do
  #         assert {:ok, [_], _} = pattern_to_type(unquote(Macro.escape(left)))
  #         assert {:ok, [_], _} = pattern_to_type(unquote(Macro.escape(right)))
  #       end
  #   end
  # end

  # describe "qualify/2" do
  #   test "superset and subset" do
  #     assert quoted_qualify(x :: integer(), 1) == :superset
  #     assert quoted_qualify(1, x :: integer()) == :subset

  #     assert quoted_qualify(x :: atom(), :foo) == :superset
  #     assert quoted_qualify(:foo, x :: atom()) == :subset

  #     assert quoted_qualify(x :: atom(), true) == :superset
  #     assert quoted_qualify(true, x :: atom()) == :subset
  #   end

  #   test "equal" do
  #     assert quoted_qualify(x :: integer(), x :: integer()) == :equal
  #     assert quoted_qualify(:foo, :foo) == :equal
  #     assert quoted_qualify(1, 1) == :equal
  #   end

  #   test "disjoint" do
  #     assert quoted_qualify(1, 0) == :disjoint
  #     assert quoted_qualify(0, 1) == :disjoint

  #     assert quoted_qualify(x :: atom(), 1) == :disjoint
  #     assert quoted_qualify(1, x :: atom()) == :disjoint

  #     assert quoted_qualify(x :: integer(), :foo) == :disjoint
  #     assert quoted_qualify(:foo, x :: integer()) == :disjoint
  #   end

  #   test "tuples" do
  #     assert quoted_qualify({:ok, 1}, {x :: atom(), y :: integer()}) == :subset
  #     assert quoted_qualify({x :: atom(), y :: integer()}, {:ok, 1}) == :superset

  #     assert quoted_qualify({}, {}) == :equal
  #     assert quoted_qualify({1, 2}, {1, 2}) == :equal
  #     assert quoted_qualify({1, 2}, {1, 2, 3}) == :disjoint
  #   end
  # end

  defmacro quoted_union(left, right) do
    with {:ok, left, _} <- pattern_to_type(left),
         {:ok, right, _} <- pattern_to_type(right) do
      quote do
        union(unquote(Macro.escape(left)), unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _, _} = pattern_to_type(unquote(Macro.escape(left)))
          assert {:ok, _, _} = pattern_to_type(unquote(Macro.escape(right)))
        end
    end
  end

  describe "union/2" do
    test "unions base types" do
      assert quoted_union(x :: integer(), x :: atom()) ==
             [:atom, :integer]

      assert quoted_union(1, 2) ==
             [{:value, 1}, {:value, 2}]

      assert quoted_union(1, x :: integer()) ==
             [:integer]

      assert quoted_union(x :: integer(), 1) ==
             [:integer]

      assert quoted_union(x :: integer(), :foo) ==
             [:integer, {:value, :foo}]
    end

    test "unions tuples" do
      assert quoted_union({}, {1}) ==
             [{:tuple, [], 0}, {:tuple, [[{:value, 1}]], 1}]

      assert quoted_union({:ok, x :: integer()}, {:ok, 1}) ==
             [{:tuple, [[{:value, :ok}], [:integer]], 2}]

      assert quoted_union({:ok, x :: integer()}, {:ok, x :: integer()}) ==
             [{:tuple, [[{:value, :ok}], [:integer]], 2}]

      assert quoted_union({:ok, x :: integer(), y :: atom()}, {:ok, 1, z :: atom()}) ==
             [{:tuple, [[{:value, :ok}], [:integer], [:atom]], 3}]

      assert quoted_union({:ok, x :: integer()}, {:error, 1}) ==
             [{:tuple, [[{:value, :error}], [{:value, 1}]], 2},
              {:tuple, [[{:value, :ok}], [:integer]], 2}]
    end
  end

  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  defp types({:ok, types, _}), do: types

  describe "of/1" do
    test "integers" do
      assert quoted_of(1) |> types() == [{:value, 1}]
      assert quoted_of(2) |> types() == [{:value, 2}]
    end

    test "atoms" do
      assert quoted_of(nil) |> types() == [{:value, nil}]
      assert quoted_of(:foo) |> types() == [{:value, :foo}]
      assert quoted_of(true) |> types() == [{:value, true}]
      assert quoted_of(false) |> types() == [{:value, false}]
    end

    test "patterns" do
      assert quoted_of(fn {x :: integer(), x :: integer()} -> x end) |> types() ==
             [{:fn, [
               {[[{:tuple, [[:integer], [:integer]], 2}]], [:integer]}
             ], 1}]

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x :: integer(), x :: boolean()} -> x end)
    end

    test "functions" do
      assert quoted_of(fn bool :: boolean() -> bool end) |> types() ==
             [{:fn, [
               {[[{:value, true}, {:value, false}]], [{:value, true}, {:value, false}]}
             ], 1}]

      assert quoted_of(fn false -> true; true -> false end) |> types() ==
             [{:fn, [
               {[[{:value, false}]], [{:value, true}]},
               {[[{:value, true}]], [{:value, false}]}
             ], 1}]

      assert {:error, _, {:invalid_fn, _, 1}} =
             quoted_of(fn true -> (true).(true) end)
    end

    test "functions with holes" do
      assert quoted_of(fn x -> x end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]], [{:var, {:x, nil}, 0}]}
             ], 1}]

      assert quoted_of(fn x -> fn y -> y end end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]],
                [{:fn, [
                  {[[{:var, {:y, nil}, 1}]], [{:var, {:y, nil}, 1}]}
                ], 1}]}
             ], 1}]

      assert quoted_of(fn x -> fn y -> x end end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]],
                [{:fn, [
                  {[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 0}]}
                ], 1}]}
             ], 1}]
    end

    test "function calls" do
      assert quoted_of((fn false -> true; true -> false end).(false)) |> types() ==
             [{:value, true}]

      assert quoted_of((fn false -> true; true -> false end).(true)) |> types() ==
             [{:value, false}]

      assert {:error, _, {:invalid_fn, _, 1}} =
             quoted_of((true).(true))
    end

    test "function calls with holes" do
      assert quoted_of((fn x -> x end).(true)) |> types() ==
             [{:value, true}]

      assert quoted_of(fn a -> (fn true -> true end).(a) end) |> types() ==
             [{:fn, [{[[{:value, true}]], [{:value, true}]}], 1}]
    end

    test "tuples with vars" do
      assert {:ok,
              [{:tuple, [[{:value, 1}], [{:value, 2}]], 2}],
              %{vars: %{{:a, nil} => [{:value, 2}]}}} =
             quoted_of({a = 1, a = 2})
    end

    test "blocks with vars" do
      assert {:ok,
              [{:value, false}],
              %{vars: %{{:a, nil} => [{:value, 2}]}}} =
             quoted_of((true; a = 2; false))
    end
  end
end
