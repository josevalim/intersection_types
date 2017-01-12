defmodule Types.UnionTest do
  use ExUnit.Case, async: true

  import Types.Union

  defmacro quoted_union(left, right) do
    with {:ok, left, _} <- Types.Checker.ast_to_types(left),
         {:ok, right, _} <- Types.Checker.ast_to_types(right) do
      quote do
        union(unquote(Macro.escape(left)),
              unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _, _} = Types.Checker.ast_to_types(unquote(Macro.escape(left)))
          assert {:ok, _, _} = Types.Checker.ast_to_types(unquote(Macro.escape(right)))
        end
    end
  end

  describe "union/2" do
    test "base types" do
      assert quoted_union(integer(), atom()) ==
             [:atom, :integer]

      assert quoted_union(:foo, atom()) ==
             [:atom]

      assert quoted_union(atom(), :foo) ==
             [:atom]

      assert quoted_union(integer(), :foo) ==
             [:integer, {:value, :foo}]
    end

    test "tuples" do
      assert quoted_union({}, {:foo}) ==
             [{:tuple, [], 0}, {:tuple, [[{:value, :foo}]], 1}]

      assert quoted_union({:ok, atom()}, {:ok, :foo}) ==
             [{:tuple, [[{:value, :ok}], [:atom]], 2}]

      assert quoted_union({:ok, atom()}, {:ok, atom()}) ==
             [{:tuple, [[{:value, :ok}], [:atom]], 2}]

      assert quoted_union({boolean(), boolean()}, {boolean(), boolean()}) ==
             [{:tuple, [[{:value, true}, {:value, false}], [{:value, true}, {:value, false}]], 2}]

      assert quoted_union({:foo, :bar}, {atom(), atom()}) ==
             [{:tuple, [[:atom], [:atom]], 2}]

      assert quoted_union({:ok, integer()}, {:error, 1}) ==
             [{:tuple, [[{:value, :error}], [:integer]], 2},
              {:tuple, [[{:value, :ok}], [:integer]], 2}]

      # TODO: Write using quoted_union once we have |
      assert union([{:tuple, [[:atom, :integer], [:atom]], 2}],
                   [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[:atom, :integer], [:atom]], 2}]

      assert union([{:tuple, [[:atom, :integer], [:atom]], 2}],
                   [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[:atom, :integer], [:atom]], 2}]
    end
  end
end
