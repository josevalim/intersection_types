defmodule TypesTest do
  use ExUnit.Case, async: true

  defp types({:ok, types, %{inferred: inferred}}) do
    Types.bind(types, inferred, :eager)
  end

  defmacro quoted_ast_to_type(ast) do
    quote do
      Types.ast_to_type(unquote(Macro.escape(ast)))
    end
  end

  describe "ast_to_type/1" do
    test "built-ins" do
      assert quoted_ast_to_type(boolean()) |> types() ==
             [{:value, true}, {:value, false}]
    end

    test "base types" do
      assert quoted_ast_to_type(atom()) |> types() ==
             [:atom]
      assert quoted_ast_to_type(integer()) |> types() ==
             [:integer]
    end

    test "values" do
      assert quoted_ast_to_type(:foo) |> types() ==
             [{:value, :foo}]
      assert quoted_ast_to_type(true) |> types() ==
             [{:value, true}]
      assert quoted_ast_to_type(false) |> types() ==
             [{:value, false}]
    end

    test "literals" do
      assert quoted_ast_to_type(1) |> types() == [:integer]
    end

    test "tuples" do
      assert quoted_ast_to_type({}) |> types() ==
             [{:tuple, [], 0}]
      assert quoted_ast_to_type({:ok, atom()}) |> types() ==
             [{:tuple, [[{:value, :ok}], [:atom]], 2}]
    end
  end


  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  describe "of/1" do
    test "atoms" do
      assert quoted_of(nil) |> types() == [{:value, nil}]
      assert quoted_of(:foo) |> types() == [{:value, :foo}]
      assert quoted_of(true) |> types() == [{:value, true}]
      assert quoted_of(false) |> types() == [{:value, false}]
    end

    test "apply" do
      assert quoted_of((fn false -> true; true -> false end).(false)) |> types() ==
             [{:value, true}]

      assert quoted_of((fn false -> true; true -> false end).(true)) |> types() ==
             [{:value, false}]

      assert {:error, _, {:disjoint_fn, _}} =
             quoted_of(fn x :: boolean() ->
               (fn true -> true end).(x)
             end)
    end

    test "apply with inference" do
      assert quoted_of((fn x -> x end).(true)) |> types() ==
             [{:value, true}]
    end

    test "match" do
      assert {:error, _, {:disjoint_match, _}} =
               quoted_of({:ok, a :: atom()} = {:ok, 0})
    end

    test "tuples" do
      assert quoted_of({:ok, :error}) |> types() ==
             [{:tuple, [[{:value, :ok}], [{:value, :error}]], 2}]
    end
  end

  describe "of/1 with variable tracking" do
    test "tuples" do
      assert quoted_of(({x = :ok, y = :error}; y)) |> types() ==
             [{:value, :error}]
    end

    test "blocks" do
      assert quoted_of((a = :ok; b = a; b)) |> types() ==
             [{:value, :ok}]
    end

    test "pattern matching" do
      assert quoted_of((a = (a = true; b = false); a)) |> types() ==
             [{:value, false}]
    end
  end

  describe "of/1 fns" do
    test "patterns" do
      assert quoted_of(fn x -> x end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]], [{:var, {:x, nil}, 0}], %{}}
             ], 1}]

      assert quoted_of(fn {x :: integer(), x} -> x end) |> types() ==
             [{:fn, [
               {[[{:tuple, [[:integer], [:integer]], 2}]], [:integer], %{}}
             ], 1}]

      assert quoted_of(fn {x :: integer(), x :: integer()} -> x end) |> types() ==
             [{:fn, [
               {[[{:tuple, [[:integer], [:integer]], 2}]], [:integer], %{}}
             ], 1}]

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x, x :: boolean()} -> x end)

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x :: integer(), x :: boolean()} -> x end)
    end

    test "late propagation" do
      assert quoted_of(fn x ->
        z = x
        (fn 0 -> 0 end).(x) # TODO: This should emit a warning in the future.
        z
      end) |> types() == [{:fn, [{[[:integer]], [:integer], %{}}], 1}]
    end

    test "bidirectional matching" do
      assert quoted_of(fn z ->
        {:ok, x} = (fn y -> {y, :error} end).(z)
        {z, x}
      end) |> types() ==
        [{:fn, [
          {[[value: :ok]], [{:tuple, [[value: :ok], [value: :error]], 2}], %{}}
        ], 1}]
    end

    test "bidirectional matching with multiple clauses" do
      assert quoted_of(fn z ->
        {x, y} = (fn true -> {true, :foo}; false -> {false, :bar} end).(z)
        {y, x}
      end) |> types() ==
        [{:fn, [
          {[[value: false, value: true]],
           [{:tuple, [[value: :foo, value: :bar], [value: true, value: false]], 2}
        ], %{}}], 1}]
    end

    test "free variables" do
      assert quoted_of(fn x -> x end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]], [{:var, {:x, nil}, 0}], %{}}
             ], 1}]

      assert quoted_of(fn x -> fn y -> y end end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]],
                [{:fn, [
                  {[[{:var, {:y, nil}, 1}]], [{:var, {:y, nil}, 1}], %{}}
                ], 1}], %{}}
             ], 1}]

      assert quoted_of(fn x -> fn y -> x end end) |> types() ==
             [{:fn, [
               {[[{:var, {:x, nil}, 0}]],
                [{:fn, [
                  {[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 0}], %{}}
                ], 1}], %{}}
             ], 1}]
    end
  end

  # end

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

  # defmacro quoted_union(left, right) do
  #   with {:ok, left, _} <- pattern_to_type(left),
  #        {:ok, right, _} <- pattern_to_type(right) do
  #     quote do
  #       union(unquote(Macro.escape(left)), unquote(Macro.escape(right))) |> Enum.sort()
  #     end
  #   else
  #     _ ->
  #       quote do
  #         assert {:ok, _, _} = pattern_to_type(unquote(Macro.escape(left)))
  #         assert {:ok, _, _} = pattern_to_type(unquote(Macro.escape(right)))
  #       end
  #   end
  # end

  # describe "union/2" do
  #   test "unions base types" do
  #     assert quoted_union(x :: integer(), x :: atom()) ==
  #            [:atom, :integer]

  #     assert quoted_union(1, 2) ==
  #            [{:value, 1}, {:value, 2}]

  #     assert quoted_union(1, x :: integer()) ==
  #            [:integer]

  #     assert quoted_union(x :: integer(), 1) ==
  #            [:integer]

  #     assert quoted_union(x :: integer(), :foo) ==
  #            [:integer, {:value, :foo}]
  #   end

  #   test "unions tuples" do
  #     assert quoted_union({}, {1}) ==
  #            [{:tuple, [], 0}, {:tuple, [[{:value, 1}]], 1}]

  #     assert quoted_union({:ok, x :: integer()}, {:ok, 1}) ==
  #            [{:tuple, [[{:value, :ok}], [:integer]], 2}]

  #     assert quoted_union({:ok, x :: integer()}, {:ok, x :: integer()}) ==
  #            [{:tuple, [[{:value, :ok}], [:integer]], 2}]

  #     assert quoted_union({:ok, x :: integer(), y :: atom()}, {:ok, 1, z :: atom()}) ==
  #            [{:tuple, [[{:value, :ok}], [:integer], [:atom]], 3}]

  #     assert quoted_union({:ok, x :: integer()}, {:error, 1}) ==
  #            [{:tuple, [[{:value, :error}], [{:value, 1}]], 2},
  #             {:tuple, [[{:value, :ok}], [:integer]], 2}]
  #   end
  # end

end
