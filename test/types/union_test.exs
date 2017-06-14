defmodule Types.UnionTest do
  use ExUnit.Case, async: true

  import Types.Union

  doctest Types.Union

  defmacro quoted_union(left, right) do
    with {:ok, left} <- ast_to_types(left),
         {:ok, right} <- ast_to_types(right) do
      quote do
        union(unquote(Macro.escape(left)),
              unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _} = ast_to_types(unquote(Macro.escape(left)))
          assert {:ok, _} = ast_to_types(unquote(Macro.escape(right)))
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

      assert quoted_union(atom(), boolean()) ==
             [:atom]

      assert quoted_union(boolean(), atom()) ==
             [:atom]

      assert quoted_union(atom() | integer(), boolean()) ==
             [:atom, :integer]

      assert quoted_union(boolean(), atom() | integer()) ==
             [:atom, :integer]

      assert quoted_union(integer(), :foo) ==
             [:integer, {:atom, :foo}]
    end

    test "vars" do
      assert union([{:var, {:x, nil}, 0}], [{:var, {:x, nil}, 0}]) == [{:var, {:x, nil}, 0}]
    end

    test "tuples" do
      assert quoted_union({}, {:foo}) ==
             [{:tuple, [], 0}, {:tuple, [atom: :foo], 1}]

      assert quoted_union({:ok, atom()}, {:ok, :foo}) ==
             [{:tuple, [{:atom, :ok}, :atom], 2}]

      assert quoted_union({:ok, atom()}, {:ok, atom()}) ==
             [{:tuple, [{:atom, :ok}, :atom], 2}]

      assert quoted_union({boolean(), boolean()}, {boolean(), boolean()}) ==
             [{:tuple, [atom: false, atom: false], 2},
              {:tuple, [atom: false, atom: true], 2},
              {:tuple, [atom: true, atom: false], 2},
              {:tuple, [atom: true, atom: true], 2}]

      assert quoted_union({:foo, :bar}, {atom(), atom()}) ==
             [{:tuple, [:atom, :atom], 2}]

      assert quoted_union({:ok, integer()}, {:error, integer()}) ==
             [{:tuple, [{:atom, :error}, :integer], 2},
              {:tuple, [{:atom, :ok}, :integer], 2}]

      assert quoted_union({atom() | integer(), atom()}, {:foo, :bar}) ==
             [{:tuple, [:atom, :atom], 2},
              {:tuple, [:integer, :atom], 2}]
    end
  end

  defmacro quoted_ast_to_types(ast) do
    quote do
      ast_to_types(unquote(Macro.escape(ast)))
    end
  end

  describe "ast_to_types/1" do
    test "built-ins" do
      assert quoted_ast_to_types(boolean()) |> elem(1) ==
             [{:atom, true}, {:atom, false}]
    end

    test "base types" do
      assert quoted_ast_to_types(atom()) |> elem(1) ==
             [:atom]
      assert quoted_ast_to_types(integer()) |> elem(1) ==
             [:integer]
    end

    test "atoms" do
      assert quoted_ast_to_types(:foo) |> elem(1) ==
             [{:atom, :foo}]
      assert quoted_ast_to_types(true) |> elem(1) ==
             [{:atom, true}]
      assert quoted_ast_to_types(false) |> elem(1) ==
             [{:atom, false}]
    end

    test "tuples" do
      assert quoted_ast_to_types({}) |> elem(1) ==
             [{:tuple, [], 0}]
      assert quoted_ast_to_types({:ok, atom()}) |> elem(1) ==
             [{:tuple, [{:atom, :ok}, :atom], 2}]
      assert quoted_ast_to_types({:a | :b, :one | :two}) |> elem(1) ==
             [{:tuple, [atom: :b, atom: :two], 2},
              {:tuple, [atom: :b, atom: :one], 2},
              {:tuple, [atom: :a, atom: :two], 2},
              {:tuple, [atom: :a, atom: :one], 2}]
      assert quoted_ast_to_types({boolean(), boolean()}) |> elem(1) ==
             [{:tuple, [atom: false, atom: false], 2},
              {:tuple, [atom: false, atom: true], 2},
              {:tuple, [atom: true, atom: false], 2},
              {:tuple, [atom: true, atom: true], 2}]
    end

    test "empty_list and cons" do
      assert quoted_ast_to_types(empty_list()) |> elem(1) ==
             [:empty_list]

      assert quoted_ast_to_types(cons(atom(), integer())) |> elem(1) ==
             [{:cons, :atom, :integer}]

      assert quoted_ast_to_types(cons(boolean(), boolean())) |> elem(1) ==
             [{:cons, {:atom, false}, {:atom, false}},
              {:cons, {:atom, false}, {:atom, true}},
              {:cons, {:atom, true}, {:atom, false}},
              {:cons, {:atom, true}, {:atom, true}}]
    end
  end

  describe "simplify/1" do
    test "merge aliases" do
      assert simplify([{:atom, false}, {:atom, true}]) == {:union, [:boolean]}
      assert simplify([{:atom, nil}, {:atom, true}]) == {:union, [{:atom, true}, {:atom, nil}]}
      assert simplify([{:atom, false}, {:atom, true}, :integer]) == {:union, [:boolean, :integer]}
    end

    test "undistribute" do
      assert simplify([{:tuple, [:atom], 1}, {:tuple, [:integer], 1}]) ==
             {:union, [{:tuple, [{:union, [:atom, :integer]}], 1}]}

      assert simplify([{:tuple, [:atom, :integer], 2}, {:tuple, [:integer, :atom], 2}]) ==
             {:union, [{:tuple, [:integer, :atom], 2}, {:tuple, [:atom, :integer], 2}]}

      assert simplify([{:cons, :integer, :atom}, {:cons, :integer, :integer}]) ==
             {:union, [{:cons,  {:union, [:integer]}, {:union, [:atom, :integer]}}]}

      assert simplify([{:cons, :integer, :atom}, {:cons, :atom, :integer}]) ==
             {:union, [{:cons, :atom, :integer}, {:cons, :integer, :atom}]}
    end

    test "traverse" do
      assert simplify([{:cons, :atom, {:atom, false}}, {:cons, :atom, {:atom, true}}]) ==
                      {:union, [{:cons, {:union, [:atom]}, {:union, [:boolean]}}]}

      assert simplify([{:tuple, [{:tuple, [{:atom, :foo}], 1}], 1},
                       {:tuple, [{:tuple, [{:atom, :bar}], 1}], 1},
                       {:tuple, [{:tuple, [{:atom, :baz}], 1}], 1}]) ==
             {:union, [{:tuple, [{:union, [{:tuple, [{:union, [{:atom, :foo}, {:atom, :baz}, {:atom, :bar}]}], 1}]}], 1}]}

      assert simplify([{:fn, [{[[{:atom, false}, {:atom, true}]], [:atom]}], [], 1}]) ==
             {:union, [{:fn, [{[[{:union, [:boolean]}]], [{:union, [:atom]}]}], [], 1}]}

      assert simplify([{:fn, [{[[{:tuple, [:atom], 1}, {:tuple, [:integer], 1}]], [:atom]}], [], 1}]) ==
             {:union, [{:fn, [{[[{:union, [{:tuple, [{:union, [:atom, :integer]}], 1}]}]], [{:union, [:atom]}]}], [], 1}]}
    end
  end
end
