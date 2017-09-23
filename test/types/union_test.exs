defmodule Types.UnionTest do
  use ExUnit.Case, async: true

  import Types.Union

  defmacro ast_to_union_to_string(ast) do
    quote do
      {:ok, value} = from_ast(unquote(Macro.escape(ast)))
      value |> to_iodata() |> IO.iodata_to_binary()
    end
  end

  describe "pretty printing" do
    test "basic types" do
      assert ast_to_union_to_string(integer() | atom()) ==
             "atom() | integer()"

      assert ast_to_union_to_string(:bar | :foo) ==
             ":bar | :foo"
    end
  end

  defmacro quoted_merge(left, right) do
    with {:ok, left} <- from_ast(left),
         {:ok, right} <- from_ast(right) do
      quote do
        merge(unquote(Macro.escape(left)),
              unquote(Macro.escape(right))) |> to_iodata() |> IO.iodata_to_binary()
      end
    else
      _ ->
        quote do
          assert {:ok, _} = from_ast(unquote(Macro.escape(left)))
          assert {:ok, _} = from_ast(unquote(Macro.escape(right)))
        end
    end
  end

  describe "merge" do
    test "merges basic types" do
      assert quoted_merge(integer(), atom()) == "atom() | integer()"
      assert quoted_merge(atom(), integer()) == "atom() | integer()"
      assert quoted_merge(integer(), integer()) == "integer()"
    end

    test "merges atoms" do
      assert quoted_merge(atom(), :foo | :bar) == "atom()"
      assert quoted_merge(:foo | :bar, atom()) == "atom()"
    end
  end
end
