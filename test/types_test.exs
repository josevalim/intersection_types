defmodule TypesTest do
  use ExUnit.Case, async: true

  defp types({:ok, types, %{inferred: inferred}}) do
    Types.bind(types, inferred)
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

  defmacro quoted_union(left, right) do
    with {:ok, left, _} <- Types.ast_to_type(left),
         {:ok, right, _} <- Types.ast_to_type(right) do
      quote do
        Types.union(unquote(Macro.escape(left)),
                    unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _, _} = Types.ast_to_type(unquote(Macro.escape(left)))
          assert {:ok, _, _} = Types.ast_to_type(unquote(Macro.escape(right)))
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
      assert Types.union([{:tuple, [[:atom, :integer], [:atom]], 2}],
                         [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[:atom, :integer], [:atom]], 2}]

      assert Types.union([{:tuple, [[:atom, :integer], [:atom]], 2}],
                         [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[:atom, :integer], [:atom]], 2}]
    end
  end

  defmacro quoted_intersection(left, right) do
    with {:ok, left, _} <- Types.ast_to_type(left),
         {:ok, right, _} <- Types.ast_to_type(right) do
      quote do
        Types.intersection(unquote(Macro.escape(left)),
                           unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _, _} = Types.ast_to_type(unquote(Macro.escape(left)))
          assert {:ok, _, _} = Types.ast_to_type(unquote(Macro.escape(right)))
        end
    end
  end

  describe "intersection/2" do
    test "base types" do
      assert quoted_intersection(integer(), atom()) ==
             []

      assert quoted_intersection(:foo, atom()) ==
             [{:value, :foo}]

      assert quoted_intersection(atom(), :foo) ==
             [{:value, :foo}]
    end

    test "tuples" do
      assert quoted_intersection({}, {:foo}) ==
             []

      assert quoted_intersection({:ok, atom()}, {:ok, :foo}) ==
             [{:tuple, [[{:value, :ok}], [{:value, :foo}]], 2}]

      assert quoted_intersection({:ok, atom()}, {:ok, atom()}) ==
             [{:tuple, [[{:value, :ok}], [:atom]], 2}]

      assert quoted_intersection({boolean(), boolean()}, {boolean(), boolean()}) ==
             [{:tuple, [[{:value, true}, {:value, false}], [{:value, true}, {:value, false}]], 2}]

      assert quoted_intersection({:foo, :bar}, {atom(), atom()}) ==
             [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]

      assert quoted_intersection({:ok, integer()}, {:error, 1}) ==
             []

      # TODO: Write using quoted_intersection once we have |
      assert Types.intersection([{:tuple, [[:atom, :integer], [:atom]], 2}],
                                [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]

      assert Types.intersection([{:tuple, [[:atom, :integer], [:atom]], 2}],
                                [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]) ==
             [{:tuple, [[{:value, :foo}], [{:value, :bar}]], 2}]
    end
  end

  describe "unify/4" do
    test "either" do
      # This pattern requires different types across left and right.
      pattern = [{:tuple, [[{:value, :left}], [{:var, {:x, nil}, 0}]], 2},
                 {:tuple, [[{:value, :right}], [{:var, {:y, nil}, 1}]], 2}]

      left  = {:tuple, [[{:value, :left}], [:atom]], 2}
      right = {:tuple, [[{:value, :right}], [:integer]], 2}

      assert Types.unify(pattern, [left, right], %{}, %{}) ==
             {%{0 => [:atom], 1 => [:integer]}, %{}, %{}, [right, left], []}

      assert Types.unify(pattern, [left, right, :atom], %{}, %{}) ==
             {%{0 => [:atom], 1 => [:integer]}, %{}, %{}, [right, left], [:atom]}

      # This pattern requires the same type across left and right.
      pattern = [{:tuple, [[{:value, :left}], [{:var, {:x, nil}, 0}]], 2},
                 {:tuple, [[{:value, :right}], [{:var, {:x, nil}, 0}]], 2}]

      assert Types.unify(pattern, [left, right], %{}, %{}) ==
             {%{0 => [:atom]}, %{}, %{}, [left], [right]}
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

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn x :: boolean() ->
               (fn true -> true end).(x)
             end)
    end

    test "apply with inference" do
      assert quoted_of(fn x ->
        (fn true -> true end).(x)
        (fn z ->
          (fn true -> true end).(z)
          z
        end).(x)
      end) |> types() ==
        [{:fn, [
          {[[value: true]], [value: true]}
        ], 1}]

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
        (fn z ->
          (fn true -> true end).(z)
          z
        end).(x)
      end) |> types() ==
        [{:fn, [
          {[[value: true]], [value: true]}
        ], 1}]

      assert {:error, _, {:disjoint_match, _, _}} =
        quoted_of(fn x ->
          false = (fn y :: boolean() -> y end).(x)
          (fn z ->
            (fn true -> true end).(z)
            z
          end).(x)
        end)

      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of(fn x ->
          (fn y :: integer() -> y end).(x)
          (fn z ->
            (fn true -> true end).(z)
            z
          end).(x)
        end)
    end

    test "apply with inference and free variables" do
      assert quoted_of(fn x ->
        (fn y -> y end).(x)
      end) |> types() ==
        [{:fn, [
          {[[{:var, {:x, nil}, 0}]], [{:var, {:x, nil}, 0}]}
        ], 1}]

      assert quoted_of(fn x ->
        (fn false -> false; nil -> nil; _ -> true end).(x)
      end) |> types() ==
        [{:fn, [
          {[[{:var, {:x, nil}, 0}]], [{:value, true}, {:value, nil}, {:value, false}]}
        ], 1}]

      assert quoted_of(fn x ->
        a = (fn false -> false; nil -> nil; _ -> true end).(x)
        b = (fn y -> y end).(x)
        c = x
        {a, b, c}
      end) |> types() ==
        [{:fn, [
          {[[{:var, {:x, nil}, 0}]],
           [{:tuple, [[value: false, value: nil, value: true], [{:var, {:x, nil}, 0}], [{:var, {:x, nil}, 0}]], 3}]}
        ], 1}]

      assert quoted_of(fn x ->
        a = (fn true -> false; y -> y end).(x)
        b = (fn z -> z end).(x)
        c = x
        {a, b, c}
      end) |> types() ==
        [{:fn, [
          {[[{:var, {:x, nil}, 0}]],
           [{:tuple, [[{:value, false}, {:var, {:x, nil}, 0}], [{:var, {:x, nil}, 0}], [{:var, {:x, nil}, 0}]], 3}]}
        ], 1}]

      assert quoted_of(fn x ->
        a = (fn true -> false; y -> y end).(x)
        b = (fn false -> false end).(x)
        c = x
        {a, b, c}
      end) |> types() ==
        [{:fn, [
          {[[{:value, false}]],
           [{:tuple, [[{:value, false}], [{:value, false}], [{:value, false}]], 3}]}
        ], 1}]
    end

    test "apply with closure" do
      assert quoted_of((fn x -> (fn y -> x end) end).(true)) |> types() ==
             [{:fn, [{[[{:var, {:y, nil}, 1}]], [value: true]}], 1}]

      assert quoted_of((fn x -> (fn y -> x end) end).(true).(:foo)) |> types() ==
             [{:value, true}]
    end

    # TODO: Make below work with rank-2 intersection types
    test "apply on variable" do
      assert {:error, _, {:invalid_fn, _, _}} =
        quoted_of((
          x = fn y -> y end
          x.(:foo)
        ))

      assert {:error, _, {:invalid_fn, _, _}} =
        quoted_of((
          x = fn y -> y end
          {x.(:foo), x.(:foo)}
        ))

      assert {:error, _, {:invalid_fn, _, _}} =
        quoted_of((
          x = fn y -> y end
          {x.(:foo), x.(:bar)}
        ))
    end

    test "match" do
      assert {:error, _, {:disjoint_match, _, _}} =
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
               {[[{:var, {:x, nil}, 0}]], [{:var, {:x, nil}, 0}]}
             ], 1}]

      assert quoted_of(fn {x :: integer(), x} -> x end) |> types() ==
             [{:fn, [
               {[[{:tuple, [[:integer], [:integer]], 2}]], [:integer]}
             ], 1}]

      assert quoted_of(fn {x :: integer(), x :: integer()} -> x end) |> types() ==
             [{:fn, [
               {[[{:tuple, [[:integer], [:integer]], 2}]], [:integer]}
             ], 1}]

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x, x :: boolean()} -> x end)

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x :: integer(), x :: boolean()} -> x end)
    end

    test "late propagation" do
      assert quoted_of(fn x ->
        z = x
        (fn 0 -> 0 end).(x) # TODO: This should emit a warning for being non-exaustive.
        z
      end) |> types() == [{:fn, [{[[:integer]], [:integer]}], 1}]
    end

    test "bidirectional matching" do
      assert quoted_of(fn z ->
        {:ok, x} = (fn y -> {y, :error} end).(z)
        {z, x}
      end) |> types() ==
        [{:fn, [
          {[[value: :ok]], [{:tuple, [[value: :ok], [value: :error]], 2}]}
        ], 1}]

      assert quoted_of(fn z ->
        {:ok, x} = (fn y -> {y, :error} end).(z)
      end) |> types() ==
        [{:fn, [
          {[[value: :ok]], [{:tuple, [[value: :ok], [value: :error]], 2}]}
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
        ]}], 1}]
    end

    test "free variables" do
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
  end
end
