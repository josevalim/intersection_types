defmodule TypesTest do
  use ExUnit.Case, async: true

  defp types({:ok, types, %{inferred: inferred}}) do
    types
    |> Types.bind(inferred, %{})
    |> elem(0)
  end

  defp format({:ok, types, %{inferred: inferred}}) do
    types
    |> Types.bind(inferred, %{})
    |> elem(0)
    |> Types.types_to_algebra()
    |> Inspect.Algebra.format(:infinity)
    |> IO.iodata_to_binary()
  end

  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  defmacro quoted_ast_to_types(ast) do
    quote do
      Types.ast_to_types(unquote(Macro.escape(ast)))
    end
  end

  describe "ast_to_types/1" do
    test "built-ins" do
      assert quoted_ast_to_types(boolean()) |> types() ==
             [{:value, true}, {:value, false}]
    end

    test "base types" do
      assert quoted_ast_to_types(atom()) |> types() ==
             [:atom]
      assert quoted_ast_to_types(integer()) |> types() ==
             [:integer]
    end

    test "values" do
      assert quoted_ast_to_types(:foo) |> types() ==
             [{:value, :foo}]
      assert quoted_ast_to_types(true) |> types() ==
             [{:value, true}]
      assert quoted_ast_to_types(false) |> types() ==
             [{:value, false}]
    end

    test "literals" do
      assert quoted_ast_to_types(1) |> types() == [:integer]
    end

    test "tuples" do
      assert quoted_ast_to_types({}) |> types() ==
             [{:tuple, [], 0}]
      assert quoted_ast_to_types({:ok, atom()}) |> types() ==
             [{:tuple, [[{:value, :ok}], [:atom]], 2}]
    end
  end

  defmacro quoted_union(left, right) do
    with {:ok, left, _} <- Types.ast_to_types(left),
         {:ok, right, _} <- Types.ast_to_types(right) do
      quote do
        Types.union(unquote(Macro.escape(left)),
                    unquote(Macro.escape(right))) |> Enum.sort()
      end
    else
      _ ->
        quote do
          assert {:ok, _, _} = Types.ast_to_types(unquote(Macro.escape(left)))
          assert {:ok, _, _} = Types.ast_to_types(unquote(Macro.escape(right)))
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

  # TODO: Rewrite those using unions.
  # test "fns" do
  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn x -> x end, fn y -> y end}) |> types()
  #   assert Types.intersection(left, right) == {left, [], []}

  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn :foo -> :foo end, fn y :: atom() -> y end}) |> types()
  #   assert Types.intersection(left, right) == {left, [], []}

  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn y :: atom() -> y end, fn :foo -> :foo end}) |> types()
  #   assert Types.intersection(left, right) == {right, right, left}

  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn :foo -> :foo; :bar -> :bar end, fn y :: atom() -> y end}) |> types()
  #   assert Types.intersection(left, right) == {left, [], []}

  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn y :: atom() -> y end, fn :foo -> :foo; :bar -> :bar end}) |> types()
  #   assert Types.intersection(left, right) == {right, right, left}

  #   [{:tuple, [left, right], _}] =
  #     quoted_of({fn x :: integer() -> x end, fn y :: atom() -> y end}) |> types()
  #   assert Types.intersection(left, right) == {[], [], left}
  # end

  describe "unify/5" do
    test "unions" do
      assert Types.unify([{:var, {:x, Elixir}, 0}], [:atom, :integer], [], %{}, %{}) ==
             {:match, [:atom, :integer], %{0 => [:atom, :integer]}, %{0 => [:atom, :integer]}}

      assert Types.unify([:atom, :integer], [{:var, {:x, Elixir}, 0}], [], %{}, %{}) ==
             {:match, [{:var, {:x, Elixir}, 0}], %{0 => [:atom, :integer]}, %{0 => [:atom, :integer]}}
    end

    test "tuple root unions" do
      assert Types.unify([{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
                         [{:tuple, [[:atom]], 1}, {:tuple, [[:integer]], 1}],
                         [], %{}, %{}) ==
             {:match,
              [{:tuple, [[:atom]], 1}, {:tuple, [[:integer]], 1}],
              %{0 => [:atom, :integer]},
              %{0 => [:atom, :integer]}}

      assert Types.unify([{:tuple, [[:atom]], 1}, {:tuple, [[:integer]], 1}],
                         [{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
                         [], %{}, %{}) ==
             {:match,
              [{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
              %{0 => [:atom, :integer]},
              %{0 => [:atom, :integer]}}
    end

    test "tuple args unions" do
      assert Types.unify([{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
                         [{:tuple, [[:atom, :integer]], 1}],
                         [], %{}, %{}) ==
             {:match,
              [{:tuple, [[:atom, :integer]], 1}],
              %{0 => [:atom, :integer]},
              %{0 => [:atom, :integer]}}

      assert Types.unify([{:tuple, [[:atom, :integer]], 1}],
                         [{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
                         [], %{}, %{}) ==
             {:match,
              [{:tuple, [[{:var, {:x, Elixir}, 0}]], 1}],
              %{0 => [:atom, :integer]},
              %{0 => [:atom, :integer]}}
    end

    test "either" do
      # This pattern accepts different types across left and right.
      pattern = [{:tuple, [[{:value, :left}], [{:var, {:x, nil}, 0}]], 2},
                 {:tuple, [[{:value, :right}], [{:var, {:y, nil}, 1}]], 2}]

      left  = {:tuple, [[{:value, :left}], [:atom]], 2}
      right = {:tuple, [[{:value, :right}], [:integer]], 2}

      assert Types.unify(pattern, [left, right], [0, 1], %{}, %{}) ==
             {:match, [left, right], %{0 => [:atom], 1 => [:integer]}, %{0 => [:atom], 1 => [:integer]}}

      assert Types.unify(pattern, [left, right, :atom], [0, 1], %{}, %{}) ==
             {:disjoint, [left, right], %{0 => [:atom], 1 => [:integer]}, %{0 => [:atom], 1 => [:integer]}}

      # This pattern requires the same type across left and right.
      pattern = [{:tuple, [[{:value, :left}], [{:var, {:x, nil}, 0}]], 2},
                 {:tuple, [[{:value, :right}], [{:var, {:x, nil}, 0}]], 2}]

      assert Types.unify(pattern, [left, right], [0, 1], %{}, %{}) ==
             {:disjoint, [left], %{0 => [:atom]}, %{0 => [:atom]}}
    end
  end

  describe "of/1" do
    test "atoms" do
      assert quoted_of(nil) |> format() == "nil"
      assert quoted_of(:foo) |> format() == ":foo"
      assert quoted_of(true) |> format() == "true"
      assert quoted_of(false) |> format() == "false"
    end

    test "tuples" do
      assert quoted_of({:ok, :error}) |> format() == "{:ok, :error}"
    end

    test "match" do
      assert {:error, _, {:disjoint_match, _, _}} =
               quoted_of({:ok, a :: atom()} = {:ok, 0})
    end

    test "apply" do
      assert quoted_of((fn false -> true; true -> false end).(false)) |> format() ==
             "true"

      assert quoted_of((fn false -> true; true -> false end).(true)) |> format() ==
             "false"

      assert quoted_of((fn y :: atom() -> y end).(:foo)) |> format() ==
             ":foo"

      assert quoted_of((fn :foo -> :bar; y :: atom() -> :baz end).(:foo)) |> format() ==
             ":bar"

      # TODO: This should fail to compile or emit a warning
      assert quoted_of(fn x :: boolean() -> (fn true -> true end).(x) end) |> format() ==
             "(true -> true)"
    end

    test "apply with inference" do
      assert quoted_of(fn x -> (fn y -> y end).(x) end) |> format() ==
             "(a -> a)"

      assert quoted_of((fn y -> y end).(fn x -> x end)) |> format() ==
             "(a -> a)"

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
      end) |> format() == "(a -> a) when a: true | false"

      assert quoted_of(fn x :: boolean() ->
        (fn y -> y end).(x)
      end) |> format() == "(a -> a) when a: true | false"

      assert quoted_of(fn x ->
        fn z ->
          (fn y :: boolean() -> y end).(x)
        end
        x
      end) |> format() == "(a -> a) when a: true | false"

      assert quoted_of(fn x ->
        (fn true -> true end).(x)
        (fn z ->
          (fn true -> true end).(z)
          z
        end).(x)
      end) |> format() == "(true -> true)"

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
        (fn z ->
          (fn true -> true end).(z)
          z
        end).(x)
      end) |> format() == "(true -> true)"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
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

    test "apply with inference on multiple clauses" do
      assert quoted_of(fn x ->
        (fn true -> true; false -> false end).(x)
        (fn false -> false end).(x)
      end) |> format() == "(false -> false)"

      assert quoted_of(fn x ->
        (fn false -> false end).(x)
        (fn true -> true; false -> false end).(x)
      end) |> format() == "(false -> false)"

      assert quoted_of(fn x ->
        (fn false -> false; nil -> nil; _ -> true end).(x)
      end) |> format() == "(a -> false | nil | true)"

      assert quoted_of(fn x ->
        a = (fn false -> false; nil -> nil; _ -> true end).(x)
        b = (fn y -> y end).(x)
        c = x
        {a, b, c}
      end) |> format() == "(a -> {false | nil | true, a, a})"

      assert quoted_of(fn x ->
        a = (fn true -> false; y -> y end).(x)
        b = (fn z -> z end).(x)
        c = x
        {a, b, c}
      end) |> format() == "(a -> {false | a, a, a})"

      assert quoted_of(fn x ->
        a = (fn true -> false; y -> y end).(x)
        b = (fn false -> false end).(x)
        c = x
        {a, b, c}
      end) |> format() == "(false -> {false, false, false})"

      assert quoted_of(fn x ->
        (fn :foo -> :bar; y :: atom() -> :baz end).(x)
      end) |> format() == "(atom() -> :bar | :baz)"

      assert quoted_of(fn x :: atom() ->
        (fn :foo -> :bar; y :: atom() -> :baz end).(x)
      end) |> format() == "(atom() -> :bar | :baz)"
    end

    test "apply with closure" do
      assert quoted_of((fn x -> (fn y -> x end) end).(true)) |> format() ==
             "(a -> true)"

      assert quoted_of((fn x -> (fn y -> x end) end).(true).(:foo)) |> format() ==
             "true"
    end

    # This test is about let polymorphism.
    #
    # Although rank 2 intersection types do not require let polymorphism,
    # we implement them to avoid having to rearrange ASTs into let formats.
    # Papers such as "Let should not be generalized" argue against this
    # in terms of simplicity on type systems that have constraints (although
    # we haven't reached such trade-offs yet).
    test "apply on variable" do
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of((
          x = fn :bar -> :bar end
          x.(:foo)
        ))

      assert quoted_of((
          x = fn y -> y end
          x.(:foo)
        )) |> format() == ":foo"

      assert quoted_of((
          x = fn y :: atom() -> y end
          x.(:foo)
        )) |> format() == ":foo"

      assert quoted_of((
          x = fn y -> y end
          {x.(:foo), x.(:foo)}
        )) |> format() == "{:foo, :foo}"

      assert quoted_of((
          x = fn y -> y end
          {x.(:foo), x.(:bar)}
        )) |> format() == "{:foo, :bar}"

      assert quoted_of((y = fn x -> x end; y.(y))) |> format() ==
             "(a -> a)"

      assert quoted_of((y = fn x -> x end; {y, y})) |> format() ==
             "{(a -> a), (b -> b)}"

      assert quoted_of((z = fn x -> fn y -> y end end; {z, z})) |> format() ==
             "{(a -> (b -> b)), (c -> (d -> d))}"

      assert quoted_of((z = (fn x -> fn y -> y end end).(:foo); {z, z})) |> format() ==
             "{(a -> a), (b -> b)}"

      assert quoted_of((w = (fn x -> z = fn y -> y end; {z, z} end); {w, w})) |> format() ==
             "{(a -> {(b -> b), (c -> c)}), (d -> {(e -> e), (f -> f)})}"

      assert quoted_of((y = fn x -> fn y -> x.(x.(y)) end end; {y, y})) |> format() ==
             "{((a -> b; b -> c) -> (a -> c)), ((d -> e; e -> f) -> (d -> f))}"

      assert quoted_of(fn x -> z = fn y -> {x, y} end; {z, z} end) |> format() ==
             "(a -> {(b -> {a, b}), (c -> {a, c})})"
    end

    test "apply with function arguments" do
      assert quoted_of((fn x ->
          x.(:foo)
        end).(fn y -> y end)) |> format() == ":foo"

      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar)}
        end).(fn y -> y end)
      ) |> format() == "{:foo, :bar}"

      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar)}
        end).(fn y :: atom() -> y end)
      ) |> format() == "{:foo, :bar}"

      # Same clauses
      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar)}
        end).(fn :foo -> :x; :bar -> :y end)
      ) |> format() == "{:x, :y}"

      # More clauses
      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar)}
        end).(fn :foo -> :x; :bar -> :y; :baz -> :z end)) |> format() == "{:x, :y}"

      # Less clauses
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of((fn x ->
          {x.(:foo), x.(:bar), x.(:baz)}
        end).(fn :foo -> :x; :bar -> :y end))

      # Support multiple bindings
      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar), x.(:baz)}
        end).(fn y :: atom() -> y end)
      ) |> format() == "{:foo, :bar, :baz}"

      # Does not restrict functions
      assert quoted_of((
        c = fn y -> y end
        (fn x -> {x.(:foo), x.(:bar)} end).(c)
        c)) |> format() == "(a -> a)"
    end

    test "apply with function arguments and free variables" do
      # Binding are lazy (z is true and not true | false)
      assert quoted_of(fn z ->
        (fn true -> true; false -> false end).(z)
        x = z
        (fn true -> true end).(z)
        x
      end) |> format() == "(true -> true)"

      assert quoted_of(fn z ->
        (fn true -> true end).(z)
        x = z
        (fn true -> true; false -> false end).(z)
        x
      end) |> format() == "(true -> true)"

      assert quoted_of(fn z ->
        (fn true -> true; false -> false end).(z)
        x = z
        (fn true -> true end).(x)
        x
      end) |> format() == "(true -> true)"

      # z must be nil
      assert quoted_of(fn z ->
        (fn x -> nil = x.(:any) end).(fn y -> z end)
        z
      end) |> format() == "(nil -> nil)"

      # z conflicts with external value
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of(fn z ->
          (fn true -> true; false -> false end).(z)
          (fn x -> nil = x.(:any) end).(fn y -> z end)
        end)

      # z conflicts with internal value
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of(fn z ->
          (fn x -> true = x.(:foo); false = x.(:bar)  end).(fn y -> z end)
          z
        end)

      # z conflicts with internal value and multiple clauses
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of(fn z ->
          (fn x -> true = x.(:foo); false = x.(:bar) end).(fn :foo -> z; :bar -> z end)
        end)
    end

    test "apply with rank-2 function argument" do
      assert {:error, _, {:disjoint_apply, _, _, _}} =
               quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                         (fn :foo -> :bar; :baz -> :bat end))

      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn :foo -> :bar; :bar -> :baz end)) |> format() == "(:foo -> :baz)"

      # TODO: Make this pass
      # assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
      #                  (fn :bar -> :baz; :foo -> :bar end)) |> format() == "(:foo -> :baz)"
    end
  end

  describe "of/1 with variable tracking" do
    test "tuples" do
      assert quoted_of(({x = :ok, y = :error}; y)) |> format() == ":error"
    end

    test "blocks" do
      assert quoted_of((a = :ok; b = a; b)) |> format() == ":ok"
    end

    test "pattern matching" do
      assert quoted_of((a = (a = true; b = false); a)) |> format() == "false"
    end
  end

  describe "of/1 fns" do
    test "patterns" do
      assert quoted_of(fn x -> x end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn {x :: integer(), x} -> x end) |> format() ==
             "({integer(), integer()} -> integer())"

      assert quoted_of(fn {x :: integer(), x :: integer()} -> x end) |> format() ==
             "({integer(), integer()} -> integer())"

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
      end) |> format() == "(integer() -> integer())"
    end

    test "bidirectional matching" do
      assert quoted_of(fn z ->
        {:ok, x} = (fn y -> {y, :error} end).(z)
        {z, x}
      end) |> format() == "(:ok -> {:ok, :error})"

      assert quoted_of(fn z ->
        {:ok, x} = (fn y -> {y, :error} end).(z)
      end) |> format() == "(:ok -> {:ok, :error})"
    end

    test "bidirectional matching with multiple clauses" do
      assert quoted_of(fn z ->
        {x, y} = (fn true -> {true, :foo}; false -> {false, :bar} end).(z)
        {y, x}
      end) |> format() == "(true | false -> {:foo | :bar, true | false})"
    end

    test "free variables" do
      assert quoted_of(fn x -> x end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn x -> fn y -> y end end) |> format() ==
             "(a -> (b -> b))"

      assert quoted_of(fn x -> fn y -> x end end) |> format() ==
             "(a -> (b -> a))"
    end

    test "rank 2 inference" do
      assert quoted_of(fn x -> {x.(:foo), x.(:foo)} end) |> format() ==
             "((:foo -> a) -> {a, a})"

      assert quoted_of(fn x -> {x.(:foo), x.(:bar)} end) |> format() ==
             "((:foo -> a; :bar -> b) -> {a, b})"

      assert quoted_of(fn x -> x.(fn y -> y end) end) |> format() ==
             "(((a -> a) -> b) -> b)"

      assert quoted_of(fn x -> fn y -> x.(x.(y)) end end) |> format() ==
             "((a -> b; b -> c) -> (a -> c))"

      # TODO: Reintroduce those when we have multiple arguments.
      # assert quoted_of((fn x ->
      #   z = (fn z :: atom() -> z end).(:bar)
      #   {x.(z), x.(z)}
      # end)) |> format() == "((atom() -> a) -> {a, a})"

      # assert quoted_of((fn x ->
      #   z = (fn z :: atom() -> z end).(:bar)
      #   {x.(:foo), x.(z)}
      # end)) |> format() == "((:foo -> a; atom() -> b) -> {a, b})"

      # assert quoted_of((fn x ->
      #   z = (fn z :: atom() -> z end).(:bar)
      #   {x.(z), x.(:foo)}
      # end)) |> format() == "((:foo -> a; atom() -> b) -> {b, a})"

      assert {:error, _, {:recursive_fn, _, _, _}} =
             quoted_of(fn x -> x.(x) end)
    end

    test "bindings" do
      assert quoted_of(fn x -> fn y :: atom() -> y end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:y, nil}, 1}],
                     %{1 => [:atom]}}], 1}],
                %{0 => []}}], 1}]

      assert quoted_of(fn x -> fn y -> y end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:y, nil}, 1}],
                     %{1 => []}}], 1}],
                %{0 => []}}], 1}]

      assert quoted_of(fn x -> fn y -> x end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:x, nil}, 0}],
                     %{1 => []}}], 1}],
                %{0 => []}}], 1}]

      assert {:ok,
              [{:fn,
               [{_, _, %{1 => [], 2 => [], 3 => []}}],
               1}],
              _} = quoted_of(fn x -> fn y -> x.(x.(y)) end end)
    end
  end
end
