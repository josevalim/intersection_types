defmodule Types.CheckerTest do
  use ExUnit.Case, async: true

  alias Types.{Checker, Union}

  defp format({:ok, types, %{inferred: inferred}}) do
    types
    |> Checker.bind_matching(inferred, inferred)
    |> Union.to_iodata()
    |> IO.iodata_to_binary()
  end

  defmacro quoted_of(expr) do
    quote do
      Checker.of(unquote(Macro.escape(expr)))
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

    test "lists" do
      assert quoted_of([]) |> format() == "empty_list()"
      assert quoted_of([true | false]) |> format() == "cons(true, false)"
      assert quoted_of([true, false]) |> format() == "cons(true, cons(false, empty_list()))"
    end

    test "match" do
      assert {:error, _, {:disjoint_match, _, _}} =
               quoted_of({:ok, a :: atom()} = {:ok, 0})

      assert {:error, _, {:disjoint_match, _, _}} =
               quoted_of(fn a :: atom() -> :ok = a end)
    end

    test "generalization" do
      assert quoted_of((y = fn x -> x end; y.(y))) |> format() ==
             "(a -> a)"

      assert quoted_of((y = fn x -> x end; z = y; {z, z})) |> format() ==
             "{(a -> a), (b -> b)}"

      assert quoted_of((y = fn x -> x end; fn z -> fn w -> {y, y} end end)) |> format() ==
             "(a -> (b -> {(c -> c), (d -> d)}))"

      assert quoted_of((z = fn x -> fn y -> y end end; {z, z})) |> format() ==
             "{(a -> (b -> b)), (c -> (d -> d))}"

      assert quoted_of((z = (fn x -> fn y -> y end end).(:foo); {z, z})) |> format() ==
             "{(a -> a), (b -> b)}"

      assert quoted_of((w = (fn x -> z = fn y -> y end; {z, z} end); {w, w})) |> format() ==
             "{(a -> {(b -> b), (c -> c)}), (d -> {(e -> e), (f -> f)})}"

      assert quoted_of(fn x -> y = (fn z -> z end).(x); {y, y} end) |> format() ==
             "(a -> {a, a})"

      assert quoted_of(fn x -> y = fn z -> x.(z) end; {y, y} end) |> format() ==
             "((a -> b) -> {(a -> b), (a -> b)})"

      assert quoted_of((y = (fn x -> fn z -> x.(z) end end).(fn w -> w end); {y, y})) |> format() ==
             "{(a -> a), (b -> b)}"

      assert quoted_of((y = fn x -> fn y -> x.(x.(y)) end end; {y, y})) |> format() ==
             "{((a -> a) -> (a -> a)), ((b -> b) -> (b -> b))}"

      assert quoted_of((w = fn x -> fn y -> fn z -> x.(y.(z)) end end end; {w, w})) |> format() ==
             "{((a -> b) -> ((c -> a) -> (c -> b))), ((d -> e) -> ((f -> d) -> (f -> e)))}"

      assert quoted_of(fn x -> y = x; y end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn x -> z = fn y -> {x, y} end; {z, z} end) |> format() ==
             "(a -> {(b -> {a, b}), (c -> {a, c})})"
    end
  end

  describe "of/1 apply" do
    test "simple" do
      assert quoted_of((fn false -> true; true -> false end).(false)) |> format() ==
             "true"

      assert quoted_of((fn false -> true; true -> false end).(true)) |> format() ==
             "false"

      assert quoted_of((fn y :: atom() -> y end).(:foo)) |> format() ==
             ":foo"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn x :: atom() -> (fn :foo -> :foo end).(x) end)

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn x :: boolean() -> (fn true -> true end).(x) end)
    end

    test "with inference" do
      assert quoted_of(fn x -> (fn y -> y end).(x) end) |> format() ==
             "(a -> a)"

      assert quoted_of((fn y -> y end).(fn x -> x end)) |> format() ==
             "(a -> a)"

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
      end) |> format() == "(false | true -> false | true)"

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
        (fn true -> true; false -> false end).(x)
      end) |> format() == "(false | true -> false | true)"

      assert quoted_of(fn x ->
        (fn y :: boolean() -> y end).(x)
        (fn y :: boolean() -> y end).(x)
      end) |> format() == "(false | true -> false | true)"

      assert quoted_of(fn x :: boolean() ->
        (fn y -> y end).(x)
      end) |> format() == "(false | true -> false | true)"

      assert quoted_of(fn x ->
        fn z ->
          (fn y :: boolean() -> y end).(x)
        end
        x
      end) |> format() == "(a -> a) when a: false | true"

      assert quoted_of(fn x ->
        (fn true -> true end).(x)
        (fn z ->
          (fn true -> true end).(z)
          z
        end).(x)
      end) |> format() == "(true -> true)"

      assert quoted_of(fn x ->
          (fn {true, z} -> z end).({x, x})
      end) |> format() == "(true -> true)"

      assert quoted_of(fn x ->
          (fn {z, true} -> z end).({x, x})
      end) |> format() == "(true -> true)"
    end

    test "with inference on multiple clauses" do
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
      end) |> format() == "(false | nil | a -> false | nil | true)"

      assert quoted_of(fn x :: :foo ->
        (fn :foo -> :bar; y :: atom() -> :baz end).(x)
      end) |> format() == "(:foo -> :bar)"

      assert quoted_of(fn x ->
        (fn :foo -> :bar; y :: atom() -> :baz end).(x)
      end) |> format() == "(atom() -> :bar | :baz)"

      assert quoted_of(fn x :: atom() ->
        (fn :foo -> :bar; y :: atom() -> :baz end).(x)
      end) |> format() == "(atom() -> :bar | :baz)"

      assert quoted_of(fn x :: atom() ->
        (fn y :: boolean() -> :bar; z :: atom() -> :baz end).(x)
      end) |> format() == "(atom() -> :bar | :baz)"

      assert quoted_of(fn x ->
        (fn :foo -> :bar; y -> y end).(x)
      end) |> format() == "(:foo | a -> :bar | a)"

      assert quoted_of((fn x ->
        (fn :foo -> :bar; y -> y end).(x)
      end).(:baz)) |> format() == ":bar | :baz"

      assert quoted_of(fn x :: atom() ->
        (fn :foo -> :bar; y -> y end).(x)
      end) |> format() == "(a -> :bar | a) when a: atom()"

      assert quoted_of((fn x :: atom() ->
        (fn :foo -> :bar; y -> y end).(x)
      end).(:baz)) |> format() == ":bar | :baz"

      assert quoted_of(fn x :: boolean() ->
        (fn true -> :foo; y -> y end).(x)
      end) |> format() == "(false | true -> false | :foo)"

      assert quoted_of(fn x :: integer() | atom() ->
        (fn y :: integer() -> :foo; z -> {:bar, z} end).(x)
      end) |> format() == "(integer() | a -> :foo | {:bar, a}) when a: atom()"

      assert quoted_of(fn x ->
        fn y :: boolean() ->
          (fn {z, true} -> z; {:foo, false} -> false end).({x, y})
        end
      end) |> format() == "(:foo | a -> (false | true -> false | a))"

      assert quoted_of(fn x ->
        fn y :: boolean() ->
          (fn {:foo, false} -> false; {z, true} -> z end).({x, y})
        end
      end) |> format() == "(:foo | a -> (false | true -> false | a))"
    end

    # TODO: Make this pass. See notes in union.ex.
    # test "with inference on same vars" do
    #   assert quoted_of(fn {a :: integer(), b :: atom()} ->
    #     (fn {x, y} -> {x, y} end).({a, b})
    #   end) |> format() == ""
    #
    #   assert quoted_of(fn {a :: integer(), b :: atom()} ->
    #     (fn {x, x} -> x end).({a, b})
    #   end) |> format() == ""
    #
    #   assert quoted_of(fn {a :: integer(), b :: atom()} ->
    #     (fn {x, x} -> {x, x}; {x, y} -> {x, y} end).({a, b})
    #   end) |> format() == ""
    # end

    # Although intersection types do not require let polymorphism,
    # we implement them to avoid having to rearrange ASTs into let
    # formats. Papers such as "Let should not be generalized" argue
    # against this in terms of simplicity on type systems that have
    # constraints (although we haven't reached such trade-offs yet).
    test "on variable" do
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

      assert quoted_of((
          x = fn y, z -> {y, z} end
          {x.(:foo, :bar), x.(:bar, :baz)}
        )) |> format() == "{{:foo, :bar}, {:bar, :baz}}"
    end

    test "with function argument" do
      # ((a -> b) -> (a -> b)) match
      assert quoted_of((fn x -> fn y -> x.(y) end end).
                       (fn :foo -> :bar end)) |> format() ==
             "(:foo -> :bar)"

      # ((a -> b) -> (a -> b)) superset
      assert quoted_of((fn x -> fn y -> x.(y) end end).
                       (fn x :: atom() -> x end)) |> format() ==
             "(atom() -> atom())"

      # ((a -> b) -> (a -> b)) multiple clauses
      assert quoted_of((fn x -> fn y -> x.(y) end end).
                       (fn :foo -> :bar; :bar -> :bat end)) |> format() ==
             "(:bar | :foo -> :bar | :bat)"

      # ((a -> a) -> (a -> a)) match
      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn :foo -> :foo end)) |> format() ==
             "(:foo -> :foo)"

      # ((a -> a) -> (a -> a)) no match
      assert {:error, _, {:disjoint_apply, _, _, _}} =
               quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                         (fn :foo -> :bar; :bar -> :baz end))

      # ((a -> a) -> (a -> a)) superset
      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn x :: atom() -> x end)) |> format() ==
             "(atom() -> atom())"

      # ((a -> a) -> (a -> a)) multiple clauses
      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn :foo -> :foo; :bar -> :bar; :no -> :match end)) |> format() ==
             "(:bar | :foo -> :bar | :foo)"

      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn :foo -> :foo; :bar -> :bar end).
                       (:foo)) |> format() ==
             ":foo"

      # (((b -> b) -> a) -> a) matches
      assert quoted_of((fn x -> x.(fn y -> y end) end).
                       (fn x -> {x.(:foo), x.(:bar)} end)) |> format() ==
             "{:foo, :bar}"

      assert quoted_of((fn x -> x.(fn y -> y end) end).
                       (fn x -> {x, x.(:foo), x.(:bar)} end)) |> format() ==
             "{(:bar -> :bar; :foo -> :foo), :foo, :bar}"

      assert quoted_of((fn x -> {x, x.(fn y -> y end)} end).
                       (fn x -> {x.(:foo), x.(:bar)} end)) |> format() ==
             "{((:bar | :foo -> :bar | :foo) -> {:foo, :bar}), {:foo, :bar}}"
    end

    test "with function argument and type-recursive" do
      # # Generalization
      assert quoted_of((
        y = (fn x -> fn y -> x.(x.(y)) end end).(fn z -> z end)
        {y, y}
      )) |> format() == "{(a -> a), (b -> b)}"

      # Multiple clauses
      assert quoted_of((
        y = (fn x -> fn y -> x.(x.(y)) end end).(fn :foo -> :foo; z -> z end)
        {y, y}
      )) |> format() == "{(:foo | a -> :foo | a), (:foo | b -> :foo | b)}"

      #  Multiple applications
      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                 (fn z -> z end).
                 (fn :foo -> :foo; :bar -> :bar end)) |> format() ==
             "(:foo -> :foo; :bar -> :bar)"
    end

    test "on intersection types" do
      assert quoted_of((fn x ->
          x.(:foo)
        end).(fn y -> y end)) |> format() == ":foo"

      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar)}
        end).(fn y -> y end)
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

      # Supertype
      assert quoted_of((fn x ->
          {x.(:foo), x.(:bar), x.(:baz)}
        end).(fn y :: atom() -> y end)
      ) |> format() == "{:foo, :bar, :baz}"

      # Does not restrict functions
      assert quoted_of((
        c = fn y -> y end
        (fn x -> {x.(:foo), x.(:bar)} end).(c)
        c
      )) |> format() == "(a -> a)"

      # Works at multiple levels
      assert quoted_of(
        (fn x ->
          {x.(:foo).(:baz), x.(:bar).(:bat)}
        end).(fn x -> fn y -> y end end)
      ) |> format() == "{:baz, :bat}"
    end

    test "on intersection types with subsets" do
      assert quoted_of(fn z ->
        (fn {x, y :: atom()} ->
          x.(y)
        end).({fn :foo -> :bar; w :: atom() -> :baz end, z})
      end) |> format() == "(atom() -> :bar | :baz)"
    end

    test "on intersection types with free variables" do
      assert quoted_of(fn z ->
          (fn x -> {x.({:ok, z}), x.({:error, z})} end).
          (fn {:ok, :ok} -> :bar; {:error, :ok} -> :foo end)
        end) |> format() == "(:ok -> {:bar, :foo})"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn z ->
               (fn x -> {x.({:ok, z}), x.({:error, z})} end).
               (fn {:ok, :ok} -> :bar; {:error, :error} -> :foo end)
             end)
    end

    test "on intersection types with multiple arguments" do
      # First arg
      assert quoted_of((fn x, y -> {x.({:foo, y}), x.({:bar, y})} end).
                       (fn {:foo, :ok} -> :bar; {:bar, :ok} -> :foo end, :ok)) |> format() ==
             "{:bar, :foo}"

      assert quoted_of(fn z ->
          (fn x, y -> {x.({:foo, y}), x.({:bar, y})} end).
          (fn {:foo, :ok} -> :bar; {:bar, :ok} -> :foo end, z)
        end) |> format() == "(:ok -> {:bar, :foo})"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of((fn x, y -> {x.({:foo, y}), x.({:bar, y})} end).
                       (fn {:foo, :ok} -> :bar; {:bar, :error} -> :foo end, :ok))

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn z ->
                (fn x, y -> {x.({:foo, y}), x.({:bar, y})} end).
                (fn {:foo, :ok} -> :bar; {:bar, :error} -> :foo end, z)
             end)

      # Second arg
      assert quoted_of((fn y, x -> {x.({:foo, y}), x.({:bar, y})} end).
                       (:ok, fn {:foo, :ok} -> :bar; {:bar, :ok} -> :foo end)) |> format() ==
             "{:bar, :foo}"

      assert quoted_of(fn z ->
          (fn y, x -> {x.({:foo, y}), x.({:bar, y})} end).
          (z, fn {:foo, :ok} -> :bar; {:bar, :ok} -> :foo end)
        end) |> format() == "(:ok -> {:bar, :foo})"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of((fn y, x -> {x.({:foo, y}), x.({:bar, y})} end).
                       (:ok, fn {:foo, :ok} -> :bar; {:bar, :error} -> :foo end))

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(fn z ->
                (fn y, x -> {x.({:foo, y}), x.({:bar, y})} end).
                (z,  fn {:foo, :ok} -> :bar; {:bar, :error} -> :foo end)
             end)
    end

    test "with lazy inference" do
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

      # Match types cannot be not lazy though
      assert quoted_of(fn x ->
        z = (fn true -> true; false -> false end).(x)
        (fn true -> true end).(x)
        z
      end) |> format() == "(true -> false | true)"

      assert quoted_of(fn x ->
        (fn true -> true end).(x)
        z = (fn true -> true; false -> false end).(x)
        z
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
          (fn x -> true = x.(:foo); false = x.(:bar) end).(fn y -> z end)
          z
        end)

      # z conflicts with internal value and multiple clauses
      assert {:error, _, {:disjoint_apply, _, _, _}} =
        quoted_of(fn z ->
          (fn x -> true = x.(:foo); false = x.(:bar) end).(fn :foo -> z; :bar -> z end)
        end)
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

    test "with binding" do
      assert quoted_of((x :: boolean()) = true) |> format() ==
             "true"

      assert quoted_of(fn y -> x = y; x end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn y :: atom() -> x = y; x end) |> format() ==
             "(a -> a) when a: atom()"

      assert quoted_of(fn y -> (x :: atom()) = y; x end) |> format() ==
             "(a -> a) when a: atom()"

      assert {:error, _, {:disjoint_match, _, _}} =
             quoted_of(fn y -> (x :: atom()) = y; (x :: integer()) = y; y end)

      assert {:error, _, {:disjoint_match, _, _}} =
             quoted_of(fn y :: atom() -> (x :: boolean()) = y; y end)

      assert {:error, _, {:disjoint_match, _, _}} =
             quoted_of(fn x -> true = (fn y :: boolean() -> y end).(x) end)
    end
  end

  describe "of/1 fns" do
    test "with no args" do
      assert quoted_of(fn -> :ok end) |> format() ==
             "(-> :ok)"
    end

    test "patterns" do
      assert quoted_of(fn x -> x end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn {x :: integer(), x} -> x end) |> format() ==
             "({integer(), integer()} -> integer())"

      assert quoted_of(fn {x :: integer(), x :: integer()} -> x end) |> format() ==
             "({integer(), integer()} -> integer())"

      assert quoted_of(fn x :: boolean() -> x end) |> format() ==
             "(false | true -> false | true)"

      assert quoted_of(fn {:ok, x :: boolean()} -> x end) |> format() ==
             "({:ok, false} | {:ok, true} -> false | true)"

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x, x :: boolean()} -> x end)

      assert {:error, _, {:bound_var, _, _, _}} =
             quoted_of(fn {x :: integer(), x :: boolean()} -> x end)
    end

    # TODO: Handle duplicate clauses
    # test "duplicate clauses" do
    #   assert quoted_of(fn 0 -> 0; 1 -> 1 end) |> format() == "(integer() -> integer())"
    # end

    test "late propagation" do
      assert quoted_of(fn x ->
        z = x
        (fn 0 -> 0 end).(x) # TODO: This should emit a warning for being non-exaustive.
        z
      end) |> format() == "(integer() -> integer())"
    end

    test "free variables" do
      assert quoted_of(fn x -> x end) |> format() ==
             "(a -> a)"

      assert quoted_of(fn x -> fn y -> y end end) |> format() ==
             "(a -> (b -> b))"

      assert quoted_of(fn x -> fn y -> x end end) |> format() ==
             "(a -> (b -> a))"

      assert quoted_of(fn x -> x.(fn y -> y end) end) |> format() ==
             "(((a -> a) -> b) -> b)"

      assert quoted_of(fn x -> fn y -> x.(y) end end) |> format() ==
             "((a -> b) -> (a -> b))"

      assert quoted_of(fn x -> fn y -> y.(x) end end) |> format() ==
             "(a -> ((a -> b) -> b))"

      assert quoted_of(fn x -> fn y -> x.(x.(y)) end end) |> format() ==
             "((a -> a) -> (a -> a))"
    end

    test "rank 2 inference" do
      assert quoted_of(fn x -> {x.(:foo), x.(:foo)} end) |> format() ==
             "((:foo -> a) -> {a, a})"

      assert quoted_of(fn x -> {x.(x.(:foo)), x.(x.(:bar))} end) |> format() ==
             "((:bar -> :bar; :foo -> :foo) -> {:foo, :bar})"

      assert quoted_of(fn x -> fn y -> {x.(y), x.(:foo), x.(:bar)} end end) |> format() ==
             "((:bar -> a; :foo -> b; c -> d) -> (c -> {d, b, a}))"

      assert quoted_of(fn x -> fn y -> {x.(:foo), x.(y), x.(:bar)} end end) |> format() ==
             "((:bar -> a; :foo -> b; c -> d) -> (c -> {b, d, a}))"

      assert quoted_of(fn x -> fn y -> {x.(:foo), x.(:bar), x.(y)} end end) |> format() ==
             "((:bar -> a; :foo -> b; c -> d) -> (c -> {b, a, d}))"

      assert quoted_of(fn x -> fn y -> {x.(:foo), x.(x.(y))} end end) |> format() ==
             "((:foo -> a; b -> b) -> (b -> {a, b}))"

      assert quoted_of(fn x -> fn y -> {x.(y), x.(y)} end end) |> format() ==
             "((a -> b) -> (a -> {b, b}))"

      assert quoted_of(fn x -> fn y -> fn z -> {x.(y), x.(z)} end end end) |> format() ==
             "((a -> b; c -> d) -> (a -> (c -> {b, d})))"

      assert quoted_of(fn x -> fn y -> {x.(x.(y)), x.(:foo)} end end) |> format() ==
             "((:foo -> a; b -> b) -> (b -> {b, a}))"

      assert quoted_of(fn x -> fn y -> {x.(x.(y)), x.(x.(y))} end end) |> format() ==
             "((a -> a) -> (a -> {a, a}))"

      assert quoted_of(fn x -> {x.(:foo), x.(:bar)} end) |> format() ==
             "((:bar -> a; :foo -> b) -> {b, a})"

      assert quoted_of(fn y -> fn x -> {x.(:foo), x.(:bar)} end end) |> format() ==
             "(a -> ((:bar -> b; :foo -> c) -> {c, b}))"

      assert quoted_of(fn x -> {x.(:foo).(:baz), x.(:bar).(:bat)} end) |> format() ==
             "((:bar -> (:bat -> a); :foo -> (:baz -> b)) -> {b, a})"

      # With supertypes
      assert quoted_of(fn x ->
        z = (fn z :: atom() -> z end).(:bar)
        {x.(:foo), x.(z)}
      end) |> format() == "((:bar -> a; :foo -> b) -> {b, a})"

      assert quoted_of(fn x ->
        z = (fn z :: atom() -> z end).(:bar)
        {x.(z), x.(:foo)}
      end) |> format() == "((:foo -> a; :bar -> b) -> {b, a})"

      assert quoted_of(fn x, y ->
        z = (fn z :: atom() -> z end).(y)
        {x.(z), x.(:foo)}
      end) |> format() == "((:foo -> a; atom() -> b), atom() -> {b, a})"

      assert quoted_of(fn x, y ->
        z = (fn z :: atom() -> z end).(y)
        {x.(:foo), x.(z)}
      end) |> format() == "((:foo -> a; atom() -> b), atom() -> {a, b})"

      assert {:error, _, {:occurs, _, _, _, _}} =
             quoted_of(fn x -> fn y -> {x.(y), y.(x)} end end)

      assert {:error, _, {:self_var_apply, _, _, _}} =
             quoted_of(fn x -> x.(x) end)

      assert {:error, _, {:self_var_apply, _, _, _}} =
             quoted_of(fn y -> x = y; x.(x) end)

      assert {:error, _, {:disjoint_var_apply, _}} =
             quoted_of(fn x -> {x.(:foo), x.(:foo, :bar)} end)

      assert {:error, _, {:recursive_var_apply, _}} =
             quoted_of(fn x -> x.({:foo, x.(:foo)}) end)
    end

    test "multiple arguments" do
      assert quoted_of(fn x, y -> x.(y) end) |> format() ==
             "((a -> b), a -> b)"

      assert quoted_of(fn x, y -> y.(x) end) |> format() ==
             "(a, (a -> b) -> b)"

      assert quoted_of(fn x, y -> {x.(y), y.(x)} end) |> format() ==
             "((a -> b), (c -> d) -> {b, d}) when c: ((c -> d) -> b), a: ((a -> b) -> d)"
    end

    test "multiple clauses" do
      assert quoted_of(fn false -> false; nil -> nil; _ -> true end) |> format() ==
             "(false -> false; nil -> nil; a -> true)"
    end

    test "binding" do
      assert quoted_of(fn x -> fn y :: atom() -> y end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:y, nil}, 1}]
                  }], %{1 => [:atom]}, 1}]
                }], %{0 => []}, 1}]

      assert quoted_of(fn x -> fn y -> y end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:y, nil}, 1}]
                   }], %{1 => []}, 1}]
                }], %{0 => []}, 1}]

      assert quoted_of(fn x -> fn y -> x end end) |> elem(1) ==
             [{:fn,
               [{[[{:var, {:x, nil}, 0}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                     [{:var, {:x, nil}, 0}]
                    }], %{1 => []}, 1}]
                }], %{0 => []}, 1}]

      assert quoted_of(fn x -> fn y -> x.(y) end end) |> elem(1) ==
             [{:fn,
              [{[[{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 2}]}], %{}, 1}]],
                [{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 2}]}], %{}, 1}]
               }], %{1 => [], 2 => []}, 1}]

      assert quoted_of(fn x -> fn y :: atom() -> x.(y) end end) |> elem(1) ==
             [{:fn,
              [{[[{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 2}]}], %{}, 1}]],
                [{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:x, nil}, 2}]}], %{}, 1}],
               }], %{1 => [:atom], 2 => []}, 1}]

      assert quoted_of(fn x -> fn y -> x.(x.(y)) end end) |> elem(1) ==
             [{:fn,
              [{[[{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:y, nil}, 1}]}], %{}, 1}]],
                [{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:y, nil}, 1}]}], %{}, 1}],
               }], %{1 => []}, 1}]

      assert quoted_of(fn x -> fn y -> fn z -> x.(x.(z)) end end end) |> elem(1) ==
             [{:fn,
               [{[[{:fn, [{[[{:var, {:z, nil}, 2}]], [{:var, {:z, nil}, 2}]}], %{}, 1}]],
                 [{:fn,
                   [{[[{:var, {:y, nil}, 1}]],
                   [{:fn, [{[[{:var, {:z, nil}, 2}]], [{:var, {:z, nil}, 2}]}], %{}, 1}],
                  }], %{1 => []}, 1}]
                }], %{2 => []}, 1}]

      assert quoted_of(fn x -> fn y -> fn z -> x.(y.(z)) end end end) |> elem(1) ==
             [{:fn,
               [{[[{:fn, [{[[{:var, {:y, nil}, 3}]], [{:var, {:x, nil}, 4}]}], %{}, 1}]],
                 [{:fn,
                   [{[[{:fn, [{[[{:var, {:z, nil}, 2}]], [{:var, {:y, nil}, 3}]}], %{}, 1}]],
                     [{:fn, [{[[{:var, {:z, nil}, 2}]], [{:var, {:x, nil}, 4}]}], %{}, 1}],
                    }], %{2 => []}, 1}],
                }], %{3 => [], 4 => []}, 1}]

      assert quoted_of((fn x -> fn y -> x.(x.(y)) end end).
                       (fn :foo -> :foo; :bar -> :bar end)) |> elem(1) ==
             [{:fn, [{[[{:var, {:y, nil}, 1}]], [{:var, {:y, nil}, 1}]}], %{}, 1}]

      assert quoted_of(recur = fn {:+, num} -> recur(num); num -> num end) |> elem(1) ==
             [{:fn,
               [{[[{:tuple, [{:atom, :+}, {:var, {:num, nil}, 0}], 2}]],
                 [{:var, {:apply, Types.Checker}, 3}]},
                {[[{:var, {:num, nil}, 2}]],
                 [{:var, {:num, nil}, 2}]}],
              %{0 => [{:tuple, [{:atom, :+}, {:var, {:num, nil}, 0}], 2},
                      {:var, {:apply, Types.Checker}, 3}],
                2 => [],
                3 => []}, 1}]
    end
  end

  describe "of/1 lists" do
    test "matching cons" do
      assert quoted_of((fn [x | y] -> {x, y} end).([:foo])) |> format() ==
             "{:foo, empty_list()}"

      assert quoted_of((fn [x | y] -> {x, y} end).([:foo | :bar])) |> format() ==
             "{:foo, :bar}"

      assert quoted_of((fn [x | y] -> {x, y} end).([:foo, :bar, :baz])) |> format() ==
             "{:foo, cons(:bar, cons(:baz, empty_list()))}"

      assert quoted_of((fn [x, y, z] -> {x, y, z} end).([:foo, :bar, :baz])) |> format() ==
             "{:foo, :bar, :baz}"

      assert {:error, _, _} =
             quoted_of((fn [x, y, z, w] -> {x, y, z, w} end).([:foo, :bar, :baz]))

      assert {:error, _, _} =
             quoted_of((fn [x | y] -> {x, y} end).([]))
    end
  end

  describe "of/1 recur" do
    test "single variable recursive tuples" do
      # Free variables
      assert quoted_of(recur = fn
        {:+, num} ->
          recur(num)
        num :: integer() ->
          num
      end) |> format() == "({:+, a} -> integer(); integer() -> integer()) when a: integer() | {:+, a}"

      # Free variables idempotency
      assert quoted_of(recur = fn
        {:+, num} ->
          recur(num)
          recur(num)
        num :: integer() ->
          num
      end) |> format() == "({:+, a} -> integer(); integer() -> integer()) when a: integer() | {:+, a}"

      # Invert free variables ordering
      assert quoted_of(recur = fn
        num :: integer() ->
          num
        {:+, num} ->
          recur(num)
      end) |> format() == "(integer() -> integer(); {:+, a} -> integer()) when a: integer() | {:+, a}"

      # Superset variables
      assert quoted_of(recur = fn
        {:+, num} ->
          (fn x :: integer() -> x; y :: atom() -> y end).(num)
          recur(num)
        num :: integer() ->
          num
      end) |> format() == "({:+, integer()} -> integer(); integer() -> integer())"

      # Untyped variable
      assert quoted_of(recur = fn
        {:+, num} ->
          recur(num)
        num ->
          num
      end) |> format() == "({:+, a} -> b; c -> c) when a: {:+, a} | b"

      assert quoted_of(recur = fn
        {:+, num} ->
          recur(num)
        {:-, num} ->
          num
      end) |> format() == "({:+, a} -> b; {:-, b} -> b) when a: {:+, a} | {:-, b}"

      # Disjoint input
      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of(recur = fn
               {:+, num} ->
                 (fn x :: atom() -> x end).(num)
                 recur(num)
               num :: integer() ->
                 num
             end)

      # Disjoint output
      assert {:error, _, {:recur_return, _, _}} =
             quoted_of(recur = fn
               {:+, num} ->
                 (fn x :: atom() -> x end).(recur(num))
               num :: integer() ->
                 num
             end)

      # Superset output
      assert {:error, _, {:recur_return, _, _}} =
             quoted_of(recur = fn
               {:+, num} ->
                 (fn true -> true end).(recur(num))
               num :: atom() ->
                 num
             end)
    end

    test "multiple variables recursive tuples" do
      # Multiple variables
      assert quoted_of(recur = fn
        {:+, left, right} ->
          {:+, recur(left), recur(right)}
        num :: integer() ->
          num
      end) |> format() == "({:+, a, b} -> {:+, c, d}; integer() -> integer()) " <>
                          "when a: integer() | {:+, a, b}, b: integer() | {:+, a, b}, " <>
                               "c: integer() | {:+, c, d}, d: integer() | {:+, c, d}"

      # # Multiple variables over multiple clauses
      assert quoted_of(recur = fn
        {:+, num} ->
          {:+, recur(num)}
        {:-, num} ->
          {:-, recur(num)}
        num :: integer() ->
          num
      end) |> format() == "({:+, a} -> {:+, b}; {:-, c} -> {:-, d}; integer() -> integer()) " <>
                          "when a: integer() | {:+, a} | {:-, c}, " <>
                               "b: integer() | {:+, b} | {:-, d}, " <>
                               "c: integer() | {:+, a} | {:-, c}, " <>
                               "d: integer() | {:+, b} | {:-, d}"

      # Multiple variables over multiple clauses with free variable
      assert quoted_of(recur = fn
        {:+, num} ->
          {:+, recur(num)}
        {:-, num} ->
          {:-, recur(num)}
        num ->
          num
      end) |> format() ==  "({:+, a} -> {:+, b}; {:-, c} -> {:-, d}; e -> e) " <>
                           "when a: {:+, a} | {:-, c} | f, " <>
                                "b: {:+, b} | {:-, d} | f, " <>
                                "c: {:+, a} | {:-, c} | g, " <>
                                "d: {:+, b} | {:-, d} | g"
    end

    test "applied on recursive tuples" do
      assert quoted_of((recur = fn
        {:+, num} ->
          recur(num)
        {:-, num} ->
          num
      end).({:+, {:-, :foo}})) |> format() == ":foo"

      assert quoted_of(fn z ->
        (recur = fn
          {:+, num} ->
            {:+, recur(num)}
          {:-, num} ->
            {:-, recur(num)}
          num :: integer() ->
            num
        end).(z)
      end) |> format() ==
             "(integer() | {:+, a} | {:-, b} -> integer() | {:+, c} | {:-, d}) " <>
             "when a: integer() | {:+, a} | {:-, b}, " <>
                  "c: integer() | {:+, c} | {:-, d}, " <>
                  "b: integer() | {:+, a} | {:-, b}, " <>
                  "d: integer() | {:+, c} | {:-, d}"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of((recur = fn
               {:+, num} ->
                 recur(num)
               {:-, num} ->
                 num
             end).({:+, {:*, 1}}))
    end

    test "unified with intersection type on recusive tuples" do
      assert quoted_of((fn x ->
        {x.({:-, :one}), x.({:+, {:-, :two}}), x.({:+, {:+, {:-, :three}}})}
      end).(recur = fn
        {:+, num} ->
          recur(num)
        {:-, num} ->
          num
      end)) |> format() == "{:one, :two, :three}"

      assert {:error, _, {:disjoint_apply, _, _, _}} =
             quoted_of((fn x ->
               x.({:+, :error})
             end).(recur = fn
               {:+, num} ->
                 recur(num)
               {:-, num} ->
                 num
             end))
    end

    test "recursive on cons" do
      # Free variables
      assert quoted_of(recur = fn
        [h | t] ->
          [h | recur(t)]
        [] ->
          []
      end) |> format() == "(cons(a, b) -> cons(a, c); empty_list() -> empty_list()) " <>
                          "when b: empty_list() | cons(a, b), " <>
                               "c: empty_list() | cons(a, c)"
    end
  end
end
