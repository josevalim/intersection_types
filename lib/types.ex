defmodule Types do
  @moduledoc """
  A type system for Elixir.

  The goal of the type system is to integrate well with
  current Elixir code and idioms by relying on atoms,
  tuples, lists and other regular Elixir data structures.
  This means a function such as `File.read/1` can be typed
  as:

      def read(binary()) :: {:ok, binary()} | {:error, atom()}

  The type system is based on union and intersection types.

  The concept of union is quite simple. For example, if an argument
  can be either an integer or an atom, we can express it as:

      integer() | atom()

  The concept of intersection is a bit more interesting. Generally
  speaking, intersections do not make much sense, for example,
  the intersection between the types `integer()` and `atom()` is
  empty. The intersection between `atom()` and `:foo` is the atom
  `:foo` itself. However, the concept of intersection is quite
  interesting for functions, as they allow us to express functions
  with multiple closes, which is very common in Elixir.

  For example, a function that receives an integer and returns an
  integer would inhabit the type `(integer() -> integer())`. One
  of such functions would be:

      fn x :: integer() -> -x end

  Another of such functions is:

      fn x :: integer() -> -x
         x :: boolean() -> not x end

  Even though the function above has multiple clauses, it is still
  capable of receiving an integer and returning another integer.

  Similar, a funciton that receives a boolean and returns a boolean
  would inhabit the type `(boolean() -> boolean())`. One of such
  functions would be:

      fn x :: boolean() -> -x end

  Another of such functions is:

      fn x :: integer() -> -x
         x :: boolean() -> not x end

  As you can see, the function with two clauses above inhabits both
  the type `(integer() -> integer())` and `(boolean() -> boolean())`.
  This means that, if there is a function that may receive either
  an integer or a boolean as argument, it requires both types, which
  means that function exists in the intersection between the types
  `(integer() -> integer())` and `(boolean() -> boolean())`.

  In the type system, we simply write that as a type with multiple
  clauses:

      (integer() -> integer(); boolean() -> boolean())

  The intersection types literature has a bunch of interesting examples
  where intersection types can be used to infer the types where classic
  Hindley Milner type systems wouldn't. For example:

      fn x -> {x.(0), x.(:foo)} end

  has the type:

      ((0 -> a; :foo -> b) -> {a, b})

  Elixir currently implements a subset of rank 2 intersection types,
  as it only allows intersections that can be expressed as function
  clauses and in a way there is no dependency between those multiple
  clauses.

  ## Literature

  We will now describe the literature that has been relevant to the
  current implementation.

  ### Introductory

  Those references contain introductory material on type system for
  those not familiar with the concepts, nomenclature and implementation:

    * Types and Programming Languages, 3rd edition (Benjamin C. Pierce)

    * On Understanding Types, Data Abstraction, and Polymorphism (Luca Cardelli)

    * How OCaml type checker works (Oleg Kiselyo)

  ### Intersection types

  The following papers explore the ides behind intersection types.

    * What are principal typings and what are they good for? (Trevor Jim)
      This paper describes rank 2 intersection type systems. Elixir
      implements a subset of the polar type system where intersections
      can only be expressed as independent function clauses. This means
      we can't infer the type for `x.(x)`, as it has the type `(a ^ (a -> b))`
      which is the intersection between a type variable and a function.
      Similarly, for `x.(x.(y))` we infer the same type as in a Hindley-Milner
      type system as otherwise it would have the type `(a -> b) ^ (b -> c)`
      which causes dependency between clauses. However, for expressions
      such as `{x.(:foo), x.(:bar)}`, we infer the proper intersection
      type `(:bar -> a) ^ (:foo -> b)` expressed as `(:bar -> a; :foo -> b)`.

  ### Erlang papers

  The following papers are important because they describe other type
  systems implemented for Erlang:

    * Practical Type Inference Based on Success Typings (Tobias Lindahl, Konstantinos Sagonas)
      The reference paper on Dialyzer and its trade-offs

  """

  ## Patterns
  # 1. adding types/patterns to receive
  # 2. mixing typed with non-typed
  # 3. the cost of having duplicate syntax

  ## Function annotations
  # 1. Annotations may have multiple clauses. Each clause must have at least one matching implementation.
  # 2. Should we force a explicit type on fn true -> true; _ -> x end? If so, what to do on catch all?

  ## Guards
  # Must perform exhaustion check based on patterns
  # Must perform exhaustion check for base types (integers, atoms, floats, etc)
  # Pattern matches {a, a} also require an exaustion check

  # TODO: Use inline_list_funcs for performance.

  ## Forbidden
  # [foo | bar] (developers must use cons(...) to avoid ambiguity)

  ## Built-in Patterns
  # pattern number() :: integer() | float()

  ## Built-in Types
  # type list(a) :: empty_list() | cons(a, list(a))
  # type improper_list(a) :: empty_list() | cons(a, list(a) | a)

  ## Implemented Patterns
  # pattern boolean() :: true | false
  # pattern atom()
  # pattern integer()

  ## Literals
  # integer
  # atom
  # tuples
end
