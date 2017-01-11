defmodule Types do
  @moduledoc """
  Type system for Elixir.
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
