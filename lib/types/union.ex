defmodule Types.Union do
  # Types are internally always represented as unions
  # which are currently represented as lists. However,
  # this list needs to be considered an opaque type.
  #
  # ## Basic types
  #
  #   * :integer
  #
  def build(type) do
    [type]
  end
end
