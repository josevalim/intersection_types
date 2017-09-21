defmodule Types.Union do
  # Types are internally always represented as unions
  # which are currently represented as lists. However,
  # this list needs to be considered an opaque type.
  #
  # ## Built-in types
  #
  #   * :integer
  #   * :atom
  #   * {:atom, atom}
  #
  # ## Adding a new type
  #
  # Adding a new type requires changing the given functions.
  #
  #   * to_algebra
  #

  alias Inspect.Algebra, as: A

  @doc """
  Converts a union type into an iodata representation
  that can be printed.
  """
  def to_iodata(union, width \\ :infinity) do
    union
    |> to_algebra()
    |> A.format(width)
  end

  @doc """
  Converts a union type into an algebra document.
  """
  def to_algebra(union) do
    union_to_algebra(union)
  end

  defp union_to_algebra(union) do
    union
    |> :lists.usort()
    |> Enum.map(&type_to_algebra/1)
    |> A.fold_doc(&A.glue(A.concat(&1, " |"), &2))
    |> A.group()
  end

  defp type_to_algebra({:atom, atom}), do: inspect(atom)
  defp type_to_algebra(:atom), do: "atom()"
  defp type_to_algebra(:integer), do: "integer()"

  @doc """
  Builds a union with the given type.
  """
  def build(type) do
    [type]
  end
end
