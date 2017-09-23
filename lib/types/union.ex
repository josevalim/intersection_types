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
  #   * from_ast
  #   * qualify
  #

  alias Inspect.Algebra, as: A

  @doc """
  Converts the given AST to type.
  """
  def from_ast({:|, _, [left, right]}) do
    with {:ok, left} <- from_ast(left),
         {:ok, right} <- from_ast(right) do
      {:ok, merge(left, right)}
    end
  end
  def from_ast({:boolean, _, []}) do
    {:ok, [{:atom, false}, {:atom, true}]}
  end
  def from_ast({:integer, _, []}) do
    {:ok, [:integer]}
  end
  def from_ast({:atom, _, []}) do
    {:ok, [:atom]}
  end
  def from_ast(value) when is_atom(value) do
    {:ok, [{:atom, value}]}
  end
  def from_ast(other) do
    {:error, other}
  end

  @doc """
  Qualifies the type on the left against the type on the right.
  """
  def qualify(type, type), do: :equal
  def qualify(:atom, {:atom, _}), do: :superset
  def qualify({:atom, _}, :atom), do: :subset
  def qualify(_left, _right), do: :disjoint

  @doc """
  Merges two unions.
  """
  def merge(left, right) do
    merge(left, right, [])
  end

  defp merge([left | lefties], righties, acc) do
    merge(left, lefties, righties, acc, [])
  end
  defp merge([], righties, acc) do
    righties ++ acc
  end

  defp merge(left, lefties, [right | righties], left_acc, right_acc) do
    case qualify(left, right) do
      :superset -> merge(left, lefties, righties, left_acc, right_acc)
      :equal -> merge(left, lefties, righties, left_acc, right_acc)
      :subset -> merge(lefties, right_acc ++ [right | righties], left_acc)
      :disjoint -> merge(left, lefties, righties, left_acc, [right | right_acc])
    end
  end

  defp merge(left, next_lefties, [], left_acc, right_acc) do
    merge(next_lefties, right_acc, [left | left_acc])
  end

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
