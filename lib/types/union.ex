defmodule Types.Union do
  @moduledoc false

  # Functions for working with union types.
  #
  # For convenience, unions are represented internally
  # simply as lists.
  #
  # The types that compose the union:
  #
  #   {:value, val}
  #   {:fn, [{head, body, inferred}], arity}
  #   {:tuple, [arg], arity}
  #   {:var, var_ctx, var_key}
  #   :integer
  #   :atom
  #
  # In order to add a new type, we must change the following
  # functions on this module:
  #
  #   traverse
  #   quantify
  #   to_algebra
  #   is_supertype?
  #   ast_to_types
  #

  alias Inspect.Algebra, as: A

  @doc """
  Converts a union type into an iodata representation
  that can be printed.
  """
  def to_iodata(types, width \\ :infinity) do
    types
    |> to_algebra()
    |> A.format(width)
  end

  @doc """
  Converts a union type into an algebra document.
  """
  def to_algebra(types) do
    {types, %{inferred: inferred} = state} =
      types_to_algebra(types, %{counter: 0, vars: %{}, inferred: %{}})

    case inferred_to_algebra(inferred, state) do
      {:ok, guards} -> A.nest(A.glue(A.concat(types, " when"), guards), 2)
      :none -> types
    end
  end

  defp inferred_to_algebra(inferred, %{vars: vars} = state) do
    guards =
      for {key, [_ | _] = value} <- inferred do
        left = Map.fetch!(vars, key)
        {right, _} = types_to_algebra(value, state)
        A.concat(A.concat(left, ": "), right)
      end
    case guards do
      [] -> :none
      _ -> {:ok, A.fold_doc(guards, &A.glue(A.concat(&1, ","), &2))}
    end
  end

  defp types_to_algebra(types, state) do
    {types, state} =
      types
      |> Enum.sort()
      |> Enum.map_reduce(state, &type_to_algebra/2)
    {A.group(A.fold_doc(types, &A.glue(A.concat(&1, " |"), &2))), state}
  end

  defp type_to_algebra({:value, val}, state) do
    {inspect(val), state}
  end
  defp type_to_algebra({:tuple, args, _arity}, state) do
    {args, state} = args_to_algebra(args, state)
    {A.surround("{", args, "}"), state}
  end
  defp type_to_algebra({:fn, clauses, _arity}, state) do
    {clauses, state} = clauses_to_algebra(clauses, state)
    {A.surround("(", clauses, ")"), state}
  end
  defp type_to_algebra({:var, _, var_counter}, %{vars: vars, counter: counter} = state) do
    case vars do
      %{^var_counter => letter} ->
        {letter, state}
      %{} ->
        letter = counter_to_letter(counter)
        vars = Map.put(vars, var_counter, letter)
        {letter, %{state | vars: vars, counter: counter + 1}}
    end
  end

  defp type_to_algebra(:atom, state), do: {"atom()", state}
  defp type_to_algebra(:integer, state), do: {"integer()", state}

  defp args_to_algebra(args, state) do
    {args, state} = Enum.map_reduce(args, state, &types_to_algebra/2)
    {A.fold_doc(args, &A.glue(A.concat(&1, ","), &2)), state}
  end

  defp clauses_to_algebra(clauses, state) do
    {clauses, state} =
      Enum.map_reduce(clauses, state, fn {head, body, inferred}, state ->
        {head, state} = args_to_algebra(head, state)
        {body, state} = types_to_algebra(body, state)
        state = update_in(state.inferred, &Map.merge(&1, inferred))
        {A.nest(A.glue(A.concat(head, " ->"), body), 2), state}
      end)
    {A.fold_doc(clauses, &A.glue(A.concat(&1, ";"), &2)), state}
  end

  defp counter_to_letter(counter) do
    div = div(counter, 26)
    rem = rem(counter, 26)

    if div > 0 do
      <<?a + rem, counter_to_letter(div) :: binary>>
    else
      <<?a + rem>>
    end
  end

  @doc """
  Traverses types in a prewalk fashion with the
  given state and function.

  The function must return `{:ok, state}`,
  `{:replace, type, state}` or `{:union, feedback, state}`.
  """
  def traverse(types, state, fun) do
    traverse(types, [], state, fun)
  end

  defp traverse([{:fn, clauses, arity} = type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        {clauses, state} =
          Enum.map_reduce(clauses, state, fn {head, body, inferred}, state ->
            {head, state} = traverse_args(head, state, fun)
            {body, state} = traverse(body, state, fun)
            {{head, body, inferred}, state}
          end)
        traverse(types, [{:fn, clauses, arity} | acc], state, fun)
      {:replace, type, state} ->
        traverse(types, [type | acc], state, fun)
    end
  end
  defp traverse([{:tuple, args, arity} = type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        {args, state} = traverse_args(args, state, fun)
        traverse(types, [{:tuple, args, arity} | acc], state, fun)
      {:replace, type, state} ->
        traverse(types, [type | acc], state, fun)
    end
  end
  defp traverse([type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        traverse(types, [type | acc], state, fun)
      {:replace, type, state} ->
        traverse(types, [type | acc], state, fun)
      {:union, extra, state} ->
        {extra, state} = traverse(extra, [], state, fun)
        {types, state} = traverse(types, acc, state, fun)
        {union(extra, types), state}
    end
  end
  defp traverse([], acc, state, _fun) do
    {:lists.reverse(acc), state}
  end

  @doc """
  Traverses the given arguments.

  Same as `traverse/2` but goes through the list
  of arguments.
  """
  def traverse_args(args, state, fun) do
    Enum.map_reduce(args, state, &traverse(&1, [], &2, fun))
  end

  @doc """
  Computes the union of two union types.
  """
  def union(lefties, []), do: lefties
  def union([], righties), do: righties
  def union([single], types), do: union_add(single, types, [])
  def union(types, [single]), do: union_add(single, types, [])
  def union(lefties, righties), do: union(lefties, righties, [])

  defp union([left | lefties], righties, acc) do
    union(left, righties, lefties, [], acc)
  end
  defp union([], righties, acc) do
    acc ++ righties
  end

  defp union(left, [right | righties], temp_left, temp_right, acc) do
    case qualify(left, right) do
      :disjoint -> union(left, righties, temp_left, [right | temp_right], acc)
      :subset -> union(temp_left, temp_right ++ [right | righties], acc)
      _ -> union(temp_left, temp_right ++ righties, [left | acc])
    end
  end
  defp union(left, [], temp_left, temp_right, acc) do
    union(temp_left, temp_right, [left | acc])
  end

  defp union_add(left, [right | righties], acc) do
    case qualify(left, right) do
      :disjoint -> union_add(left, righties, [right | acc])
      :subset -> acc ++ [right | righties]
      _ -> acc ++ [left | righties]
    end
  end
  defp union_add(left, [], acc) do
    [left | acc]
  end

  @doc """
  Qualifies two non-union types.

  This is the "heart" of union types as it is the part of
  the code that knows the relationship between types and
  therefore how to compute the union between them.

  In other words, this is part that handles subtyping,
  given union is only complicated if one type inhabits
  another.

  It returns one of :disjoint, :equal, :subset or :superset.
  """
  def qualify(left, right) do
    qualify(left, right, %{}, %{}) |> elem(0)
  end

  defp qualify(type, type, lvars, rvars), do: {:equal, lvars, rvars}

  defp qualify({:var, _, left_counter} = left, {:var, _, right_counter} = right, lvars, rvars) do
    left_value = Map.get(lvars, left_counter, [right])
    right_value = Map.get(rvars, right_counter, [left])
    if left_value == right_value do
      {:equal,
       Map.put(lvars, left_counter, left_value),
       Map.put(rvars, right_counter, right_value)}
    else
      {:disjoint, lvars, rvars}
    end
  end

  defp qualify(:atom, {:value, atom}, lvars, rvars) when is_atom(atom), do: {:superset, lvars, rvars}
  defp qualify({:value, atom}, :atom, lvars, rvars) when is_atom(atom), do: {:subset, lvars, rvars}

  defp qualify({:tuple, args1, arity}, {:tuple, args2, arity}, lvars, rvars) do
    qualify_args(args1, args2, lvars, rvars, :equal)
  end

  defp qualify(_, _, lvars, rvars), do: {:disjoint, lvars, rvars}

  @doc """
  Qualifies multiple arguments.

  The same as `qualify/2` but for arguments.
  """
  def qualify_args(left, right) do
    qualify_args(left, right, %{}, %{}, :equal) |> elem(0)
  end

  defp qualify_args([left | lefties], [right | righties], lvars, rvars, :equal) do
    case qualify_look_ahead(:lists.sort(left), :lists.sort(right), lvars, rvars) do
      {:equal, lvars, rvars} -> qualify_args(lefties, righties, lvars, rvars, :equal)
      {kind, lvars, rvars} -> qualify_args([left | lefties], [right | righties], lvars, rvars, kind)
    end
  end
  defp qualify_args([left | lefties], [right | righties], lvars, rvars, :superset) do
    case qualify_set(left, right, lvars, rvars, :superset) do
      {lvars, rvars} -> qualify_args(lefties, righties, lvars, rvars, :superset)
      :error -> {:disjoint, lvars, rvars}
    end
  end
  defp qualify_args([left | lefties], [right | righties], lvars, rvars, :subset) do
    case qualify_set(left, right, lvars, rvars, :subset) do
      {lvars, rvars} -> qualify_args(lefties, righties, lvars, rvars, :subset)
      :error -> {:disjoint, lvars, rvars}
    end
  end
  defp qualify_args(_, _, lvars, rvars, :disjoint) do
    {:disjoint, lvars, rvars}
  end
  defp qualify_args([], [], lvars, rvars, kind) do
    {kind, lvars, rvars}
  end

  defp qualify_look_ahead([left | lefties], [right | righties], lvars, rvars) do
    case qualify(left, right, lvars, rvars) do
      {:equal, lvars, rvars} -> qualify_look_ahead(lefties, righties, lvars, rvars)
      {kind, lvars, rvars} -> {kind, lvars, rvars}
    end
  end
  defp qualify_look_ahead([], [], lvars, rvars), do: {:equal, lvars, rvars}
  defp qualify_look_ahead([], _, lvars, rvars), do: {:subset, lvars, rvars}
  defp qualify_look_ahead(_, [], lvars, rvars), do: {:superset, lvars, rvars}

  defp qualify_set(lefties, [right | righties], lvars, rvars, kind) do
    qualify_set(lefties, right, lefties, righties, lvars, rvars, kind)
  end
  defp qualify_set(_lefties, [], lvars, rvars, _kind) do
    {lvars, rvars}
  end

  defp qualify_set([type | types], right, lefties, righties, lvars, rvars, kind) do
    case qualify(type, right, lvars, rvars) do
      {^kind, lvars, rvars} -> qualify_set(lefties, righties, lvars, rvars, kind)
      {:equal, lvars, rvars} -> qualify_set(lefties, righties, lvars, rvars, kind)
      {_, _} -> qualify_set(types, right, lefties, righties, lvars, rvars, kind)
    end
  end
  defp qualify_set([], _right, _lefties, _righties, _lvars, _rvars, _kind) do
    :error
  end

  @doc """
  Returns true if the given union can be supertype of another type.

  By default, any union with more than one element is a supertype
  of its subsets. However, a union with one element can also be
  a supertype if the element is a supertype. For example, `:atom`
  is a supertype of the values `:foo`, `:bar`, etc.

  In other words, for unions with one element, this function checks
  if there is some type in which `qualify(element, some_type)`
  returns true.
  """
  def supertype?([type]), do: each_supertype?(type)
  def supertype?(types) when is_list(types), do: true

  defp each_supertype?({:tuple, args, _}) do
    Enum.any?(args, &supertype?/1)
  end
  defp each_supertype?({:fn, clauses, _}) do
    Enum.any?(clauses, fn {head, body, _} ->
      Enum.any?(head, &supertype?/1) or supertype?(body)
    end)
  end

  defp each_supertype?(:atom), do: true
  defp each_supertype?(_), do: false
end
