defmodule Types.Union do
  @moduledoc false

  # Functions for working with union types.
  #
  # For convenience, unions are represented internally
  # simply as lists.
  #
  # The types that compose the union:
  #
  #   {:atom, val}
  #   {:fn, [{head, body}], inferred, arity}
  #   {:tuple, [arg], arity}
  #   {:cons, left, right}
  #   {:var, var_ctx, var_key}
  #   :integer
  #   :atom
  #
  # In order to add a new type, we must change the following
  # functions on this module:
  #
  #   traverse
  #   reduce
  #   qualify
  #   to_algebra
  #   ast_to_types
  #   simplify
  #

  # TODO
  #
  # ## Function type parsing.
  #
  # Variables in functions apply to the most outer level the
  # variable exists. Variables on the right side must appear
  # on the left side before.
  #
  # Another restriction is that multiple clauses can only
  # share variables in the body, however this restriction is
  # broken with recursive functions. TODO: We need to carefully
  # consider how this impacts the code and if we are going to
  # allow users to express those types. Maybe it should only
  # be possible if the recursion is at the top level function.
  #
  # ## Function code parsing.
  #
  # What is the type of:
  #
  #     def same?(a, a), do: true
  #     def same?(_a, _b), do: false
  #
  # Note it is not (a, a -> true; a, b -> false) because variables
  # in types talk about types inhabitation. For example, the values
  # 0 and 1 will match (a, a -> true) because they are both integers.
  #
  # Also note that, when applying to same?(x, y), there is no way
  # we can infer x and y are of the same type, especially because
  # the second clause will give them the distinct and generic types
  # a and b.
  #
  # Also note that this issue generally applies to any guard that
  # may be added to the code.
  #
  # One solution to this problem is to always translate those cases
  # to an applied case:
  #
  #     def same?(x, y) do
  #       (fn
  #         {a, a} -> true
  #         {a, b} -> false
  #       end).({x, y})
  #     end
  #
  # where any runtime condition (such as matching vars and guards)
  # imply the clause never matches fully and we need to move to
  # exaust further clauses.

  alias Inspect.Algebra, as: A

  @doc """
  Converts a union type into an iodata representation
  that can be printed.
  """
  @spec to_iodata({:ok, var} | {:ok, integer()}, {:error, var} | atom()) :: atom when var: var
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
    {guards, _} =
      Enum.flat_map_reduce inferred, state, fn
        {key, [_ | _] = value}, state ->
          left = Map.fetch!(vars, key)
          {right, state} = types_to_algebra(value, state)
          {[A.concat(A.concat(left, ": "), right)], state}
        {_, []}, state ->
          {[], state}
      end

    case guards do
      [] -> :none
      _ -> {:ok, A.fold_doc(guards, &A.glue(A.concat(&1, ","), &2))}
    end
  end

  defp types_to_algebra(types, state) do
    {types, state} =
      types
      |> :lists.usort()
      |> Enum.map_reduce(state, &type_to_algebra/2)
    {A.group(A.fold_doc(types, &A.glue(A.concat(&1, " |"), &2))), state}
  end

  defp type_to_algebra({:atom, val}, state) do
    {inspect(val), state}
  end
  defp type_to_algebra({:cons, left, right}, state) do
    {args, state} = args_to_algebra([left, right], state)
    {A.surround("cons(", args, ")"), state}
  end
  defp type_to_algebra({:tuple, args, _arity}, state) do
    {args, state} = args_to_algebra(args, state)
    {A.surround("{", args, "}"), state}
  end
  defp type_to_algebra({:fn, clauses, inferred, _arity}, state) do
    state = update_in(state.inferred, &Map.merge(&1, inferred))
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
  defp type_to_algebra(:empty_list, state), do: {"empty_list()", state}

  defp args_to_algebra(args, state) do
    {args, state} = Enum.map_reduce(args, state, &type_to_algebra/2)
    {A.fold_doc(args, &A.glue(A.concat(&1, ","), &2)), state}
  end

  defp head_to_algebra([], state) do
    {"", state}
  end
  defp head_to_algebra(head, state) do
    {head, state} = Enum.map_reduce(head, state, &types_to_algebra/2)
    doc = A.fold_doc(head, &A.glue(A.concat(&1, ","), &2))
    {A.concat(doc, " "), state}
  end

  defp clauses_to_algebra(clauses, state) do
    {clauses, state} =
      Enum.map_reduce(clauses, state, fn {head, body}, state ->
        {head, state} = head_to_algebra(head, state)
        {body, state} = types_to_algebra(body, state)
        {A.nest(A.glue(A.concat(head, "->"), body), 2), state}
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
  Checks if two unions are the same.
  """
  def same?(old, new) do
    old == new or same_traverse?(:lists.sort(old), :lists.sort(new))
  end

  @doc """
  Check if two args (list of unions) are the same.
  """
  def same_args?(left, right)
  def same_args?([left_arg | left], [right_arg | right]) do
    same?(left_arg, right_arg) and same_args?(left, right)
  end
  def same_args?([], []), do: true
  def same_args?(_, _), do: false

  defp same_traverse?([type | left], [type | right]) do
    same_traverse?(left, right)
  end
  defp same_traverse?([{:fn, left_head, left_body, arity} | left],
                      [{:fn, right_head, right_body, arity} | right]) do
    same_args?(left_head, right_head) and
      same?(left_body, right_body) and
      same_traverse?(left, right)
  end
  defp same_traverse?([], []) do
    true
  end
  defp same_traverse?(_, _) do
    false
  end

  @doc """
  Converts the given type AST to its inner type.
  """
  # TODO: Once we support variables and functions
  # and so on here, we need to make sure those
  # features are not accessible from :: patterns
  # on the actual code.
  def ast_to_types(ast)

  def ast_to_types({:|, _, [left, right]}) do
    with {:ok, left} <- ast_to_types(left),
         {:ok, right} <- ast_to_types(right) do
      {:ok, left ++ right}
    end
  end
  def ast_to_types({:boolean, _, []}) do
    {:ok, [{:atom, true}, {:atom, false}]}
  end
  def ast_to_types({:integer, _, []}) do
    {:ok, [:integer]}
  end
  def ast_to_types({:atom, _, []}) do
    {:ok, [:atom]}
  end
  def ast_to_types({:empty_list, _, []}) do
    {:ok, [:empty_list]}
  end
  def ast_to_types({:cons, _, [left, right]}) do
    permute_args_to_types([left, right], fn [left, right], _arity ->
      {:cons, left, right}
    end)
  end
  def ast_to_types(value) when is_atom(value) do
    {:ok, [{:atom, value}]}
  end
  def ast_to_types({left, right}) do
    permute_args_to_types([left, right], fn args, arity ->
      {:tuple, args, arity}
    end)
  end
  def ast_to_types({:{}, _, args}) do
    permute_args_to_types(args, fn args, arity ->
      {:tuple, args, arity}
    end)
  end
  def ast_to_types(other) do
    {:error, {:invalid_type, other}}
  end

  defp permute_args_to_types(args, callback) do
    permute_args_to_types(args, [], 0, callback)
  end

  defp permute_args_to_types([arg | args], acc, arity, callback) do
    with {:ok, types} <- ast_to_types(arg) do
      permute_args_to_types(args, [types | acc], arity + 1, callback)
    end
  end
  defp permute_args_to_types([], acc, arity, callback) do
    {:ok, permute_args(:lists.reverse(acc), fn arg -> callback.(arg, arity) end)}
  end

  @doc """
  Permutes the given arguments.

  Calling the callback with each permutation and the arity.
  """
  def permute_args(args, callback) do
    permute_args(args, [], callback, [])
  end

  defp permute_args([pivot | pivots], call, callback, acc) do
    permute_args(pivot, pivots, call, callback, acc)
  end
  defp permute_args([], call, callback, acc) do
    [callback.(:lists.reverse(call)) | acc]
  end

  defp permute_args([arg | args], pivots, call, callback, acc) do
    acc = permute_args(pivots, [arg | call], callback, acc)
    permute_args(args, pivots, call, callback, acc)
  end
  defp permute_args([], _pivots, _call, _callback, acc) do
    acc
  end

  @doc """
  Reduces over leaf types.
  """
  def reduce(types, state, fun) do
    Enum.reduce(types, state, &reduce_each(&1, &2, fun))
  end

  defp reduce_each({:fn, clauses, _inferred, _arity}, acc, fun) do
    Enum.reduce(clauses, acc, fn {head, body}, acc ->
      acc = reduce_args(head, acc, fun)
      acc = reduce(body, acc, fun)
      acc
    end)
  end
  defp reduce_each({:cons, left, right}, acc, fun) do
    acc = reduce_each(left, acc, fun)
    acc = reduce_each(right, acc, fun)
    acc
  end
  defp reduce_each({:tuple, args, _arity}, acc, fun) do
    reduce(args, acc, fun)
  end
  defp reduce_each(type, acc, fun) do
    fun.(type, acc)
  end

  @doc """
  Reducers over all leaf types.

  Same as `reduce/3` but goes through the list of arguments.
  """
  def reduce_args(args, acc, fun) do
    Enum.reduce(args, acc, &reduce(&1, &2, fun))
  end

  @doc """
  Traverses types in a prewalk fashion with the
  given state and function.

  The function must return `{:ok, state}` or
  `{:replace, replace, state}`.
  """
  def traverse(types, state, fun) do
    traverse(types, [], state, fun)
  end

  defp traverse([{:fn, clauses, inferred, arity} = type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        {clauses, state} =
          Enum.map_reduce(clauses, state, fn {head, body}, state ->
            {head, state} = traverse_args(head, state, fun)
            {body, state} = traverse(body, state, fun)
            {{head, body}, state}
          end)
        traverse(types, [{:fn, clauses, inferred, arity} | acc], state, fun)
      {:replace, replace, state} ->
        traverse(types, replace ++ acc, state, fun)
    end
  end
  defp traverse([{:cons, left, right} = type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        {conses, state} =
          traverse_and_permute([left, right], state, fun, fn
            [left, right] -> {:cons, left, right}
          end)
        traverse(types, conses ++ acc, state, fun)
      {:replace, replace, state} ->
        traverse(types, replace ++ acc, state, fun)
    end
  end
  defp traverse([{:tuple, args, arity} = type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        {tuples, state} = traverse_and_permute(args, state, fun, &{:tuple, &1, arity})
        traverse(types, tuples ++ acc, state, fun)
      {:replace, replace, state} ->
        traverse(types, replace ++ acc, state, fun)
    end
  end
  defp traverse([type | types], acc, state, fun) do
    case fun.(type, state) do
      {:ok, state} ->
        traverse(types, [type | acc], state, fun)
      {:replace, replace, state} ->
        traverse(types, replace ++ acc, state, fun)
    end
  end
  defp traverse([], acc, state, _fun) do
    {:lists.reverse(acc), state}
  end

  defp traverse_and_permute(args, state, fun, callback) do
    case traverse_with_single_check(args, [], [], state, fun) do
      {:single, args, state} -> {[callback.(args)], state}
      {:permute, args, state} -> {permute_args(args, callback), state}
    end
  end

  # This function is an optimization so we don't permute unless we have to.
  defp traverse_with_single_check([type | types], acc, single, state, fun) do
    case traverse([type], [], state, fun) do
      {[type] = new, state} when is_list(single) ->
        traverse_with_single_check(types, [new | acc], [type | single], state, fun)
      {new, state} ->
        traverse_with_single_check(types, [new | acc], false, state, fun)
    end
  end
  defp traverse_with_single_check([], _acc, single, state, _fun) when is_list(single) do
    {:single, :lists.reverse(single), state}
  end
  defp traverse_with_single_check([], acc, _single, state, _fun) do
    {:permute, :lists.reverse(acc), state}
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
      _ -> union(left, righties, temp_left, temp_right, acc)
    end
  end
  defp union(left, [], temp_left, temp_right, acc) do
    union(temp_left, temp_right, [left | acc])
  end

  defp union_add(left, [right | righties], acc) do
    case qualify(left, right) do
      :disjoint -> union_add(left, righties, [right | acc])
      :subset -> acc ++ [right | righties]
      _ -> union_add(left, righties, acc)
    end
  end
  defp union_add(left, [], acc) do
    [left | acc]
  end

  @doc """
  Qualifies two non-union types.

  This is the code responsible for handling subtypes,
  such as {:atom, :foo} being a subtype of :atom.

  It returns one of :disjoint, :equal, :subset or :superset.
  """
  def qualify(left, right)

  def qualify(type, type), do: :equal

  def qualify(:atom, {:atom, atom}) when is_atom(atom), do: :superset
  def qualify({:atom, atom}, :atom) when is_atom(atom), do: :subset

  def qualify({:tuple, args1, arity}, {:tuple, args2, arity}) do
    qualify_paired(args1, args2, :equal)
  end

  def qualify({:cons, left1, right1}, {:cons, left2, right2}) do
    qualify_paired([left1, right1], [left2, right2], :equal)
  end

  def qualify(_, _), do: :disjoint

  defp qualify_paired([left | lefties], [right | righties], :equal) do
    case qualify(left, right) do
      :disjoint -> :disjoint
      kind -> qualify_paired(lefties, righties, kind)
    end
  end

  defp qualify_paired([left | lefties], [right | righties], kind) do
    case qualify(left, right) do
      ^kind -> qualify_paired(lefties, righties, kind)
      :equal -> qualify_paired(lefties, righties, kind)
      _ -> :disjoint
    end
  end

  defp qualify_paired([], [], kind) do
    kind
  end

  @doc """
  Returns true if the given union can be supertype of another type.

  By default, any union with more than one element is a supertype
  of its subsets. However, a union with one element can also be
  a supertype if the element is a supertype. For example, `atom()`
  is a supertype of the values `:foo`, `:bar`, etc.

  If inferred is given, variables are expanded and are marked as
  supertype based on its expansion. Without inferred, variables are
  not considered supertypes.
  """
  def supertype?([type], inferred) do
    reduce([type], false, fn
      {:var, _, counter}, acc when is_map(inferred) ->
        acc or supertype?(Map.get(inferred, counter, []), Map.delete(inferred, counter))
      :atom, _acc ->
        true
      _, acc ->
        acc
    end)
  end
  def supertype?(types, _inferred) when is_list(types) do
    true
  end

  @doc """
  Simplifies unions by merging distributed unions over
  tuples and cons, and merging types into aliases.

  This function should only be used for pretty-printing since
  it returns aliased types and unions are converted to
  `{:union, [type]}`.

  ## Examples

      iex> simplify([{:tuple, [:atom], 1}, {:tuple, [:integer], 1}])
      {:union, [{:tuple, [{:union, [:atom, :integer]}], 1}]}

      iex> simplify([{:atom, false}, {:atom, true}])
      {:union, [:boolean]}

      iex> simplify([:atom, :integer])
      {:union, [:integer, :atom]}
  """
  def simplify(types) when is_list(types) do
    types
    |> undistribute_union([])
    |> traverse_aliases()
  end

  # Merges predefined aliases so that true | false => boolean()
  defp traverse_aliases({:union, types}) do
    types = merge_aliases(types)
    {:union, traverse(types, :ok, &traverse_aliases/2) |> elem(0)}
  end
  defp traverse_aliases({:union, _} = union, acc) do
    {:replace, [traverse_aliases(union)], acc}
  end
  defp traverse_aliases(_, acc) do
    {:ok, acc}
  end

  def merge_aliases(types) do
    Enum.reduce(types, types, &merge_alias/2)
  end

  defp merge_alias({:atom, false} = type, types) do
    case pop_type(types, {:atom, true}) do
      {:ok, types} -> [:boolean | List.delete(types, type)]
      :error -> types
    end
  end
  defp merge_alias(_, types) do
    types
  end

  defp pop_type([], _type), do: :error
  defp pop_type(types, type) do
    case Enum.split_while(types, & &1 != type) do
      {_pre, []} -> :error
      {pre, [_ | pos]} -> {:ok, pre ++ pos}
    end
  end

  # Undistributes a union so that {x} | {y} => {x | y}
  defp undistribute_union([first | rest], acc) do
    {merge, keep} = Enum.split_with(rest, &distributed?(first, &1))
    if merge == [] do
      undistribute_union(keep, [undistribute_fn(first) | acc])
    else
      undistribute_union(keep, [merge_union([first | merge]) | acc])
    end
  end
  defp undistribute_union([], acc) do
    {:union, acc}
  end

  defp undistribute_fn({:fn, clauses, inferred, arity}) do
    clauses = Enum.map(clauses, fn {head, body} ->
      head = Enum.map(head, &[undistribute_union(&1, [])])
      body = [undistribute_union(body, [])]
      {head, body}
    end)
    {:fn, clauses, inferred, arity}
  end
  defp undistribute_fn(other) do
    other
  end

  defp distributed?({:cons, left, _}, {:cons, left, _}), do: true
  defp distributed?({:cons, _, right}, {:cons, _, right}), do: true
  defp distributed?({:tuple, left, arity}, {:tuple, right, arity}) do
    # Check if the tuples only differ in one element
    zipped = Enum.zip(left, right)
    equal_elems = Enum.count(zipped, fn {left, right} -> left == right end)
    arity - equal_elems == 1
  end
  defp distributed?(_, _), do: false

  # Merges a union of cons or tuples into a single cons or tuple where
  # the union is moved inside the elements
  defp merge_union([{:cons, _, _} | _] = union) do
    {left, right} =
      Enum.reduce(union, {[], []}, fn {:cons, left, right}, {left_union, right_union} ->
        {union_add(left, left_union, []), union_add(right, right_union, [])}
      end)
    {:cons, undistribute_union(left, []), undistribute_union(right, [])}
  end
  defp merge_union([{:tuple, args, arity} | union]) do
    args = Enum.map(args, &[&1])
    args = Enum.reduce(union, args, fn {:tuple, args, ^arity}, acc ->
      Enum.map(Enum.zip(args, acc), fn {left, union} -> union_add(left, union, []) end)
    end)
    {:tuple, Enum.map(args, &undistribute_union(&1, [])), arity}
  end
end
