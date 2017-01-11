defmodule Types.Checker do
  @moduledoc false

  alias Types.Union

  @doc """
  Converts the given type AST to its inner type.
  """
  # TODO: Currently this is sharing code with of/2
  # but I don't believe it should in the long term
  # as they will likely end-up with different logic
  # regarding how literals are parsed. When that
  # happens, this should be moved to the union module.
  def ast_to_types(ast, state \\ state())

  def ast_to_types({:boolean, _, []}, state) do
    ok([{:value, true}, {:value, false}], state)
  end
  def ast_to_types({:integer, _, []}, state) do
    ok([:integer], state)
  end
  def ast_to_types({:atom, _, []}, state) do
    ok([:atom], state)
  end
  def ast_to_types(other, state) do
    literal(other, state, &ast_to_types/2)
  end

  @doc """
  Unifies the types on left and right.

  All of the types on the right must match at least one type
  on the left. Internally we keep track of the following variables:

    * vars - variables already inferred.
    * type_vars - variables inferred for each type on the right. Starts as vars.
    * acc_vars - variables inferred for from the caller loop.

  Any variable found during unification must intersect with
  whatever variable found on the proper `*vars`. For example,
  if a variable is found on the right side, it must intersect
  with any inferred value in `vars`.

  Unification works by pinning each specific type on the `right`
  and finding a `left` type that matches. If such type exists
  and variables are involved, `type_*vars` will be properly
  updated and be set as the main `*vars` once we move to the
  next type.

  `acc_vars` is only updated by this function, never read.
  `acc_vars` keeps inference information across the caller
  loop. For example, if we are unifying against multiple clauses,
  `acc_vars` will keep unifying information for all clauses.
  """
  # TODO: Include error reason every time unification fails.
  def unify(left, right, keep, vars, acc_vars) do
    unify(left, right, keep, vars, vars, acc_vars)
  end

  defp unify(left, right, keep, vars, type_vars, acc_vars) do
    unify(left, unify_counter(right, 0), keep, vars, type_vars, acc_vars, %{})
  end

  defp unify([left | lefties], righties, keep, vars, type_vars, acc_vars, unmatched) do
    unify(left, righties, keep, vars, type_vars, acc_vars, lefties, righties, unmatched)
  end
  defp unify([], righties, _keep, _vars, type_vars, acc_vars, unmatched) do
    {kind, matched} = unify_matched(righties, unmatched, :match, [])
    {kind, matched, type_vars, acc_vars}
  end

  defp unify(left, [{key, type} | types], keep, vars, type_vars, acc_vars,
             lefties, righties, unmatched) do
    case unify_each(left, type, keep, vars, type_vars, acc_vars) do
      {:match, type_vars, acc_vars} ->
        unify(left, types, keep, vars, type_vars, acc_vars,
              lefties, righties, Map.put(unmatched, key, {:match, type}))
      {:subset, type, type_vars, acc_vars} ->
        unify(left, types, keep, vars, type_vars, acc_vars,
              lefties, righties, Map.put_new(unmatched, key, {:subset, type}))
      :disjoint ->
        unify(left, types, keep, vars, type_vars, acc_vars,
              lefties, righties, unmatched)
    end
  end
  defp unify(_left, [], keep, vars, type_vars, acc_vars, lefties, righties, unmatched) do
    vars = Map.merge(vars, Map.take(type_vars, keep))
    unify(lefties, righties, keep, vars, type_vars, acc_vars, unmatched)
  end

  defp unify_counter([type | types], counter) do
    [{counter, type} | unify_counter(types, counter + 1)]
  end
  defp unify_counter([], _counter) do
    []
  end

  defp unify_matched([{key, _} | righties], unmatched, kind, matched) do
    case Map.fetch(unmatched, key) do
      {:ok, {new_kind, new_value}} ->
        unify_matched(righties, unmatched, unify_min(kind, new_kind), [new_value | matched])
      :error ->
        unify_matched(righties, unmatched, :disjoint, matched)
    end
  end
  defp unify_matched([], _unmatched, kind, matched) do
    {kind, :lists.reverse(matched)}
  end

  defp unify_min(:disjoint, _), do: :disjoint
  defp unify_min(_, :disjoint), do: :disjoint
  defp unify_min(:subset, _), do: :subset
  defp unify_min(_, :subset), do: :subset
  defp unify_min(_, _), do: :match

  defp unify_each(type, type, _keep, _vars, type_vars, acc_vars) do
    {:match, type_vars, acc_vars}
  end

  defp unify_each({:var, _, key1}, {:var, _, key2} = right, keep, vars, type_vars, acc_vars) do
    case {Map.get(vars, key1, []), Map.get(vars, key2, [])} do
      {[], _} ->
        type_vars =
          type_vars
          |> Map.update(key1, [right], &Union.union(&1, [right]))
        acc_vars =
          acc_vars
          |> Map.put(key2, Map.get(type_vars, key2, []))
          |> Map.update(key1, [right], &Union.union(&1, [right]))
        {:match, type_vars, acc_vars}
      {left_value, []} ->
        type_vars =
          type_vars
          |> Map.update(key2, left_value, &Union.union(&1, left_value))
          |> Map.update(key1, [right], &Union.union(&1 -- left_value, [right]))
        acc_vars =
          acc_vars
          |> Map.update(key2, left_value, &Union.union(&1, left_value))
          |> Map.update(key1, [right], &Union.union(&1 -- left_value, [right]))
        {:match, type_vars, acc_vars}
      {left_value, right_value} ->
        with {_, [_ | _] = match, type_vars, acc_vars} <-
               unify(left_value, right_value, keep, vars, type_vars, acc_vars) do
          type_vars =
            type_vars
            |> Map.update(key1, match, &Union.union(&1 -- left_value, match))
            |> Map.update(key2, match, &Union.union(&1 -- right_value, match))
          acc_vars =
            acc_vars
            |> Map.update(key1, match, &Union.union(&1 -- left_value, match))
            |> Map.update(key2, match, &Union.union(&1 -- right_value, match))
          {:match, type_vars, acc_vars}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_each({:var, _, key}, type, keep, vars, type_vars, acc_vars) do
    unify_var(key, type, keep, vars, type_vars, acc_vars)
  end

  defp unify_each(type, {:var, _, key}, keep, vars, type_vars, acc_vars) do
    unify_var(key, type, keep, vars, type_vars, acc_vars)
  end

  defp unify_each({:fn, lefties, arity}, {:fn, righties, arity},
                  keep, vars, type_vars, acc_vars) do
    unify_fn(lefties, righties, keep, vars, type_vars, acc_vars)
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  keep, vars, type_vars, acc_vars) do
    case unify_args(lefties, righties, keep, vars, type_vars, acc_vars) do
      {:match, _, type_vars, acc_vars} ->
        {:match, type_vars, acc_vars}
      {:subset, args, type_vars, acc_vars} ->
        {:subset, {:tuple, :lists.reverse(args), arity}, type_vars, acc_vars}
      {:disjoint, _, _, _} ->
        :disjoint
    end
  end

  defp unify_each(left, right, _keep, _vars, type_vars, acc_vars) do
    case Union.qualify(left, right) do
      :equal -> {:match, type_vars, acc_vars}
      :superset -> {:match, type_vars, acc_vars}
      :subset -> {:subset, left, type_vars, acc_vars}
      :disjoint -> :disjoint
    end
  end

  defp unify_var(key, type, keep, vars, type_vars, acc_vars) do
    case Map.get(vars, key, []) do
      [] ->
        {:match,
         Map.update(type_vars, key, [type], &Union.union(&1, [type])),
         Map.update(acc_vars, key, [type], &Union.union(&1, [type]))}
      value ->
        with {_, [_ | _] = match, type_vars, acc_vars} <-
               unify(value, [type], keep, vars, type_vars, acc_vars) do
          {:match,
           Map.update(type_vars, key, match, &Union.union(&1 -- value, match)),
           Map.update(acc_vars, key, match, &Union.union(&1 -- value, match))}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_fn([{left_head, left_body, left_inferred} | lefties], righties,
                keep, vars, type_vars, acc_vars) do

    case unify_fn(left_head, left_body, left_inferred, righties, keep, vars, type_vars, acc_vars, false) do
      {type_vars, acc_vars} ->
        unify_fn(lefties, righties, keep, type_vars, type_vars, acc_vars)
      :error ->
        :disjoint
    end
  end
  defp unify_fn([], _righties, _keep, _vars, type_vars, acc_vars) do
    {:match, type_vars, acc_vars}
  end

  defp unify_fn(left_head, left_body, left_inferred,
                [{right_head, right_body, right_inferred} | clauses],
                keep, vars, type_vars, acc_vars, matched?) do
    vars =
      vars
      |> Map.merge(left_inferred)
      |> Map.merge(right_inferred)
      |> Map.drop(keep)

    type_vars =
      type_vars
      |> Map.merge(left_inferred)
      |> Map.merge(right_inferred)
      |> Map.drop(keep)

    with {:match, _, type_vars, acc_vars} <-
           unify_args(right_head, left_head, keep, vars, type_vars, acc_vars),
         {:match, _, type_vars, acc_vars} <-
           unify(right_body, left_body, keep, type_vars, type_vars, acc_vars) do
      unify_fn(left_head, left_body, left_inferred, clauses, keep, vars, type_vars, acc_vars, true)
    else
      _ ->
        unify_fn(left_head, left_body, left_inferred, clauses, keep, vars, type_vars, acc_vars, matched?)
    end
  end
  defp unify_fn(_, _, _, [], _keep, _vars, type_vars, acc_vars, true) do
    {type_vars, acc_vars}
  end
  defp unify_fn(_, _, _, [], _keep, _vars, _type_vars, _acc_vars, false) do
    :error
  end

  defp unify_args(lefties, righties, keep, vars, type_vars, acc_vars) do
    unify_args(lefties, righties, keep, vars, type_vars, acc_vars, :match, [])
  end

  defp unify_args([left | lefties], [right | righties],
                  keep, vars, type_vars, acc_vars, acc_kind, acc_matched) do
    case unify(left, right, keep, vars, type_vars, acc_vars) do
      {:disjoint, _, _, _} = disjoint ->
        disjoint
      {kind, matched, type_vars, acc_vars} ->
        unify_args(lefties, righties, keep, vars, type_vars, acc_vars,
                   unify_min(kind, acc_kind), [matched | acc_matched])
    end
  end
  defp unify_args([], [], _keep, _vars, type_vars, acc_vars, kind, acc_matched) do
    {kind, acc_matched, type_vars, acc_vars}
  end

  @doc """
  Binds the variables to their types.

  A set of variables to not be replaced can be given, useful
  to guarantee anonymous functions only interpolate variables
  introduced by themselves.
  """
  def bind(types, vars, preserve \\ %{}) do
    bind(types, %{}, vars, preserve)
  end

  defp bind(types, used, vars, preserve) do
    Union.traverse(types, used, fn
      {:var, _, key}, used ->
        {value, used} =
          case Map.fetch(preserve, key) do
            {:ok, value} -> {value, used}
            :error -> {[], Map.put(used, key, true)}
          end
        case Map.get(vars, key, []) do
          [_ | _] = existing when value == [] ->
            {:union, existing, used}
          _ ->
            {:ok, used}
        end
      _, used ->
        {:ok, used}
    end)
  end

  defp bind_args(args, used, vars, preserve) do
    Enum.map_reduce(args, used, &bind(&1, &2, vars, preserve))
  end

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, state())
  end

  defp of({var, meta, ctx}, %{counter: counter, vars: vars} = state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Map.fetch(vars, {var, ctx}) do
      {:ok, types} ->
        {types, counter} = Union.traverse(types, counter, &of_var/2)
        ok(types, %{state | counter: counter})
      :error ->
        error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, state) do
    with {:ok, clauses, state} <- of_clauses(clauses, state) do
      ok([{:fn, clauses, 1}], state)
    end
  end

  defp of({:__block__, _meta, args}, state) do
    of_block(args, state)
  end

  defp of({:=, meta, [left, right]}, state) do
    with {:ok, right, right_state} <- of(right, state),
         {:ok, left, left_state} <- of_pattern(left, replace_vars(right_state, state)) do
      state = lift_vars(left_state, right_state)
      %{inferred: inferred, vars: vars, match: match} = state

      case of_match(left, right, inferred, vars, match) do
        {:ok, acc_vars, acc_inferred, acc_body} ->
          ok(acc_body, %{state | inferred: acc_inferred, vars: acc_vars})
        :error ->
          error(meta, {:disjoint_match, left, right})
      end
    end
  end

  defp of({{:., _, [fun]}, meta, args}, state) do
    with {:ok, fun, fun_state} <- of(fun, state),
         {:ok, args, arity, state} <- args(args, replace_vars(fun_state, state), &of/2) do
      of_apply(fun, arity, meta, args, state, [], fun_state)
    end
  end

  defp of(value, state) do
    literal(value, state, &of/2)
  end

  ## Apply

  defp of_apply([{:fn, clauses, arity} | types], arity, meta, args, state, acc, fun_state) do
    with {:ok, return, state} <- of_fn_apply(clauses, meta, args, state),
         do: of_apply(types, arity, meta, args, state, Union.union(acc, return), fun_state)
  end
  defp of_apply([{:var, var_ctx, var_counter} | types], arity, meta, args, state, acc, fun_state) do
    with {:ok, return, state} <- of_var_apply(var_ctx, var_counter, meta, args, arity, state),
         do: of_apply(types, arity, meta, args, state, Union.union(acc, return), fun_state)
  end
  defp of_apply([fun_type | _], arity, meta, _args, _state, _acc, _fun_state) do
    error(meta, {:invalid_fn, fun_type, arity})
  end
  defp of_apply([], _arity, _meta, _args, state, acc, fun_state) do
    {:ok, acc, lift_vars(state, fun_state)}
  end

  ### Var apply

  defp of_var_apply(var_ctx, var_counter, meta, [arg_types], arity, state) do
    %{inferred: inferred, counter: counter, var_apply: var_apply} = state
    var_applies = Map.get(var_apply, var_counter, [])

    # We allow only a limited for of rank 2 intersections where
    # type variables in one clause do not affect type variables
    # in other clauses. This means we need to carefully check the
    # argument types input considering that:
    #
    #   1. if a variable is called passing itself as an argument,
    #      such as `x.(x)`, it is a recursive call that would have
    #      type a ^ (a -> b) which is not supported
    #
    #   2. if a variable is called with the result of a previous
    #      invocation on the same variable, such as `x.(x.(y))`,
    #      we need to guarantee all variables returned as a result
    #      of the parent invocation are resolved. For example, the
    #      snippet above would return (a -> b) & (b -> c) which we
    #      don't support, so we attempt to resolve it and get instead
    #      the more restrict type (a -> a).
    #
    #   3. if there is no recursion, then we are good to go.
    case of_var_apply_recur([arg_types], var_counter, var_applies) do
      :self ->
        error(meta, {:recursive_fn, [{:var, var_ctx, var_counter}], arg_types, arity})
      var_recur ->
        var_recur = Enum.uniq(var_recur)

        case of_var_apply_unify(var_counter, [arg_types], arity, inferred, var_recur) do
          {{:match, return, inferred}, types} ->
            inferred = Map.put(inferred, var_counter, types)
            ok(return, %{state | inferred: inferred})
          {:recursive, _} ->
            error(meta, {:disjoint_var_apply, [var_ctx, [arg_types]]})
          {:nomatch, []} ->
            error(meta, {:disjoint_var_apply, [var_ctx, [arg_types]]})
          {:nomatch, types} ->
            return = [{:var, var_ctx, counter}]

            types =
              for {:fn, clauses, arity} <- types do
                {:fn, of_var_apply_clauses(clauses, [arg_types], return), arity}
              end

            inferred =
              inferred
              |> Map.put(counter, [])
              |> Map.put(var_counter, types)

            var_apply =
              Map.put(var_apply, var_counter, [counter | var_applies])

            ok(return, %{state | inferred: inferred, counter: counter + 1, var_apply: var_apply})
        end
    end
  end

  defp of_var_apply_recur(types, var_counter, var_applies) do
    Union.traverse_args(types, [], fn
      {:var, _, ^var_counter}, _ ->
        {:ok, :self}
      {:var, _, counter}, acc when is_list(acc) ->
        {:ok, if(counter in var_applies, do: [counter | acc], else: acc)}
      _type, acc ->
        {:ok, acc}
    end) |> elem(1)
  end

  defp of_var_apply_unify(key, args, arity, inferred, recur) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], arity}]}
      existing ->
        funs = for {:fn, _, ^arity} = fun <- existing, do: fun

        {case recur do
          [] -> of_var_apply_unify_equal(funs, args, inferred)
          _  -> of_var_apply_unify_recur(funs, args, recur, inferred, [], inferred)
         end, funs}
    end
  end

  defp of_var_apply_unify_recur([{:fn, clauses, _} | funs], args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
  end
  defp of_var_apply_unify_recur([], _args, recur, _inferred, sum, acc_inferred) do
    if acc_inferred |> Map.take(recur) |> Enum.all?(fn {_, types} -> types != [] end) do
      {:match, sum, acc_inferred}
    else
      :recursive
    end
  end

  defp of_var_apply_unify_recur([{head, [{:var, _, var_recur}] = body, _} | clauses],
                                funs, args, recur, inferred, sum, acc_inferred) do
    with true <- var_recur in recur,
         {:match, _, _, acc_inferred} <-
           unify_args(args, head, [], inferred, inferred, acc_inferred) do
      of_var_apply_unify_recur(clauses, funs, args, recur, inferred, Union.union(body, sum), acc_inferred)
    else
      _ -> of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
    end
  end
  defp of_var_apply_unify_recur([_ | clauses], funs, args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
  end
  defp of_var_apply_unify_recur([], funs, args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(funs, args, recur, inferred, sum, acc_inferred)
  end

  defp of_var_apply_unify_equal([{:fn, clauses, _} | funs], args, inferred) do
    of_var_apply_unify_equal(clauses, funs, args, inferred)
  end
  defp of_var_apply_unify_equal([], _args, _inferred) do
    :nomatch
  end

  defp of_var_apply_unify_equal([{args, body, _} | _clauses], _funs, args, inferred) do
    {:match, body, inferred}
  end
  defp of_var_apply_unify_equal([_ | clauses], funs, args, inferred) do
    of_var_apply_unify_equal(clauses, funs, args, inferred)
  end
  defp of_var_apply_unify_equal([], funs, args, inferred) do
    of_var_apply_unify_equal(funs, args, inferred)
  end

  defp of_var_apply_clauses(clauses, args, return) do
    {pre, pos} =
      Enum.split_while(clauses, fn {head, _, _} ->
        Union.qualify_args(head, args) != :superset
      end)
    pre ++ [{args, return, %{}} | pos]
  end

  ### Fn Apply

  defp of_fn_apply(clauses, meta, [arg_types], state) do
    %{inferred: inferred} = state

    case of_fn_apply_each(clauses, arg_types, inferred, arg_types, inferred, []) do
      {:ok, acc_inferred, acc_body} ->
        ok(acc_body, %{state | inferred: acc_inferred})
      {:error, pending} ->
        error(meta, {:disjoint_apply, pending, clauses, arg_types})
    end
  end

  # If we have matched all arguments and we haven't inferred anything new,
  # it means they are literals and there is no need for an exhaustive search.
  # TODO: If we have multiple arguments. We need to generate a cartesian
  # product of all of them and ensure all of them have a match.
  defp of_fn_apply_each(_clauses, _arg, inferred, [], inferred, acc_body) do
    {:ok, inferred, acc_body}
  end
  defp of_fn_apply_each([{[head], body, vars} | clauses],
                        arg, inferred, acc_arg, acc_inferred, acc_body) do
    inferred = Map.merge(inferred, vars)
    acc_inferred = Map.merge(acc_inferred, vars)

    with {_, [_ | _] = matched, _, acc_inferred} <-
           unify(head, arg, Map.keys(vars), inferred, acc_inferred) do
      acc_body = Union.union(acc_body, body)
      of_fn_apply_each(clauses, arg, inferred, acc_arg -- matched, acc_inferred, acc_body)
    else
      _ ->
        of_fn_apply_each(clauses, arg, inferred, acc_arg, acc_inferred, acc_body)
    end
  end
  defp of_fn_apply_each([], _arg, _inferred, [], acc_inferred, acc_body) do
    {:ok, acc_inferred, acc_body}
  end
  defp of_fn_apply_each([], _arg, _inferred, pending, _acc_inferred, _acc_body) do
    {:error, pending}
  end

  ## Matching

  # All of the possible types returned on the right side
  # must be matched on the left side. We must also unify
  # values on the right side with expressions on the left.
  # For example, the type:
  #
  #     fn z ->
  #       {:ok, x} = (fn y -> {y, :error} end).(z)
  #       {z, x}
  #     end
  #
  # Should infer that:
  #
  #     x is :error
  #     y is :ok
  #     z is :ok
  #
  # And the function must return {:ok, :error}.
  defp of_match(left, right, inferred, vars, match) do
    keep = for {_, {:var, _, counter}} <- match, do: {counter, []}, into: %{}

    with {:match, _, _, match_inferred} <- unify(left, right, keep, inferred, inferred) do
      {vars, inferred} = of_match_vars(Map.to_list(match), vars, match_inferred)
      {:ok, vars, inferred, right}
    else
      _ -> :error
    end
  end

  defp of_match_vars([{var_ctx, [{_, _, counter}]} | matches], vars, inferred) do
    of_match_vars(matches,
                  Map.put(vars, var_ctx, Map.fetch!(inferred, counter)),
                  Map.delete(inferred, counter))
  end
  defp of_match_vars([], vars, inferred) do
    {vars, inferred}
  end

  ## Clauses

  # TODO: Support multiple args
  # TODO: Check if clauses have overlapping types
  defp of_clauses(clauses, state) do
    of_clauses(clauses, state, [], state)
  end

  defp of_clauses([{:->, _, [[arg], body]} | clauses],
                   %{inferred: preserve} = state, acc_clauses, acc_state) do
    with {:ok, arg, %{match: match, vars: vars} = acc_state} <- of_pattern(arg, acc_state),
         acc_state = %{acc_state | vars: Map.merge(vars, match)},
         {:ok, body, acc_state} <- of(body, acc_state) do
      acc_state = replace_vars(acc_state, state)
      %{inferred: inferred, var_apply: var_apply} = acc_state

      # Get all variables introduced in the function head.
      match_counters =
        for {_, [{:var, _, key}]} <- match,
            counter <- [key | Map.get(var_apply, key, [])],
            do: counter

      # We will expand all entries except the upper scope
      # and except the match counters.
      {body, body_used} =
        bind(body, Map.drop(inferred, match_counters), preserve)

      # We must only keep counters that are free OR have been
      # used and are a super type.
      match_counters =
        for counter <- match_counters,
            value = Map.get(inferred, counter, []),
            value == [] or (Map.has_key?(body_used, counter) and Union.supertype?(value)),
            do: counter

      # The outer scope is going to keep all variables except
      # the ones we have been abstracting away. That's because
      # an outer scope may be pointing to an inner scope.
      acc_inferred = Map.drop(inferred, match_counters)

      # Go through all arguments and expand what
      # we are not keeping and is not from upstream.
      {head, head_used} =
        bind_args([arg], %{}, acc_inferred, preserve)

      # If there are variables in the head that are not in match
      # counters, and we have not inferred about them, we need to
      # hoist them up.
      # TODO: Remove hoisting by tracking the level of variables.
      hoist =
        for counter <- Map.keys(head_used) -- match_counters,
            not Map.has_key?(inferred, counter),
            do: counter

      {head, body} =
        case hoist do
          [] ->
            {head, body}
          _ ->
            {head, _} = Union.traverse_args(head, hoist, &of_clauses_hoist/2)
            {body, _} = Union.traverse(body, hoist, &of_clauses_hoist/2)
            {head, body}
        end

      # Build our final list of bindings.
      clause_inferred =
        for counter <- hoist ++ match_counters,
            {value, _} = bind(Map.get(inferred, counter, []), acc_inferred, preserve),
            do: {counter, value},
            into: %{}

      acc_state = %{acc_state | inferred: acc_inferred}
      of_clauses(clauses, state, [{head, body, clause_inferred} | acc_clauses], acc_state)
    end
  end
  defp of_clauses([], _state, acc_clauses, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_state}
  end

  defp of_clauses_hoist({:fn, clauses, arity}, hoist) do
    clauses =
      for {head, body, inferred} <- clauses do
        {head, _} = Union.traverse_args(head, hoist, &of_clauses_hoist/2)
        {body, _} = Union.traverse(body, hoist, &of_clauses_hoist/2)
        {head, body, Map.drop(inferred, hoist)}
      end
    {:replace, {:fn, clauses, arity}, hoist}
  end
  defp of_clauses_hoist(_, hoist) do
    {:ok, hoist}
  end

  ## Blocks

  defp of_block([arg], state) do
    of(arg, state)
  end
  defp of_block([arg | args], state) do
    case of(arg, state) do
      {:ok, _, state} -> of_block(args, state)
      {:error, _, _} = error -> error
    end
  end

  ## Vars

  defp of_var({:fn, clauses, arity}, counter) do
    {:replace, rewrite, _} =
      of_var_rewrite({:fn, clauses, arity}, {counter, %{}})
    {:replace, rewrite, counter + 1}
  end
  defp of_var(_type, acc) do
    {:ok, acc}
  end

  defp of_var_rewrite({:fn, clauses, arity}, {counter, rewrite} = info) do
    clauses =
      for {head, body, inferred} <- clauses do
        info = {counter, Map.merge(rewrite, inferred)}

        {head, _} = Union.traverse_args(head, info, &of_var_rewrite/2)
        {body, _} = Union.traverse(body, info, &of_var_rewrite/2)
        inferred = for {k, v} <- inferred, do: {[counter | k], v}, into: %{}

        {head, body, inferred}
      end

    {:replace, {:fn, clauses, arity}, info}
  end
  defp of_var_rewrite({:var, ctx, key}, {counter, rewrite} = info) do
    case rewrite do
      %{^key => _} ->
        {:replace, {:var, ctx, [counter | key]}, info}
      %{} ->
        {:ok, info}
    end
  end
  defp of_var_rewrite(_type, counter) do
    {:ok, counter}
  end

  ## Patterns

  defp of_pattern(ast, state) do
    of_pattern_each(ast, %{state | match: %{}})
  end

  defp of_pattern_each({:::, meta, [{var, _, ctx}, type_ast]}, state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    with {:ok, type, state} <- ast_to_types(type_ast, state) do
      of_pattern_bound_var(meta, {var, ctx}, type, state)
    end
  end
  defp of_pattern_each({var, meta, ctx}, state) when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    of_pattern_var(meta, {var, ctx}, state)
  end
  defp of_pattern_each({:::, meta, [_, _]} = ann, _vars) do
    error(meta, {:invalid_annotation, ann})
  end
  defp of_pattern_each(other, vars) do
    literal(other, vars, &of_pattern_each/2)
  end

  defp of_pattern_var(_meta, var_ctx, state) do
    %{match: match, counter: counter, inferred: inferred} = state

    case Map.fetch(match, var_ctx) do
      {:ok, type} ->
        ok(type, state)
      :error ->
        inferred = Map.put(inferred, counter, [])
        return = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, return)
        ok(return, %{state | match: match, counter: counter + 1, inferred: inferred})
    end
  end

  defp of_pattern_bound_var(meta, var_ctx, types, state) do
    %{match: match, counter: counter, inferred: inferred} = state
    case Map.fetch(match, var_ctx) do
      {:ok, [{:var, _, counter}] = return} ->
        case Map.fetch!(inferred, counter) do
          ^types -> ok(return, state)
          other -> error(meta, {:bound_var, var_ctx, other, types})
        end
      :error ->
        inferred = Map.put(inferred, counter, types)
        return = [{:var, var_ctx, counter}]
        match = Map.put(match, var_ctx, return)
        ok(return, %{state | match: match, counter: counter + 1, inferred: inferred})
    end
  end

  ## Helpers

  defp literal(value, state, _fun) when is_integer(value) do
    ok([:integer], state)
  end

  defp literal(value, state, _fun) when is_atom(value) do
    ok([{:value, value}], state)
  end
  defp literal({left, right}, state, fun) do
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      ok([{:tuple, args, arity}], state)
    end
  end
  defp literal({:{}, _, args}, state, fun) do
    with {:ok, args, arity, state} <- args(args, state, fun) do
      ok([{:tuple, args, arity}], state)
    end
  end
  defp literal(other, _state, _fun) do
    error([], {:unknown_pattern, other})
  end

  defp args(args, state, fun) do
    args(args, [], 0, state, state, fun)
  end

  defp args([arg | args], acc_args, acc_count, acc_state, state, fun) do
    case fun.(arg, replace_vars(acc_state, state)) do
      {:ok, arg, arg_state} ->
        args(args, [arg | acc_args], acc_count + 1, lift_vars(arg_state, acc_state), state, fun)
      {:error, _, _} = error ->
        error
    end
  end
  defp args([], acc_args, acc_count, acc_state, _state, _fun) do
    {:ok, :lists.reverse(acc_args), acc_count, acc_state}
  end

  @compile {:inline, ok: 2, error: 2}

  defp ok(type, state) when is_list(type) do
    {:ok, type, state}
  end

  defp error(meta, args) do
    {:error, meta, args}
  end

  ## State helpers

  # The :vars map keeps all Elixir variables and their types
  # The :match map keeps all Elixir variables defined in a match
  # The :inferred map keeps track of all inferred types (they have a counter)
  @state %{vars: %{}, match: %{}, inferred: %{}, counter: 0, var_apply: %{}}

  defp state do
    @state
  end

  defp replace_vars(state, %{vars: vars}) do
    %{state | vars: vars}
  end

  defp lift_vars(%{vars: vars1} = state, %{vars: vars2}) do
    %{state | vars: Map.merge(vars2, vars1)}
  end
end