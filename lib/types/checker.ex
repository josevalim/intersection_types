defmodule Types.Checker do
  @moduledoc false

  alias Types.Union

  ## Unification

  # The next functions are responsible for unification.
  # Unification is about unifying types on the left with
  # types on the right according to some rules. The rules
  # change according to the unification being performed.
  #
  # There are five unification functions:
  #
  #   * unify_vars - for unifying type variable unions
  #   * unify_return - for unifying return type unions
  #   * unify_paired - for unifying two lists of types
  #     side by side (i.e. in pairs)
  #   * unify_each - the low level function that unifies
  #     a non-union type directly with another type
  #
  # All unification functions receive the following variables:
  #
  #   * keep - the variables that should be refreshed when
  #     unifying functions with functions
  #   * vars - the variables that have been inferred so far
  #   * acc_vars - the variables that have been inferred
  #     during unification

  ## UNIFY RETURN

  # This function is used when all types on the right must
  # have a match on the left side. It is used to check for
  # return types.
  #
  # Returns `{:match, vars}` if so, `:disjoint` otherwise.
  defp unify_return(lefties, [right | righties], keep, vars, acc_vars) do
    unify_return(lefties, right, keep, vars, acc_vars, lefties, righties)
  end
  defp unify_return(_lefties, [], _keep, _vars, acc_vars) do
    {:match, acc_vars}
  end

  defp unify_return([type | types], right, keep, vars, acc_vars, lefties, righties) do
    case unify_each(type, right, keep, vars, acc_vars) do
      {:match, acc_vars} ->
        unify_return(lefties, righties, keep, vars, acc_vars)
      _ ->
        unify_return(types, right, keep, vars, acc_vars, lefties, righties)
    end
  end
  defp unify_return([], _right, _keep, _vars, _acc_vars, _lefties, _righties) do
    :disjoint
  end

  ## UNIFY VARS

  # This is used when unifying two vars.
  #
  # When unifying vars, we want to find all types on the
  # right side that match the left side. If some types do
  # not match, that's ok.
  #
  # This function returns `{:match, matched, vars}` if all
  # matched were full matches and `{:subset, matched, vars}`
  # if one or more matched were subsets.
  def unify_vars(left, right, keep, vars, acc_vars) do
    unify_vars(left, right, keep, vars, acc_vars, [], :match)
  end

  defp unify_vars(lefties, [right | righties], keep, vars, acc_vars, matched, kind) do
    unify_vars(lefties, right, keep, vars, acc_vars, lefties, righties, matched, [], kind)
  end
  defp unify_vars(_lefties, [], _keep, _vars, acc_vars, matched, kind) do
    {kind, matched, acc_vars}
  end

  defp unify_vars([type | types], right, keep, vars, acc_vars, lefties, righties, matched, subset, kind) do
    case unify_each(type, right, keep, vars, acc_vars) do
      {:match, acc_vars} ->
        unify_vars(lefties, righties, keep, vars, acc_vars, [right | matched], kind)
      {:subset, acc_vars} ->
        unify_vars(types, right, keep, vars, acc_vars, lefties, righties, matched, [type | subset], kind)
      :disjoint ->
        unify_vars(types, right, keep, vars, acc_vars, lefties, righties, matched, subset, kind)
    end
  end
  defp unify_vars([], _right, keep, vars, acc_vars, lefties, righties, matched, [], kind) do
    unify_vars(lefties, righties, keep, vars, acc_vars, matched, kind)
  end
  defp unify_vars([], _right, keep, vars, acc_vars, lefties, righties, matched, subset, _kind) do
    unify_vars(lefties, righties, keep, vars, acc_vars, subset ++ matched, :subset)
  end

  ## UNIFY EACH

  defp unify_each(type, type, _keep, _vars, acc_vars) do
    {:match, acc_vars}
  end

  defp unify_each({:var, _, key1}, {:var, _, key2} = right, keep, vars, acc_vars) do
    case {Map.get(vars, key1, []), Map.get(vars, key2, [])} do
      {[], right_value} ->
        acc_vars =
          acc_vars
          |> Map.put(key2, right_value)
          |> Map.update(key1, [right], &Union.union(&1, [right]))
        {:match, acc_vars}

      {left_value, right_value} when right_value == [] when right_value == left_value ->
        if Enum.any?(left_value, &match?({:var, _, ^key2}, &1)) do
          {:match, acc_vars}
        else
          acc_vars =
            acc_vars
            |> Map.update(key2, left_value, &Union.union(&1, left_value))
            |> Map.update(key1, [right], &Union.union(&1 -- left_value, [right]))
          {:match, acc_vars}
        end

      {left_value, right_value} ->
        with {kind, [_ | _] = match, acc_vars} <-
               unify_vars(left_value, right_value, keep, vars, acc_vars) do
          acc_vars =
            acc_vars
            |> Map.update(key1, match, &Union.union(&1 -- left_value, match))
            |> Map.update(key2, match, &Union.union(&1 -- right_value, match))
          {kind, acc_vars}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_each({:var, _, key}, type, keep, vars, acc_vars) do
    case Map.get(vars, key, []) do
      [] ->
        {:match, Map.update(acc_vars, key, [type], &Union.union(&1, [type]))}
      value ->
        case unify_vars(value, [type], keep, vars, acc_vars) do
          {kind, [_ | _] = match, acc_vars} ->
            acc_vars = Map.update(acc_vars, key, match, &Union.union(&1 -- value, match))
            {kind, acc_vars}
          _ ->
            :disjoint
        end
    end
  end

  # Variables on the right side always need to match.
  defp unify_each(type, {:var, _, key}, keep, vars, acc_vars) do
    case Map.get(vars, key, []) do
      [] ->
        {:match, Map.update(acc_vars, key, [type], &Union.union(&1, [type]))}
      value ->
        case unify_vars([type], value, keep, vars, acc_vars) do
          {kind, [_ | _] = match, acc_vars} ->
            acc_vars = Map.update(acc_vars, key, match, &Union.union(&1 -- value, match))
            {kind, acc_vars}
          _ ->
            :disjoint
        end
    end
  end

  defp unify_each({:fn, lefties, left_inferred, arity}, {:fn, righties, right_inferred, arity},
                  keep, vars, acc_vars) do
    lefties =
      for {head, body} <- lefties do
        permuted = Union.permute_args(head, & &1)
        {permuted, body}
      end

    righties =
      for {head, body} <- righties, permuted <- Union.permute_args(head, & &1) do
        {permuted, body}
      end

    keep = Map.merge(keep, left_inferred)
    unify_fn(lefties, righties, right_inferred, keep, vars, acc_vars)
  end

  defp unify_each({:cons, left1, right1}, {:cons, left2, right2}, keep, vars, acc_vars) do
    unify_paired([left1, right1], [left2, right2], keep, vars, acc_vars)
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity}, keep, vars, acc_vars) do
    unify_paired(lefties, righties, keep, vars, acc_vars)
  end

  defp unify_each(left, right, _keep, _vars, acc_vars) do
    case Union.qualify(left, right) do
      :equal -> {:match, acc_vars}
      :superset -> {:match, acc_vars}
      :subset -> {:subset, acc_vars}
      :disjoint -> :disjoint
    end
  end

  ## UNIFY FN (helper for unifying functions on unify_each)

  # Unifying functions is done by making sure that all clauses
  # on the left side is satisfied by at least one clause on the
  # right side.
  #
  # This is quite complex as it requires tracking different kinds
  # of variables and renewing them at different stages. We will
  # explore those scenarios below.
  #
  # ## Example 1
  #
  # The type:
  #
  #     ((a -> b) -> (a -> b))
  #
  # applied with:
  #
  #     (:foo -> :bar; :bar -> :baz)
  #
  # should unify to:
  #
  #     (:foo | :bar -> :bar | :baz)
  #
  # Note the left side is made of three functions, where the variables
  # a and b are defined in the outermost one. This means that, we
  # need to know which variables have been in the outermost function
  # and properly pass them forward for "cleaning".
  #
  # This is done by the keep argument. The keep argument keeps all
  # variables from the left side, both outer and inner ones.
  #
  # ## Example 2
  #
  # The type:
  #
  #     (({:bar, a} -> b; {:foo, a} -> c), a -> {c, b})
  #
  # applied with:
  #
  #     (:foo, :ok} -> :bar; {:bar, :error} -> :foo)
  #
  # should not unify. That's because we are attempting to assign the
  # variable `a`, from different clauses, to two different values:
  # :ok and :error.
  #
  # In order to do this, we need to make sure the `keep` variables
  # from the previous section are refreshed every time we change the
  # left clause being analyzed.
  defp unify_fn([{left_heads, left_body} | lefties], righties, right_inferred,
                keep, vars, acc_vars) do
    keep =
      vars
      |> Map.take(Map.keys(keep))
      |> Map.merge(right_inferred)

    case unify_fn(left_heads, left_body, righties, right_inferred, keep, vars, acc_vars, false) do
      {vars, acc_vars} ->
        unify_fn(lefties, righties, right_inferred, keep, vars, acc_vars)
      :error ->
        :disjoint
    end
  end
  defp unify_fn([], _righties, _right_inferred, _keep, _vars, acc_vars) do
    {:match, acc_vars}
  end

  defp unify_fn(left_heads, left_body, [{right_head, right_body} | clauses],
                right_inferred, keep, vars, acc_vars, matched?) do
    vars = Map.merge(vars, keep)

    # Unifying functions require all types on the left to be
    # matched by the types on the right, so we swap them below.
    #
    # Here is a test case that will fail if the order is wrong:
    #
    #     (fn x ->
    #        {x.(:foo), x.(:bar), x.(:baz)}
    #      end).(fn y :: atom() -> y end))
    #
    match =
      Enum.reduce_while(left_heads, {:disjoint, %{}}, fn left_head, {kind, new_vars} ->
        case unify_paired(right_head, left_head, keep, vars, new_vars) do
          {:match, new_vars} -> {:halt, {:match, new_vars}}
          {:subset, new_vars} -> {:cont, {:subset, new_vars}}
          _ -> {:cont, {kind, new_vars}}
        end
      end)

    with {kind, new_vars} when kind in [:match, :subset] <- match,
         {vars, acc_vars} = unify_fn_keep(new_vars, vars, acc_vars),
         right_body = bind_matching(right_body, keep, vars),
         {:match, new_vars} <- unify_return(left_body, right_body, keep, vars, %{}) do
      {vars, acc_vars} = unify_fn_keep(new_vars, vars, acc_vars)
      unify_fn(left_heads, left_body, clauses, right_inferred, keep,
               vars, acc_vars, matched? or kind == :match)
    else
      _ ->
        unify_fn(left_heads, left_body, clauses, right_inferred, keep, vars, acc_vars, matched?)
    end
  end
  defp unify_fn(_, _, [], _right_inferred, _keep, vars, acc_vars, true) do
    {vars, acc_vars}
  end
  defp unify_fn(_, _, [], _right_inferred, _keep, _vars, _acc_vars, false) do
    :error
  end

  # This is a variant of of_fn_apply_keep but it is simpler
  # as we don't need to keep levels for variables generated
  # from inside inner functions, therefore we can use unique
  # integers to generate such variables.
  defp unify_fn_keep(new_inferred, inferred, acc_inferred) do
    rebind =
      Enum.reduce(new_inferred, %{}, fn
        {key, []}, rebind ->
          counter = -System.unique_integer([:positive])
          value = [{:var, {:unify_fn, __MODULE__}, counter}]
          Map.put(rebind, key, value)
        _, rebind ->
          rebind
      end)

    Enum.reduce(new_inferred, {inferred, acc_inferred}, fn
      {key, value}, {inferred, acc_inferred} ->
        value =
          case value do
            [_ | _] -> bind_matching(value, rebind, rebind)
            [] -> Map.fetch!(rebind, key)
          end
        {Map.put(inferred, key, value),
         Map.update(acc_inferred, key, value, &Union.union(&1, value))}
    end)
  end

  ## UNIFY PAIRED

  defp unify_paired(lefties, righties, keep, vars, acc_vars) do
    unify_paired(lefties, righties, keep, vars, acc_vars, :match)
  end

  defp unify_paired([left | lefties], [right | righties], keep, vars, acc_vars, kind) do
    case unify_each(left, right, keep, vars, acc_vars) do
      {:match, new_vars} ->
        vars = Map.merge(vars, new_vars)
        acc_vars = Map.merge(acc_vars, new_vars)
        unify_paired(lefties, righties, keep, vars, acc_vars, kind)
      {:subset, new_vars} ->
        vars = Map.merge(vars, new_vars)
        acc_vars = Map.merge(acc_vars, new_vars)
        unify_paired(lefties, righties, keep, vars, acc_vars, :subset)
      :disjoint ->
        :disjoint
    end
  end
  defp unify_paired([], [], _keep, _vars, acc_vars, kind) do
    {kind, acc_vars}
  end

  ## UNIFY ARGS

  @doc """
  Traverses types binding the variables in only with their types in vars.
  """
  def bind_matching(types, only, _vars) when only == %{} do
    types
  end
  def bind_matching(types, only, vars) do
    bind_if(types, &Map.has_key?(only, &1), vars, [])
  end

  defp bind_if(types, condition, vars, recur) do
    Union.traverse(types, :ok, fn
      {:var, _, counter}, acc ->
        case counter not in recur and condition.(counter) do
          true ->
            case Map.get(vars, counter, []) do
              [_ | _] = existing -> {:replace, bind_if(existing, condition, vars, [counter | recur]), acc}
              _ -> {:ok, acc}
            end
          false ->
            {:ok, acc}
        end
      _, acc ->
        {:ok, acc}
    end) |> elem(0)
  end

  # Similar to bind but binds based on the variable level.
  defp bind_level(types, unused, vars, level, levels) do
    bind_level_traverse(types, {unused, []}, vars, level, levels)
  end

  defp bind_level_args(args, acc, vars, level, levels) do
    Enum.map_reduce(args, {acc, []}, &bind_level_traverse(&1, &2, vars, level, levels))
  end

  defp bind_level_traverse(types, acc, vars, level, levels) do
    Union.traverse(types, acc, &bind_level_each(&1, &2, vars, level, levels))
  end

  defp bind_level_each({:var, _, counter}, {unused, rec}, vars, level, levels) do
    case Map.fetch(levels, counter) do
      {:ok, {var_level, _, _}} when var_level < level ->
        {:ok, {unused, rec}}
      _ ->
        unused = List.delete(unused, counter)

        case Map.get(vars, counter, []) do
          [_ | _] = existing ->
            try do
              vars = Map.put(vars, counter, :recursive)
              bind_level_traverse(existing, {unused, rec}, vars, level, levels)
            catch
              :recursive -> {:ok, {unused, [counter | rec]}}
            else
              {existing, acc} -> {:replace, existing, acc}
            end
          [] ->
            {:ok, {unused, rec}}
          :recursive ->
            throw(:recursive)
        end
    end
  end
  defp bind_level_each(_, acc, _vars, _level, _levels) do
    {:ok, acc}
  end

  @doc """
  Returns the type of the given expression.
  """
  def of(expr) do
    of(expr, state())
  end

  defp of({var, meta, ctx}, state) when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    %{vars: vars, level: level} = state
    case Map.fetch(vars, {var, ctx}) do
      {:ok, {var_level, var_types}} ->
        {types, state} = Union.traverse(var_types, %{state | level: var_level}, &of_var/2)
        ok(types, %{state | level: level})
      :error ->
        error(meta, {:unbound_var, var, ctx})
    end
  end

  defp of({:fn, _, clauses}, %{level: level} = state) do
    with {:ok, clauses, inferred, state} <- of_fn(clauses, %{state | level: level + 1}) do
      [{head, _} | _] = clauses
      ok([{:fn, clauses, inferred, length(head)}], %{state | level: level})
    end
  end

  defp of({:__block__, _meta, args}, state) do
    of_block(args, state)
  end

  # TODO: This is a special case for recursion
  defp of({:=, _, [{:recur, _, _}, {:fn, _, clauses}]}, state) do
    with {:ok, clauses_state, clauses_inferred, state} <- of_def(clauses, state),
         {:ok, clauses, inferred} <- of_recur(clauses_state, clauses_inferred, state) do
      [{head, _} | _] = clauses
      ok([{:fn, clauses, inferred, length(head)}], state)
    end
  end

  defp of({:=, meta, [left, right]}, state) do
    with {:ok, right, right_state} <- of(right, state),
         {:ok, [left], left_state} <- of_pattern([left], replace_vars(right_state, state)) do
      state = lift_vars(left_state, right_state)
      %{match: match, vars: vars, inferred: inferred} = state

      case of_match(left, right, inferred, %{}) do
        {:ok, acc_inferred} ->
          {vars, acc_inferred} = of_match_vars(Map.to_list(match), vars, acc_inferred)
          ok(right, %{state | inferred: acc_inferred, vars: vars})
        :error ->
          error(meta, {:disjoint_match, left, right})
      end
    end
  end

  defp of({{:., _, [fun]}, meta, args}, state) do
    with {:ok, fun, fun_state} <- of(fun, state),
         {:ok, args, arity, state} <- args(args, replace_vars(fun_state, state), &of/2),
         {:ok, res, state} <- of_apply(fun, arity, meta, args, state, []) do
      ok(res, lift_vars(state, fun_state))
    end
  end

  defp of({name, _, _} = value, state) when name in [:{}, :<<>>] do
    literal(value, state, &of/2)
  end

  # TODO: This is a special case for recursion
  defp of({name, meta, args}, state) when is_list(args) do
    if name == :recur do
      with {:ok, args, _arity, state} <- args(args, state, &of/2) do
        %{rec: rec, counter: counter, inferred: inferred, levels: levels, level: level} = state
        return = [{:var, {:recur, Elixir}, counter}]
        state = %{state | inferred: Map.put(inferred, counter, []),
                          counter: counter + 1,
                          levels: Map.put(levels, counter, {level, [], []}),
                          rec: Map.put(rec, args, {meta, return})}
        ok(return, state)
      end
    else
      raise "only recur is supported"
    end
  end

  defp of(value, state) do
    literal(value, state, &of/2)
  end

  ## Apply

  defp of_apply([{:fn, clauses, fn_inferred, arity} | types], arity, meta, args, state, acc) do
    with {:ok, return, state} <- of_fn_apply(clauses, fn_inferred, meta, args, state) do
      of_apply(types, arity, meta, args, state, Union.union(acc, return))
    end
  end
  # TODO: We need to act differently depending if var is a free variable or not.
  defp of_apply([{:var, var_ctx, var_counter} | types], arity, meta, args, state, acc) do
    with {:ok, return, state} <- of_var_apply(var_ctx, var_counter, meta, args, arity, state) do
      of_apply(types, arity, meta, args, state, Union.union(acc, return))
    end
  end
  defp of_apply([fun_type | _], arity, meta, _args, _state, _acc) do
    error(meta, {:invalid_fn, fun_type, arity})
  end
  defp of_apply([], _arity, _meta, _args, state, acc) do
    {:ok, acc, state}
  end

  ### Var apply

  defp of_var_apply(var_ctx, var_counter, meta, args, arity, state) do
    %{inferred: inferred, counter: counter, levels: levels} = state
    {var_level, var_applies, var_deps} = Map.fetch!(levels, var_counter)

    # We allow only a limited for of level 2 intersections where
    # type variables can only be shared between bodies. This means
    # we need to carefully check the argument types considering that:
    #
    #   1. if a variable is called passing itself as an argument,
    #      such as `x.(x)`, it is a recursive call that would have
    #      type a ^ (a -> b) which is not supported. This will error.
    #
    #   2. we also make sure co-recursive calls do not occur, such as
    #      `fn x -> fn y -> {x.(y), y.(x)} end end`. This is the
    #      so-called occurs check.
    #
    #   3. if a variable is called with the result of a previous
    #      invocation on the same variable, such as `x.(x.(y))`,
    #      we need to guarantee all variables returned as a result
    #      of the parent invocation are resolved. For example, the
    #      snippet above would return (a -> b) & (b -> c) which we
    #      don't support, so we attempt to resolve it and get instead
    #      the more restrict type (a -> a). Those recursive variables
    #      are returned in `var_recur` below.
    #
    #   4. if there `var_recur` is empty, then we are on the simplest case
    #
    case of_var_apply_recur(args, var_counter, var_applies, var_level, levels) do
      {{:occurs, counter}, _move_up} ->
        error(meta, {:occurs, [{:var, var_ctx, var_counter}], counter, args, arity})
      {:self, _move_up} ->
        error(meta, {:self_var_apply, [{:var, var_ctx, var_counter}], args, arity})
      {var_recur, move_up} ->
        var_recur = Enum.uniq(var_recur)

        # Now we need to unify the argument types against what we have
        # already inferred for the variable.
        #
        #   1. If there is a match, we just use it.
        #   2. If the unification is recursive, then it is an error
        #   3. If there is no match and no types, it means we have
        #      inferred it to not be a function or it has different arity
        #   4. Otherwise there is no match and we just need to add our new types
        #
        case of_var_apply_unify(var_counter, args, arity, inferred, var_recur) do
          {{:match, return, inferred}, types} ->
            inferred = Map.put(inferred, var_counter, types)
            ok(return, %{state | inferred: inferred})
          {:recursive, _} ->
            error(meta, {:recursive_var_apply, [var_ctx, args]})
          {:nomatch, []} ->
            error(meta, {:disjoint_var_apply, [var_ctx, args]})
          {:nomatch, types} ->
            return = [{:var, var_ctx, counter}]

            # We have a new clause for each existing inferred function,
            # we need to find the proper placement for it.
            types =
              for {:fn, fn_clauses, fn_inferred, arity} <- types do
                {:fn, of_var_apply_clauses(fn_clauses, args, return, inferred), fn_inferred, arity}
              end

            # Any variable that is given as argument to the variable
            # being applied needs to moved up to their level. For example:
            #
            #     fn x -> fn y -> x.(y) end end
            #
            # y has level 1 and x has level 0 but we need to move y
            # to level 0 as it is given as input to its parent with type:
            #
            #      ((a -> b) -> (a -> b))
            #
            # If the variable is already at the same level or higher,
            # then we don't move it.
            levels =
              Enum.reduce(move_up, levels, fn up_counter, levels ->
                Map.update!(levels, up_counter, fn {_, applies, deps} ->
                  {var_level, applies, deps}
                end)
              end)

            # Add the inferred variables for the variable being applied
            # on (var_counter) and to the return type (counter)
            inferred =
              inferred
              |> Map.put(counter, [])
              |> Map.put(var_counter, types)

            # var_applies keeps all variables generated as a result
            # of an application (output). var_deps are the inputs.
            # Those are stored with the variable level information
            # as shown below.
            var_applies = [counter | var_applies]
            var_deps = [counter | move_up] ++ var_deps

            levels =
              levels
              |> Map.put(var_counter, {var_level, var_applies, var_deps})
              |> Map.put(counter, {var_level, [], []})

            ok(return, %{state | inferred: inferred, counter: counter + 1, levels: levels})
        end
    end
  end

  defp of_var_apply_recur(types, var_counter, var_applies, var_level, levels) do
    Union.reduce_args(types, {[], []}, fn
      {:var, _, ^var_counter}, {_, acc_levels} ->
        {:self, acc_levels}
      {:var, _, counter}, {acc_applies, acc_levels} when is_list(acc_applies) ->
        if counter in var_applies do
          {[counter | acc_applies], acc_levels}
        else
          {level, _applies, deps} = Map.fetch!(levels, counter)
          cond do
            var_counter in deps ->
              {{:occurs, counter}, acc_levels}
            level > var_level ->
              {acc_applies, [counter | acc_levels]}
            true ->
              {acc_applies, acc_levels}
          end
        end
      _type, acc ->
        acc
    end)
  end

  defp of_var_apply_unify(key, args, arity, inferred, recur) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], %{}, arity}]}
      existing ->
        funs = for {:fn, _, _, ^arity} = fun <- existing, do: fun

        {case recur do
          [] ->
            of_var_apply_unify_equal(funs, args, inferred)
          _  ->
            args = Union.permute_args(args, & &1)
            of_var_apply_unify_recur(funs, args, recur, inferred, [], inferred)
         end, funs}
    end
  end

  defp of_var_apply_unify_recur([{:fn, clauses, _, _} | funs], args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
  end
  defp of_var_apply_unify_recur([], _args, _recur, _inferred, sum, acc_inferred) do
    {:match, sum, acc_inferred}
  end

  defp of_var_apply_unify_recur([{head, [{:var, _, var_recur}] = body} | clauses],
                                funs, args, recur, inferred, sum, acc_inferred) do
    if var_recur in recur do
      case of_var_apply_unify_permute(args, head, inferred, acc_inferred) do
        {:match, acc_inferred} ->
          of_var_apply_unify_recur(clauses, funs, args, recur,
                                   inferred, Union.union(body, sum), acc_inferred)
        _ ->
          :recursive
      end
    else
      of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
    end
  end
  defp of_var_apply_unify_recur([_ | clauses], funs, args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
  end
  defp of_var_apply_unify_recur([], funs, args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(funs, args, recur, inferred, sum, acc_inferred)
  end

  defp of_var_apply_unify_permute(args, head, inferred, acc_inferred) do
    permuted = Union.permute_args(head, & &1)
    Enum.find_value(args, fn arg ->
      Enum.find_value(permuted, fn head ->
        case unify_paired(arg, head, %{}, inferred, acc_inferred) do
          {:match, _} = match -> match
          _ -> nil
        end
      end)
    end)
  end

  defp of_var_apply_unify_equal([{:fn, clauses, _, _} | funs], args, inferred) do
    of_var_apply_unify_equal(clauses, funs, args, inferred)
  end
  defp of_var_apply_unify_equal([], _args, _inferred) do
    :nomatch
  end

  defp of_var_apply_unify_equal([{fn_args, body} | clauses], funs, args, inferred) do
    if Union.same_args?(args, fn_args) do
      {:match, body, inferred}
    else
      of_var_apply_unify_equal(clauses, funs, args, inferred)
    end
  end
  defp of_var_apply_unify_equal([], funs, args, inferred) do
    of_var_apply_unify_equal(funs, args, inferred)
  end

  # If we have a function with type:
  #
  #    (true -> a; boolean() -> b; atom() -> c)(atom())
  #
  # When passing an atom to it, which we don't know the value
  # at compile-time, so may inflect that the response is binary()
  # but, if the input is the atom `:foo`, it will actually be `:bar`!
  # We need to either consider those cases by also considering the
  # results of all subsets or not support overlapping clauses.
  defp of_var_apply_clauses(clauses, args, return, inferred) do
    args = Union.permute_args(args, & &1)

    {index, _} =
      Enum.reduce(clauses, {0, 0}, fn {head, _}, {acc, current} ->
        permuted =
          head
          |> of_var_apply_replace_vars_by_bricks(inferred)
          |> Union.permute_args(& &1)

        match? =
          Enum.any?(permuted, fn head ->
            Enum.any?(args, fn arg ->
              match?({:match, _}, unify_paired(arg, head, %{}, inferred, %{}))
            end)
          end)

        if match? do
          {current + 1, current + 1}
        else
          {acc, current + 1}
        end
      end)

    List.insert_at(clauses, index, {args, return})
  end

  # We don't want the existing free variables in the head to match,
  # so we replace them by "bricks", which are fake atoms with
  # references that are never supposed to match.
  defp of_var_apply_replace_vars_by_bricks(args, inferred) do
    ref = make_ref()
    for arg <- args do
      Union.traverse(arg, :ok, fn
        {:var, _, counter}, acc ->
          case Map.get(inferred, counter, []) do
            [] -> {:replace, [{:atom, [counter | ref]}], acc}
            _ -> {:ok, acc}
          end
        _, acc ->
          {:ok, acc}
      end) |> elem(0)
    end
  end

  ### Fn Apply

  # Applying functions require permutating all arguments and heads.
  #
  # Imagine the following function:
  #
  #     (x | integer(), x | atom() -> ...)
  #
  # Being applied with the arguments:
  #
  #     integer(), empty_list()
  #
  # If we bind the first x to integer(), the second argument will
  # never bind. Therefore, we need to permutate and consider each
  # possible condition in isolation:
  #
  #     (x, x -> ...)
  #     (x, atom() -> ...)
  #     (integer(), x -> ...)
  #     (integer(), atom() -> ...)
  #
  # Where those particular arguments will bind on the third permutation.
  #
  # Because all arguments on the right-side need to match, permutation
  # may not be required on the right side, but we permute those anyway
  # for code simplicity.
  defp of_fn_apply(clauses, fn_inferred, meta, args, state) do
    %{inferred: inferred} = state
    inferred = Map.merge(inferred, fn_inferred)

    permuted_clauses =
      for {head, body} <- clauses, permuted <- Union.permute_args(head, & &1) do
        {permuted, body}
      end

    permuted_args =
      Union.permute_args(args, & &1)

    case of_fn_apply_each(permuted_args, permuted_clauses, fn_inferred, inferred, %{}, state, []) do
      {:ok, _, _} = ok ->
        ok
      {:error, no_match} ->
        error(meta, {:disjoint_apply, no_match, clauses, args})
    end
  end

  defp of_fn_apply_each([arg | args], clauses, fn_inferred,
                        inferred, acc_inferred, state, return) do
    # If the arguments are have no supertypes, we don't need an exaustive search.
    only_non_supertypes? = of_fn_apply_only_non_supertypes?(arg, inferred)

    {match?, acc_inferred, state, return} =
      Enum.reduce_while(clauses, {false, acc_inferred, state, return},
        fn {head, body}, {matched?, acc_inferred, state, return} = acc ->
          case unify_paired(head, arg, fn_inferred, inferred, %{}) do
            {kind, new_inferred} ->
              {acc_inferred, state} = of_fn_apply_keep(new_inferred, acc_inferred, state)
              return = Union.union(return, body)
              next = if only_non_supertypes?, do: :halt, else: :cont
              {next, {matched? or kind == :match, acc_inferred, state, return}}
            _ ->
              {:cont, acc}
          end
      end)

    if match? do
      of_fn_apply_each(args, clauses, fn_inferred, inferred, acc_inferred, state, return)
    else
      {:error, arg}
    end
  end
  defp of_fn_apply_each([], _clauses, _fn_inferred, inferred, acc_inferred, state, return) do
    {:ok, return, %{state | inferred: Map.merge(inferred, acc_inferred)}}
  end

  defp of_fn_apply_only_non_supertypes?(arg, inferred) do
    not Enum.any?(arg, &Union.supertype?([&1], inferred))
  end

  # If the variable has an empty union type, it means it
  # was compared against another free variable. So we need
  # to assign a new typed variable that will be merged into
  # the overall inferred. This logic is what allows this code:
  #
  #     fn x ->
  #       (fn false -> false; nil -> nil; _ -> true end).(x)
  #     end
  #
  # To have the type:
  #
  #     (false | nil | a -> false | nil | true)
  #
  defp of_fn_apply_keep(new_inferred, acc_inferred, state) do
    {rebind, state} =
      Enum.reduce(new_inferred, {%{}, state}, fn
        {key, []}, {rebind, state} ->
          %{counter: counter, level: level, levels: levels} = state
          {var_level, var_applies, var_deps} = Map.fetch!(levels, key)

          levels =
            levels
            |> Map.put(counter, {level, [], []})
            |> Map.put(key, {var_level, var_applies, [counter | var_deps]})

          state = %{state | counter: counter + 1, levels: levels}
          value = [{:var, {:apply, __MODULE__}, counter}]
          {Map.put(rebind, key, value), state}
        _, acc ->
          acc
      end)

    acc_inferred =
      Enum.reduce(new_inferred, acc_inferred, fn
        {key, [_ | _] = value}, acc_inferred ->
          value = bind_matching(value, rebind, rebind)
          Map.update(acc_inferred, key, value, &Union.union(&1, value))
        {key, []}, acc_inferred ->
          value = Map.fetch!(rebind, key)
          Map.update(acc_inferred, key, value, &Union.union(&1, value))
      end)

    {acc_inferred, state}
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
  defp of_match(lefties, [right | righties], inferred, acc_inferred) do
    {match?, acc_inferred} =
      Enum.reduce_while(lefties, {false, acc_inferred},
        fn left, {_, acc_inferred} = acc ->
          case unify_paired([left], [right], %{}, inferred, acc_inferred) do
            {:match, acc_inferred} ->
              {:halt, {true, acc_inferred}}
            _ ->
              {:cont, acc}
          end
      end)

    if match? do
      of_match(lefties, righties, inferred, acc_inferred)
    else
      :error
    end
  end
  defp of_match(_lefties, [], inferred, acc_inferred) do
    {:ok, Map.merge(inferred, acc_inferred)}
  end

  # For each variable on the left side of `=`, we remove its
  # associated type variable and assign the type directly to
  # its var name. This is necessary because generalization
  # works on the types returned by vars.
  defp of_match_vars([{var_ctx, {level, match_vars}} | matches], vars, inferred) do
    of_match_vars(match_vars, var_ctx, level, matches, vars, inferred)
  end
  defp of_match_vars([], vars, inferred) do
    {vars, inferred}
  end

  defp of_match_vars([{_, _, counter} | match_vars], var_ctx,
                     level, matches, vars, inferred) do
    of_match_vars(match_vars, var_ctx, level, matches,
                  Map.put(vars, var_ctx, {level, Map.fetch!(inferred, counter)}),
                  Map.delete(inferred, counter))
  end
  defp of_match_vars([], _var_ctx, _level, matches, vars, inferred) do
    of_match_vars(matches, vars, inferred)
  end

  ## Clauses

  # TODO: Check if clauses have overlapping types
  defp of_fn(clauses, state) do
    of_fn(clauses, state, [], %{}, state)
  end

  defp of_fn([clause | clauses], state, acc_clauses, acc_inferred, acc_state) do
    with {:ok, head, body, clause_state} <- of_fn_clause(clause, acc_state) do
      {clause, clause_inferred, state_inferred} = of_fn_expand(head, body, clause_state)
      acc_inferred = Map.merge(acc_inferred, clause_inferred)
      acc_state = %{replace_vars(clause_state, state) | inferred: state_inferred}
      of_fn(clauses, state, [clause | acc_clauses], acc_inferred, acc_state)
    end
  end
  defp of_fn([], _state, acc_clauses, acc_inferred, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_inferred, acc_state}
  end

  defp of_fn_clause({:->, _, [args, body]}, state) do
    with {:ok, args, head_state} <- of_pattern(args, state),
         %{match: match, vars: vars} = head_state,
         head_state = %{head_state | vars: Map.merge(vars, match)},
         {:ok, body, body_state} <- of(body, head_state) do
      {:ok, args, body, %{body_state | match: match}}
    end
  end

  defp of_fn_expand(head, body, clause_state) do
    %{inferred: inferred, levels: levels, level: level, match: match} = clause_state

    # Get all variables introduced in the function head,
    # including the ones that may have come as part of
    # applying to a variable.
    #
    # Then we check they belong to the current level and
    # make sure they are either free or are a supertype.
    match_counters =
      for {_, {_, match_vars}} <- match,
          {:var, _, counter} <- match_vars,
          do: counter

    clause_counters =
      of_fn_match(match_counters, inferred, level, levels, [])

    # We will expand everything that is not in the clause
    # counters and belong to the current level.
    expand = Map.drop(inferred, clause_counters)
    {body, {unused_counters, rec_counters}} =
      bind_level(body, clause_counters, expand, level, levels)

    # Any recursive counter should not be expanded
    expand = Map.drop(expand, rec_counters)
    clause_counters = Enum.uniq(rec_counters) ++ clause_counters

    # If there is a clause variable that was not used in the body,
    # and it is not free, we shall expand it.
    {unused_counters, expand} =
      Enum.reduce(unused_counters, {[], expand}, fn counter, {counters, expand} ->
        case Map.get(inferred, counter, []) do
          [] -> {counters, expand}
          types -> {[counter | counters], Map.put(expand, counter, types)}
        end
      end)

    # Go through all arguments and expand what we are not keeping.
    {head, {_, rec_counters}} =
      bind_level_args(head, [], expand, level, levels)

    clause_counters = (clause_counters -- unused_counters) ++ rec_counters

    clause_inferred =
      for counter <- clause_counters,
          {value, _} = bind_level(Map.get(inferred, counter, []), [], expand, level, levels),
          do: {counter, value},
          into: %{}

    {{head, body}, clause_inferred, Map.drop(inferred, clause_counters)}
  end

  defp of_fn_match([key | keys], inferred, level, levels, acc) do
    case Map.fetch!(levels, key) do
      {^level, _applies, deps} ->
        value = Map.get(inferred, key, [])
        acc = if Union.supertype?(value, false), do: [key | acc], else: acc
        acc = of_fn_match(deps, inferred, level, levels, acc)
        of_fn_match(keys, inferred, level, levels, acc)
      {_, _, _} ->
        of_fn_match(keys, inferred, level, levels, acc)
    end
  end
  defp of_fn_match([], _inferred, _level, _levels, acc) do
    acc
  end

  ## Recursive definitions

  defp of_def(clauses, state) do
    of_def(clauses, [], %{}, state)
  end

  defp of_def([clause | clauses], acc_clauses, acc_inferred, acc_state) do
    with {:ok, head, body, clause_state} <- of_fn_clause(clause, acc_state) do
      %{inferred: clause_inferred, counter: counter} = clause_state
      acc_state = %{acc_state | counter: counter}
      acc_inferred = Map.merge(acc_inferred, clause_inferred)
      of_def(clauses, [{{head, body}, clause_state} | acc_clauses], acc_inferred, acc_state)
    end
  end
  defp of_def([], acc_clauses, acc_inferred, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_inferred, acc_state}
  end

  # This function receives all clauses and their state as well as
  # all type variables inferred across all clauses and invokes
  # the recursive args across all clauses in order to define the
  # recursive types.
  #
  # The of_recur/6 function traverses all recursive clauses and,
  # at the end, defines the overall function type.
  defp of_recur(clauses_state, clauses_inferred, %{counter: counter}) do
    # Extract only the clauses to make it easier to apply later on.
    clauses = for {clause, _} <- clauses_state, do: clause

    # Retrieve all free variables. Free variables can lead to
    # dependencies between clauses in cases such as this:
    #
    #     fn
    #       {:+, num} -> recur(num)
    #       num -> num
    #     end
    #
    # So if we have free variables, we need to make sure they
    # are bound.
    free = for {k, []} <- clauses_inferred, do: k

    of_recur(clauses_state, clauses, free, clauses_inferred, counter, [])
  end

  defp of_recur([{_, %{rec: rec}} = clause_state | clauses_state],
                clauses, free, inferred, counter, acc) when rec == %{} do
    of_recur(clauses_state, clauses, free, inferred, counter, [clause_state | acc])
  end
  defp of_recur([{clause, %{rec: recs, inferred: clause_inferred} = state} | clauses_state],
                clauses, free, inferred, counter, acc) do
    keys = Map.keys(clause_inferred)
    state = %{state | counter: counter}
    case of_recur_rec(Map.to_list(recs), state, clauses, free -- keys, keys, clause_inferred, inferred) do
      {:ok, %{counter: counter} = state} ->
        of_recur(clauses_state, clauses, free, inferred, counter, [{clause, state} | acc])
      {:error, _, _} = error ->
        error
    end
  end
  defp of_recur([], _clauses, free, _inferred, _counter, acc) do
    {clauses, inferred} =
      Enum.map_reduce(:lists.reverse(acc), %{}, fn {{head, body}, state}, inferred ->
        {clause, clause_inferred, _} = of_fn_expand(head, body, state)
        {clause, Map.merge(inferred, clause_inferred)}
      end)

    {:ok, clauses, inferred}
  end

  # This function applies the different recursion arguments for a given
  # clause over all clauses (including itself). `clause_inferred` keeps
  # what was inferred for the current clause, `acc_inferred` keeps what
  # was inferred across all clauses.
  #
  # The goal of this code is to refine the inferred types for the current
  # clause (clause_inferred) and replicate those changes on acc_inferred.
  defp of_recur_rec([{args, {meta, left_return}} | recs],
                    state, clauses, free, keys, clause_inferred, acc_inferred) do
    with {:ok, right_return, state} <-
           of_fn_apply(clauses, clause_inferred, meta, args, %{state | inferred: acc_inferred}) do
      %{inferred: inferred} = state

      right_return = bind_if(right_return, & &1 in free, inferred, [])
      case unify_return(left_return, right_return, clause_inferred, inferred, inferred) do
        {:match, inferred} ->
          clause_inferred = Map.take(inferred, keys)
          acc_inferred = Map.merge(acc_inferred, clause_inferred)
          of_recur_rec(recs, state, clauses, free, keys, clause_inferred, acc_inferred)
        _ ->
          error(meta, {:recur_return, left_return, right_return})
      end
    end
  end
  defp of_recur_rec([], state, _clauses, _free, _keys, _clause_inferred, inferred) do
    {:ok, %{state | inferred: inferred}}
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

  defp of_var({:fn, clauses, inferred, arity}, %{counter: counter} = state) do
    {:replace, rewrite, _} = of_var_rewrite({:fn, clauses, inferred, arity}, state)
    {:replace, rewrite, %{state | counter: counter + 1}}
  end
  defp of_var(_type, acc) do
    {:ok, acc}
  end

  defp of_var_rewrite({:fn, clauses, inferred, arity}, %{counter: counter} = state) do
    clauses =
      for {head, body} <- clauses do
        {head, _} = Union.traverse_args(head, state, &of_var_rewrite/2)
        {body, _} = Union.traverse(body, state, &of_var_rewrite/2)
        {head, body}
      end

    inferred = for {k, v} <- inferred, do: {[counter | k], v}, into: %{}
    {:replace, [{:fn, clauses, inferred, arity}], state}
  end
  defp of_var_rewrite({:var, _, key} = var, state) do
    %{counter: counter, inferred: inferred, levels: levels, level: level} = state
    case Map.get(levels, key) do
      {key_level, _, _} when key_level <= level ->
        {:ok, state}
      _ ->
        {:replace, of_var_rewrite_free([var], counter, inferred), state}
    end
  end
  defp of_var_rewrite(_type, state) do
    {:ok, state}
  end

  defp of_var_rewrite_free([{:var, ctx, key} | types], counter, inferred) do
    case Map.get(inferred, key, []) do
      [] -> [{:var, ctx, [counter | key]} | of_var_rewrite_free(types, counter, inferred)]
      more -> of_var_rewrite_free(more ++ types, counter, inferred)
    end
  end
  defp of_var_rewrite_free([type | types], counter, inferred) do
    [type | of_var_rewrite_free(types, counter, inferred)]
  end
  defp of_var_rewrite_free([], _counter, _inferred) do
    []
  end

  ## Patterns

  defp of_pattern(args, state) do
    of_pattern(args, [], %{state | match: %{}})
  end

  defp of_pattern([arg | args], acc, state) do
    with {:ok, arg, state} <- of_pattern_each(arg, state) do
      of_pattern(args, [arg | acc], state)
    end
  end
  defp of_pattern([], acc, state) do
    {:ok, :lists.reverse(acc), state}
  end

  defp of_pattern_each({:::, meta, [{var, _, ctx}, ast]}, state)
       when is_atom(var) and (is_atom(ctx) or is_integer(ctx)) do
    case Union.ast_to_types(ast) do
      {:ok, types} ->
        of_pattern_bound_var(meta, {var, ctx}, types, state)
      {:error, error} ->
        error(meta, {:ast_to_type, error, ast})
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

  defp of_pattern_var(_meta, var_ctx, %{match: match} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, {_level, return}} ->
        ok(return, state)
      :error ->
        of_pattern_bind_var(match, var_ctx, [], state)
    end
  end

  defp of_pattern_bound_var(meta, var_ctx, types, %{match: match, inferred: inferred} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, {_level, return}} ->
        previous = for {_, _, counter} <- return,
                       type <- Map.fetch!(inferred, counter),
                       do: type

        if Union.same?(previous, types) do
          ok(return, state)
        else
          error(meta, {:bound_var, var_ctx, previous, types})
        end
      :error ->
        of_pattern_bind_var(match, var_ctx, types, state)
    end
  end

  defp of_pattern_bind_var(match, var_ctx, [], state) do
    %{counter: counter, inferred: inferred, level: level, levels: levels} = state
    inferred = Map.put(inferred, counter, [])
    vars = [{:var, var_ctx, counter}]
    match = Map.put(match, var_ctx, {level, vars})
    levels = Map.put(levels, counter, {level, [], []})
    state = %{state | match: match, counter: counter + 1, inferred: inferred, levels: levels}
    ok(vars, state)
  end

  defp of_pattern_bind_var(match, var_ctx, types, state) do
    %{counter: counter, inferred: inferred, level: level, levels: levels} = state

    {vars, {counter, inferred, levels}} =
      Enum.map_reduce(types, {counter, inferred, levels}, fn type, {counter, inferred, levels} ->
        inferred = Map.put(inferred, counter, [type])
        levels = Map.put(levels, counter, {level, [], []})
        {{:var, var_ctx, counter}, {counter + 1, inferred, levels}}
      end)

    match = Map.put(match, var_ctx, {level, vars})
    state = %{state | match: match, counter: counter, inferred: inferred, levels: levels}
    ok(vars, state)
  end

  ## Helpers

  defp literal(value, state, _fun) when is_integer(value) do
    ok([:integer], state)
  end
  defp literal(value, state, _fun) when is_atom(value) do
    ok([{:atom, value}], state)
  end
  defp literal([], state, _fun) do
    ok([:empty_list], state)
  end
  defp literal([{:|, _, [left, right]}], state, fun) do
    with {:ok, args, _arity, state} <- args([left, right], state, fun) do
      types = Union.permute_args(args, fn [left, right] -> {:cons, left, right} end)
      ok(types, state)
    end
  end
  defp literal([left | right], state, fun) do
    with {:ok, args, _arity, state} <- args([left, right], state, fun) do
      types = Union.permute_args(args, fn [left, right] -> {:cons, left, right} end)
      ok(types, state)
    end
  end
  defp literal({left, right}, state, fun) do
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      types = Union.permute_args(args, &{:tuple, &1, arity})
      ok(types, state)
    end
  end
  defp literal({:{}, _, args}, state, fun) do
    with {:ok, args, arity, state} <- args(args, state, fun) do
      types = Union.permute_args(args, &{:tuple, &1, arity})
      ok(types, state)
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

  # :counter keeps the variable counter (de brujin indexes)
  # :level keeps the function level
  # The :match map keeps all Elixir variables defined in a match
  # The :vars map keeps all Elixir variables and their types
  # The :inferred map keeps track of all inferred types
  # The :levels map keeps the variable level as well as all related level variables
  # The :rec keeps all recursive calls that must be resolved later
  @state %{counter: 0, level: 0, match: %{}, vars: %{}, inferred: %{},
           levels: %{}, rec: %{}}

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
