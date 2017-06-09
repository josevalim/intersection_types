defmodule Types.Checker do
  @moduledoc false

  alias Types.Union

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
  def unify(left, right, vars, acc_vars) do
    unify(left, right, vars, acc_vars, [], true)
  end

  defp unify([left | lefties], righties, vars, acc_vars, matched, matched?) do
    unify(left, righties, vars, acc_vars, lefties, righties, matched, matched?)
  end
  defp unify([], _righties, _vars, acc_vars, matched, true) do
    {:match, matched, acc_vars}
  end
  defp unify([], _righties, _vars, acc_vars, matched, false) do
    {:disjoint, matched, acc_vars}
  end

  defp unify(left, [type | types], vars, acc_vars, lefties, righties, matched, matched?) do
    case unify_each(left, type, vars, acc_vars) do
      {:match, acc_vars} ->
        unify(left, types, vars, acc_vars, lefties, righties, [type | matched], matched?)
      :disjoint ->
        unify(left, types, vars, acc_vars, lefties, righties, matched, false)
    end
  end
  defp unify(_left, [], vars, acc_vars, lefties, righties, matched, matched?) do
    unify(lefties, righties, vars, acc_vars, matched, matched?)
  end

  defp unify_each(type, type, _vars, acc_vars) do
    {:match, acc_vars}
  end

  defp unify_each({:var, _, key1}, {:var, _, key2} = right, vars, acc_vars) do
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
        with {_, [_ | _] = match, acc_vars} <-
               unify(left_value, right_value, vars, acc_vars) do
          acc_vars =
            acc_vars
            |> Map.update(key1, match, &Union.union(&1 -- left_value, match))
            |> Map.update(key2, match, &Union.union(&1 -- right_value, match))
          {:match, acc_vars}
        else
          _ -> :disjoint
        end
    end
  end

  defp unify_each({:var, _, key}, type, vars, acc_vars) do
    case Map.get(vars, key, []) do
      [] ->
        {:match, Map.update(acc_vars, key, [type], &Union.union(&1, [type]))}
      value ->
        case unify(value, [type], vars, acc_vars) do
          {_, [_ | _] = match, acc_vars} ->
            acc_vars = Map.update(acc_vars, key, match, &Union.union(&1 -- value, match))
            {:match, acc_vars}
          _ ->
            :disjoint
        end
    end
  end

  # Variables on the right side always need to match.
  defp unify_each(type, {:var, _, key}, vars, acc_vars) do
    case Map.get(vars, key, []) do
      [] ->
        {:match, Map.update(acc_vars, key, [type], &Union.union(&1, [type]))}
      value ->
        case unify([type], value, vars, acc_vars) do
          {_, [_ | _] = match, acc_vars} ->
            acc_vars = Map.update(acc_vars, key, match, &Union.union(&1 -- value, match))
            {:match, acc_vars}
          _ ->
            :disjoint
        end
    end
  end

  defp unify_each({:fn, lefties, left_inferred, arity}, {:fn, righties, right_inferred, arity},
                  vars, acc_vars) do
    lefties =
      for {head, body} <- lefties do
        permuted = Union.permute_args(head, arity, fn head, _ -> head end)
        {permuted, body}
      end

    righties =
      for {head, body} <- righties,
          permuted <- Union.permute_args(head, arity, fn head, _ -> head end) do
        {permuted, body}
      end

    unify_fn(lefties, righties, left_inferred, right_inferred, vars, vars, acc_vars)
  end

  defp unify_each({:cons, left1, right1}, {:cons, left2, right2}, vars, acc_vars) do
    case unify_paired([left1, right1], [left2, right2], vars, acc_vars) do
      {:match, _, acc_vars} ->
        {:match, acc_vars}
      :disjoint ->
        :disjoint
    end
  end

  defp unify_each({:tuple, lefties, arity}, {:tuple, righties, arity},
                  vars, acc_vars) do
    case unify_paired(lefties, righties, vars, acc_vars) do
      {:match, _, acc_vars} ->
        {:match, acc_vars}
      :disjoint ->
        :disjoint
    end
  end

  defp unify_each(left, right, _vars, acc_vars) do
    case Union.qualify(left, right) do
      :equal -> {:match, acc_vars}
      :superset -> {:match, acc_vars}
      :subset -> :disjoint
      :disjoint -> :disjoint
    end
  end

  # Unifying functions is quite complex as it requires tracking
  # different kinds of variables and renewing them at different
  # stages.
  #
  # We will explore those scenarios below.
  #
  # ## Example 1
  #
  #     ((a -> b) -> (a -> b)) <~> (:foo -> :bar; :bar -> :baz)
  #
  # should unify to:
  #
  #     (:foo | :bar; :bar | :baz)
  #
  # Note the left side is made of three functions, where the variables
  # (a -> b) are defined in the outermost one. This means that, we
  # need to know which variables have been in the outermost function
  # and properly pass them forward for "cleaning" the inferred variables.
  defp unify_fn([{left_heads, left_body} | lefties], righties, left_inferred, right_inferred,
                vars, type_vars, acc_vars) do
    case unify_fn(left_heads, left_body, righties, left_inferred, right_inferred,
                  vars, type_vars, acc_vars, false) do
      {type_vars, acc_vars} ->
        unify_fn(lefties, righties, left_inferred, right_inferred, vars, type_vars, acc_vars)
      :error ->
        :disjoint
    end
  end
  defp unify_fn([], _righties, _left_inferred, _right_inferred, _vars, _type_vars, acc_vars) do
    {:match, acc_vars}
  end

  defp unify_fn(left_heads, left_body, [{right_head, right_body} | clauses],
                left_inferred, right_inferred, vars, type_vars, acc_vars, matched?) do
    vars = Map.merge(vars, right_inferred)
    type_vars = Map.merge(type_vars, right_inferred)

    match =
      Enum.find_value(left_heads, fn left_head ->
        case unify_paired(right_head, left_head, type_vars, %{}) do
          {:match, _, _} = match -> match
          _ -> nil
        end
      end)

    with {:match, _, new_vars} <- match,
         type_vars = Map.merge(type_vars, new_vars),
         acc_vars = Map.merge(acc_vars, new_vars, fn _, v1, v2 -> Union.union(v1, v2) end),
         right_body = bind(right_body, right_inferred, type_vars),
         {:match, _, new_vars} <-
           unify(left_body, right_body, type_vars, %{}) do
      unify_fn(left_heads, left_body, clauses, left_inferred, right_inferred, vars,
               Map.merge(type_vars, new_vars),
               Map.merge(acc_vars, new_vars, fn _, v1, v2 -> Union.union(v1, v2) end), true)
    else
      _ ->
        unify_fn(left_heads, left_body, clauses, left_inferred, right_inferred,
                 vars, type_vars, acc_vars, matched?)
    end
  end
  defp unify_fn(_, _, [], _left_inferred, _right_inferred, _vars, type_vars, acc_vars, true) do
    {type_vars, acc_vars}
  end
  defp unify_fn(_, _, [], _left_inferred, _right_inferred, _vars, _type_vars, _acc_vars, false) do
    :error
  end

  defp unify_paired(lefties, righties, vars, acc_vars) do
    unify_paired(lefties, righties, vars, acc_vars, [])
  end
  defp unify_paired([left | lefties], [right | righties], vars, acc_vars, matched) do
    case unify_each(left, right, vars, %{}) do
      {:match, new_vars} ->
        vars = Map.merge(vars, new_vars)
        acc_vars = Map.merge(acc_vars, new_vars, fn _, v1, v2 -> Union.union(v1, v2) end)
        unify_paired(lefties, righties, vars, acc_vars, [right | matched])
      :disjoint ->
        :disjoint
    end
  end
  defp unify_paired([], [], _vars, acc_vars, matched) do
    {:match, :lists.reverse(matched), acc_vars}
  end

  # TODO: Review or remove me
  def unify_args([left | lefties], [right | righties], vars, acc_vars) do
    case unify(left, right, vars, acc_vars) do
      {:match, _, acc_vars} ->
        unify_args(lefties, righties, vars, acc_vars)
      {:disjoint, _, _} ->
        :disjoint
    end
  end
  def unify_args([], [], _vars, acc_vars) do
    {:match, acc_vars}
  end

  @doc """
  Binds the variables to their types.
  """
  def bind(types, only, vars) do
    Union.traverse(types, :ok, fn
      {:var, _, counter}, acc ->
        case only do
          %{^counter => _} ->
            case Map.get(vars, counter, []) do
              [_ | _] = existing ->
                {:union, bind(existing, only, vars), acc}
              _ ->
                {:ok, acc}
            end
          %{} ->
            {:ok, acc}
        end
      _, acc ->
        {:ok, acc}
    end) |> elem(0)
  end

  # Similar to bind but checks exclusively for current levels.
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
              {existing, acc} -> {:union, existing, acc}
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
    with {:ok, clauses, inferred, state} <- of_fn_clauses(clauses, %{state | level: level + 1}) do
      [{head, _} | _] = clauses
      ok([{:fn, clauses, inferred, length(head)}], %{state | level: level})
    end
  end

  defp of({:__block__, _meta, args}, state) do
    of_block(args, state)
  end

  # TODO: This is a special case for recursion
  defp of({:=, _, [{:recur, _, _}, {:fn, _, clauses}]}, state) do
    with {:ok, clauses_state, clause_inferred, state} <- of_def(clauses, state),
         {:ok, clauses, inferred} <- of_recur(clauses_state, clause_inferred) do
      ok([{:fn, clauses, inferred, 1}], state)
    end
  end

  defp of({:=, meta, [left, right]}, state) do
    with {:ok, right, right_state} <- of(right, state),
         {:ok, [left], left_state} <- of_pattern([left], replace_vars(right_state, state)) do
      state = lift_vars(left_state, right_state)
      %{match: match, vars: vars, inferred: inferred} = state

      case of_match(left, right, inferred, inferred) do
        {:ok, new_inferred} ->
          case of_match_vars(Map.to_list(match), vars, inferred, new_inferred) do
            {vars, new_inferred} -> ok(right, %{state | inferred: new_inferred, vars: vars})
            :error -> error(meta, {:match_binding, left})
          end
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

  defp of({name, _, _} = value, state) when name in [:{}, :<<>>] do
    literal(value, state, &of/2)
  end

  # TODO: This is a special case for recursion
  defp of({name, meta, args}, state) when is_list(args) do
    if name == :recur do
      with {:ok, args, _arity, state} <- args(args, state, &of/2) do
        %{rec: rec, counter: counter, inferred: inferred, levels: levels, level: level} = state
        case Map.fetch(rec, args) do
          {:ok, {_meta, return}} ->
            ok(return, state)
          :error ->
            return = [{:var, {:recur, Elixir}, counter}]
            state = %{state | inferred: Map.put(inferred, counter, []),
                              counter: counter + 1,
                              levels: Map.put(levels, counter, {level, [], []}),
                              rec: Map.put(rec, args, {meta, return})}
            ok(return, state)
        end
      end
    else
      raise "only recur is supported"
    end
  end

  defp of(value, state) do
    literal(value, state, &of/2)
  end

  ## Apply

  defp of_apply([{:fn, clauses, fn_inferred, arity} | types], arity, meta, args,
                %{inferred: inferred} = state, acc, fun_state) do
    with {:ok, inferred, return} <- of_fn_apply(clauses, fn_inferred, meta, args, inferred) do
      of_apply(types, arity, meta, args, %{state | inferred: inferred},
               Union.union(acc, return), fun_state)
    end
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
    %{inferred: inferred, counter: counter, levels: levels} = state
    {var_level, var_applies, var_deps} = Map.fetch!(levels, var_counter)

    # We allow only a limited for of level 2 intersections where
    # type variables can only be shared between bodies. This means
    # we need to carefully check the argument types input considering
    # that:
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
    #
    case of_var_apply_recur([arg_types], var_counter, var_applies, var_level, levels) do
      {{:occurs, counter}, _move_up} ->
        error(meta, {:occurs, [{:var, var_ctx, var_counter}], counter, arg_types, arity})
      {:self, _move_up} ->
        error(meta, {:recursive_fn, [{:var, var_ctx, var_counter}], arg_types, arity})
      {var_recur, move_up} ->
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
              for {:fn, fn_clauses, fn_inferred, arity} <- types do
                {:fn, of_var_apply_clauses(fn_clauses, [arg_types], return), fn_inferred, arity}
              end

            levels =
              Enum.reduce(move_up, levels, fn up_counter, levels ->
                Map.update!(levels, up_counter, fn {_, applies, deps} ->
                  {var_level, applies, deps}
                end)
              end)

            inferred =
              inferred
              |> Map.put(counter, [])
              |> Map.put(var_counter, types)

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
    Union.traverse_args(types, {[], []}, fn
      {:var, _, ^var_counter}, {_, acc_levels} ->
        {:ok, {:self, acc_levels}}
      {:var, _, counter}, {acc_applies, acc_levels} when is_list(acc_applies) ->
        if counter in var_applies do
          {:ok, {[counter | acc_applies], acc_levels}}
        else
          {level, _applies, deps} = Map.fetch!(levels, counter)
          cond do
            var_counter in deps ->
              {:ok, {{:occurs, counter}, acc_levels}}
            level > var_level ->
              {:ok, {acc_applies, [counter | acc_levels]}}
            true ->
              {:ok, {acc_applies, acc_levels}}
          end
        end
      _type, acc ->
        {:ok, acc}
    end) |> elem(1)
  end

  defp of_var_apply_unify(key, args, arity, inferred, recur) do
    case Map.fetch!(inferred, key) do
      [] ->
        {:nomatch, [{:fn, [], %{}, arity}]}
      existing ->
        funs = for {:fn, _, _, ^arity} = fun <- existing, do: fun

        {case recur do
          [] -> of_var_apply_unify_equal(funs, args, inferred)
          _  -> of_var_apply_unify_recur(funs, args, recur, inferred, [], inferred)
         end, funs}
    end
  end

  defp of_var_apply_unify_recur([{:fn, clauses, _, _} | funs], args, recur, inferred, sum, acc_inferred) do
    of_var_apply_unify_recur(clauses, funs, args, recur, inferred, sum, acc_inferred)
  end
  defp of_var_apply_unify_recur([], _args, recur, _inferred, sum, acc_inferred) do
    if acc_inferred |> Map.take(recur) |> Enum.all?(fn {_, types} -> types != [] end) do
      {:match, sum, acc_inferred}
    else
      :recursive
    end
  end

  defp of_var_apply_unify_recur([{head, [{:var, _, var_recur}] = body} | clauses],
                                funs, args, recur, inferred, sum, acc_inferred) do
    with true <- var_recur in recur,
         {:match, acc_inferred} <- unify_args(args, head, inferred, acc_inferred) do
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

  defp of_var_apply_unify_equal([{:fn, clauses, _, _} | funs], args, inferred) do
    of_var_apply_unify_equal(clauses, funs, args, inferred)
  end
  defp of_var_apply_unify_equal([], _args, _inferred) do
    :nomatch
  end

  defp of_var_apply_unify_equal([{args, body} | _clauses], _funs, args, inferred) do
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
      Enum.split_while(clauses, fn {head, _} ->
        Union.qualify_args(head, args) != :superset
      end)
    pre ++ [{args, return} | pos]
  end

  ### Fn Apply

  defp of_fn_apply(clauses, fn_inferred, meta, args, inferred) do
    inferred = Map.merge(inferred, fn_inferred)

    # TODO: Refactor shared permutation logic
    permuted_clauses =
      for {head, body} <- clauses,
          permuted <- Union.permute_args(head, 0, fn head, _ -> head end) do
        {permuted, body}
      end

    permuted_args =
      Union.permute_args(args, 0, fn args, _ -> args end)

    case of_fn_apply_each(permuted_args, permuted_clauses, inferred, %{}, []) do
      {:ok, acc_inferred, acc_body} ->
        {:ok, acc_inferred, acc_body}
      {:error, no_match} ->
        error(meta, {:disjoint_apply, no_match, clauses, args})
    end
  end

  # If we have matched all arguments and we haven't inferred anything new,
  # it means they are literals and there is no need for an exhaustive search.
  defp of_fn_apply_each([arg | args], clauses, inferred, acc_inferred, acc_body) do
    # TODO: Remove acc_inferred. It is being used as a fast check for changes.
    {match?, acc_inferred, acc_body} =
      Enum.reduce_while(clauses, {false, acc_inferred, acc_body},
        fn {head, body}, {_, acc_inferred, acc_body} = acc ->
          case unify_paired(head, arg, inferred, %{}) do
            {:match, _, new_inferred} when new_inferred == %{} ->
              acc_inferred = of_fn_apply_keep(new_inferred, acc_inferred)
              acc_body = Union.union(acc_body, body)
              {:halt, {true, acc_inferred, acc_body}}
            {:match, _, new_inferred} ->
              acc_inferred = of_fn_apply_keep(new_inferred, acc_inferred)
              acc_body = Union.union(acc_body, body)
              {:cont, {true, acc_inferred, acc_body}}
            _ ->
              {:cont, acc}
          end
      end)

    if match? do
      of_fn_apply_each(args, clauses, inferred, acc_inferred, acc_body)
    else
      {:error, arg}
    end
  end
  defp of_fn_apply_each([], _clauses, inferred, acc_inferred, acc_body) do
    {:ok, Map.merge(inferred, acc_inferred), acc_body}
  end

  defp of_fn_apply_keep(new_inferred, acc_inferred) do
    Enum.reduce(new_inferred, acc_inferred, fn
      # TODO: This deletion will cause trouble with multiple arguments.
      # It is likely we need to generate a fake variable that points to
      # k instead.
      {k, []}, acc -> Map.delete(acc, k)
      {k, v}, acc  -> Map.update(acc, k, v, &Union.union(&1, v))
    end)
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
    # TODO: Refactor and figure out acc_inferred
    # TODO: Maybe get rid of subset matches
    {match?, acc_inferred} =
      Enum.reduce_while(lefties, {false, acc_inferred},
        fn left, {_, acc_inferred} = acc ->
          case unify_each(left, right, inferred, acc_inferred) do
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
  defp of_match(_lefties, [], _inferred, acc_inferred) do
    {:ok, acc_inferred}
  end

  # We check the original match bindings because we don't allow binding
  # with `::` on the left side of `=` for simplicity reasons. If desired,
  # this could be implemented by introducing a new state field that keeps
  # track exclusively of `::` which are verified at the end of every scope.
  # The current implementation relies on `match` variables for that (as to
  # not introduce a new field).
  defp of_match_vars([{var_ctx, {level, [{_, _, counter}]}} | matches], vars, bindings, inferred) do
    case Map.fetch!(bindings, counter) do
      [] ->
        of_match_vars(matches,
                      Map.put(vars, var_ctx, {level, Map.fetch!(inferred, counter)}),
                      bindings, Map.delete(inferred, counter))
      _ ->
        :error
    end
  end
  defp of_match_vars([], vars, _bindings, inferred) do
    {vars, inferred}
  end

  ## Clauses

  # TODO: Check if clauses have overlapping types
  defp of_fn_clauses(clauses, state) do
    of_fn_clauses(clauses, state, [], %{}, state)
  end

  defp of_fn_clauses([clause | clauses], state, acc_clauses, acc_inferred, acc_state) do
    with {:ok, head, body, clause_state} <- of_fn_clause(clause, acc_state) do
      {clause, clause_inferred, state_inferred} = of_fn_expand(head, body, clause_state)
      acc_inferred = Map.merge(acc_inferred, clause_inferred)
      acc_state = %{replace_vars(clause_state, state) | inferred: state_inferred}
      of_fn_clauses(clauses, state, [clause | acc_clauses], acc_inferred, acc_state)
    end
  end
  defp of_fn_clauses([], _state, acc_clauses, acc_inferred, acc_state) do
    {:ok, :lists.reverse(acc_clauses), acc_inferred, acc_state}
  end

  defp of_fn_clause({:->, meta, [args, body]}, state) do
    with {:ok, args, head_state} <- of_pattern(args, state),
         %{match: match, vars: vars, inferred: old_inferred} = head_state,
         head_state = %{head_state | vars: Map.merge(vars, match)},
         {:ok, body, %{inferred: new_inferred} = body_state} <- of(body, head_state) do
      case of_fn_verify(match, old_inferred, new_inferred) do
        {:ok, _} -> {:ok, args, body, %{body_state | match: match}}
        {:error, var, old, new} -> error(meta, {:restricted_head, var, old, new})
      end
    end
  end

  defp of_fn_verify(match, old_inferred, new_inferred) do
    Enum.reduce_while(match, {:ok, new_inferred}, fn
      {_, {_, [{_, _, counter} = var]}}, {:ok, new_inferred} ->
        old = Map.get(old_inferred, counter, [])
        {new, new_inferred} = Map.pop(new_inferred, counter)
        if old == [] or old == new do
          {:cont, {:ok, new_inferred}}
        else
          {:halt, {:error, var, old, new}}
        end
    end)
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
      for {_, {_, [{:var, _, counter}]}} <- match, do: counter

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
        acc = if Union.supertype?(value), do: [key | acc], else: acc
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

  defp of_recur(clauses_state, clause_inferred) do
    clauses = for {clause, _} <- clauses_state, do: clause
    of_recur(clauses_state, clauses, clause_inferred, [])
  end

  defp of_recur([{_, %{rec: rec}} = clause_state | clauses_state],
                clauses, inferred, acc) when rec == %{} do
    of_recur(clauses_state, clauses, inferred, [clause_state | acc])
  end
  defp of_recur([{clause, %{rec: recs, inferred: clause_inferred} = state} | clauses_state],
                clauses, inferred, acc) do
    case of_recur_rec(Map.to_list(recs), clauses, clause_inferred, inferred) do
      {:ok, clause_inferred} ->
        of_recur(clauses_state, clauses, inferred,
                 [{clause, %{state | inferred: Map.merge(inferred, clause_inferred)}} | acc])
      {:error, _, _} = error ->
        error
    end
  end
  defp of_recur([], _clauses, _inferred, acc) do
    {clauses, inferred} =
      Enum.map_reduce(:lists.reverse(acc), %{}, fn {{head, body}, state}, acc_inferred ->
        {clause, clause_inferred, _} = of_fn_expand(head, body, state)
        {clause, Map.merge(acc_inferred, clause_inferred)}
      end)
    {:ok, clauses, inferred}
  end

  defp of_recur_keep(inferred, clause_inferred, acc_inferred) do
    Enum.reduce(clause_inferred, {%{}, acc_inferred}, fn {k, _}, {clause_inferred, acc_inferred} ->
      v = Map.fetch!(inferred, k)
      {Map.put(clause_inferred, k, v), Map.put(acc_inferred, k, v)}
    end)
  end

  defp of_recur_rec([{args, {meta, left_return}} | recs], clauses, clause_inferred, acc_inferred) do
    with {:ok, inferred, right_return} <-
           of_fn_apply(clauses, clause_inferred, meta, args, acc_inferred) do
      case unify(left_return, right_return, inferred, inferred) do
        {:match, _, inferred} ->
          # One every invocation, we only keep the variables that matters
          # for the current clause. That's because acc_inferred has all of
          # the variables but we don't want the binding of one clause to
          # affect the others. This is solved on regular apply by generalization,
          # which we could also have used here.
          {clause_inferred, acc_inferred} = of_recur_keep(inferred, clause_inferred, acc_inferred)
          of_recur_rec(recs, clauses, clause_inferred, acc_inferred)
        _ ->
          error(meta, {:recur_return, left_return, right_return})
      end
    end
  end
  defp of_recur_rec([], _original, clause_inferred, _inferred) do
    {:ok, clause_inferred}
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
      {:ok, {_level, return}} -> ok(return, state)
      :error -> of_pattern_bind_var(match, var_ctx, [], state)
    end
  end

  defp of_pattern_bound_var(meta, var_ctx, types, %{match: match, inferred: inferred} = state) do
    case Map.fetch(match, var_ctx) do
      {:ok, {_level, [{:var, _, counter}] = return}} ->
        case Map.fetch!(inferred, counter) do
          ^types -> ok(return, state)
          other -> error(meta, {:bound_var, var_ctx, other, types})
        end
      :error ->
        of_pattern_bind_var(match, var_ctx, types, state)
    end
  end

  defp of_pattern_bind_var(match, var_ctx, types, state) do
    %{counter: counter, inferred: inferred, level: level, levels: levels} = state
    inferred = Map.put(inferred, counter, types)
    return = [{:var, var_ctx, counter}]
    match = Map.put(match, var_ctx, {level, return})
    levels = Map.put(levels, counter, {level, [], []})
    ok(return, %{state | match: match, counter: counter + 1, inferred: inferred, levels: levels})
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
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      types =
        Union.permute_args(args, arity, fn [left, right], _arity ->
          {:cons, left, right}
        end)
      ok(types, state)
    end
  end
  defp literal([left | right], state, fun) do
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      types =
        Union.permute_args(args, arity, fn [left, right], _arity ->
          {:cons, left, right}
        end)
      ok(types, state)
    end
  end
  defp literal({left, right}, state, fun) do
    with {:ok, args, arity, state} <- args([left, right], state, fun) do
      types = Union.permute_args(args, arity, &{:tuple, &1, &2})
      ok(types, state)
    end
  end
  defp literal({:{}, _, args}, state, fun) do
    with {:ok, args, arity, state} <- args(args, state, fun) do
      types = Union.permute_args(args, arity, &{:tuple, &1, &2})
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
