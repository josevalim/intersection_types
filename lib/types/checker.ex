defmodule Types.Checker do
  # The type checker engine.

  alias Types.Union

  def init do
    %{}
  end

  def expr(integer, state) when is_integer(integer) do
    ok(integer, Union.build(:integer), state)
  end

  def expr(atom, state) when is_atom(atom) do
    ok(atom, Union.build({:atom, atom}), state)
  end

  @compile {:inline, ok: 3}

  defp ok(expr, types, state) do
    {expr, types, state}
  end
end
