defmodule Types.Checker do
  # The type checker engine.

  alias Types.Union

  def init do
    %{}
  end

  def expr(integer, state) when is_integer(integer) do
    ok(Union.build(:integer), state)
  end

  @compile {:inline, ok: 2}

  defp ok(types, state) do
    {:ok, types, state}
  end
end
