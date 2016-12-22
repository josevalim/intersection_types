defmodule TypesTest do
  use ExUnit.Case, async: true

  defmacro quoted_of(expr) do
    quote do
      Types.of(unquote(Macro.escape(expr)))
    end
  end

  test "booleans" do
    assert {:ok, :boolean} = quoted_of(true)
    assert {:ok, :boolean} = quoted_of(false)
  end

  test "ifs" do
    assert {:ok, :boolean} =
           quoted_of(if true, do: true, else: false)

    assert {:error, {:if_conditional, :integer}, _} =
           quoted_of(if 0, do: true, else: false)

    assert {:error, {:if_branches, :boolean, :integer}, _} =
           quoted_of(if true, do: true, else: 0)
  end

  test "functions" do
    assert {:ok, {:fn, {[:boolean], :boolean}}} =
           quoted_of(fn bool :: :boolean -> bool end)
  end

  test "function calls" do
    assert {:ok, :boolean} =
           quoted_of((fn bool :: :boolean -> bool end).(true))

    assert {:error, {:fn_app, _}, _} =
           quoted_of(fn bool :: :boolean -> bool.(true) end)

    assert {:error, {:fn_arg, _, _}, _} =
           quoted_of((fn bool :: :boolean -> bool end).(fn bool :: :boolean -> bool end))
  end
end
