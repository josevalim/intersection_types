defmodule TypesTest do
  use ExUnit.Case
  doctest Types

  test "greets the world" do
    assert Types.hello() == :world
  end
end
