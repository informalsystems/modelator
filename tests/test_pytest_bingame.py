import pytest

from modelator.pytest.decorators import mbt, step


@pytest.fixture
def state():
    return {}


@step("Zero")
def zero(state, number):
    state["number"] = 0
    assert state["number"] == number


@step("AddOne")
def add_one(state, number):
    state["number"] += 1
    assert state["number"] == number


@step("MultiplyTwo")
def multiply_two(state, number):
    state["number"] *= 2
    assert state["number"] == number


@mbt("tests/models/bingame.tla", keypath="action")
def test_collatz(state):
    assert state["number"] == 30
