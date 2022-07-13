from dataclasses import dataclass

import pytest

from modelator.pytest.decorators import itf, mbt, step


@dataclass
class State:
    x: int
    y: str


@pytest.fixture
def state() -> State:
    return State(1400, "hello")


@step()
def hellostep(state: State, x, y):
    assert state.x == x
    assert state.y == y

    print(f"At step: {state}")

    state.x -= 2
    state.y = "world"


@mbt("modelator/samples/HelloFull.tla")
def test_hellofull():
    print("end of tla test")


@itf("modelator/samples/HelloFull1.itf.json")
def test_hellofull_itf():
    print("end of itf test")
