from dataclasses import dataclass

import pytest

from modelator.pytest.decorators import mbt, step


@dataclass
class Number:
    val: int


@pytest.fixture
def state() -> Number:
    return Number(20)


@step()
def collatz(state: Number, x):
    n = state.val
    if n % 2 == 0:
        next_val = n // 2
    else:
        next_val = 1 + n * 3
    assert next_val == x
    state.val = next_val


@mbt("tests/models/collatz.tla", keypath="action")
def test_collatz():
    print("pass test")
