from dataclasses import dataclass
from typing import Optional

import pytest

from modelator.pytest.decorators import mbt, step


@dataclass
class Number:
    val: Optional[int]


@pytest.fixture
def state() -> Number:
    return Number(None)


@step()
def collatz(state: Number, x):
    if state.val is None:
        state.val = x
    else:
        n = state.val
        if n % 2 == 0:
            next_val = n // 2
        else:
            next_val = 1 + n * 3
        assert next_val == x
        state.val = next_val


@mbt("tests/models/collatz.tla")
def test_collatz():
    print("pass test")
