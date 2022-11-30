import pytest
from hanoi import HanoiTower
from munch import Munch

from modelator.pytest.decorators import itf, step

N_DISC = 3


# pytest.fixture allows a variable to be persistent through out the test.
# we want the SUT state to persist during the test.
# ref: https://docs.pytest.org/en/6.2.x/fixture.html
@pytest.fixture
def sut():
    return Munch()


# you have to create hooks for each actions/steps from TLA+ trace steep.
# this is done by annotating with `@step(TAG)`.
@step("init")
def init(sut, action):
    print(f"N_DISC: {N_DISC}")
    sut.hanoi = HanoiTower(N_DISC)


# note how `action`` variable is automatically available from ITF trace.
@step("move")
def move(sut, action):
    print(f"MOVE: {sut.hanoi.state} | {action.source} -> {action.target}")
    sut.hanoi.move(action.source, action.target)
    assert sut.hanoi.is_valid()


# `@itf(ITF_TRACE_FILE)` annotates a pytest method to use drive the test using that itf trace.
# `keypath` params denotes a consistent path to a string variable in each ITF trace state
# it is used to match against tags for each step.
@itf("traces/Test/violation1.itf.json", keypath="action.tag")
def test_hanoi(sut):
    assert sut.hanoi.is_solved()
    print(f"FINAL: {sut.hanoi.state}")
