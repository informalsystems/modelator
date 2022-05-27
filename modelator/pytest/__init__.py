from dataclasses import dataclass
from typing import List

import pytest


@dataclass
class Testnet:
    nodes: List[str]
    accounts: List[str]
    validators: List[str]


@pytest.fixture
def testnet():
    return Testnet(["node1"], ["account1"], ["validator1"])
