from typing import List, Optional, Tuple


class HanoiTower:
    state: Tuple[List[int], List[int], List[int]]

    def __init__(self, n_disc: Optional[int] = None):
        self.n_disc = n_disc or 3
        self.state = (list(range(self.n_disc, 0, -1)), [], [])

    def move(self, source: int, target: int):
        if len(self.state[source - 1]) == 0:
            raise RuntimeError("Source tower is empty")

        if (
            len(self.state[target - 1]) > 0
            and self.state[target - 1][-1] < self.state[source - 1][-1]
        ):
            raise RuntimeError("target has smaller disc than source")

        self.state[target - 1].append(self.state[source - 1].pop())

    def is_valid(self) -> bool:
        return all(sorted(e, reverse=True) == e for e in self.state)

    def is_solved(self) -> bool:
        return self.state == ([], [], list(range(self.n_disc, 0, -1)))
