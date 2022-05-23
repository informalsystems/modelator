import json
import tabulate
from itf import ITF
import deepdiff


class ITFDiff:
    def __init__(self, filename):
        self.filename = filename

    def process(self):
        with open(self.filename) as f:
            data = json.load(f)

        states = data["states"]

        itfs = list(ITF(state) for state in states)

        for i in range(1, len(itfs)):
            diff_list = []
            ddiff = deepdiff.DeepDiff(
                itfs[i - 1].itf, itfs[i].itf, ignore_order=True, view="tree"
            )
            for vs in ddiff.values():
                for v in vs:
                    l_path = v.path(output_format="list")
                    t1 = "-" if isinstance(v.t1, deepdiff.helper.NotPresent) else v.t1
                    t2 = "-" if isinstance(v.t2, deepdiff.helper.NotPresent) else v.t2
                    diff_list.append((ITFDiff.format_path(l_path), t1, t2))
            print(
                tabulate.tabulate(
                    diff_list, headers=["path", "prev_state", "next_state"]
                )
            )
            print()

    @staticmethod
    def format_path(path):
        if len(path) == 0:
            return ""
        match path[0]:
            case "record":
                st = f".{path[1]}" + ITFDiff.format_path(path[2:])
            case "function":
                st = f"({path[1]})" + ITFDiff.format_path(path[3:])
            case "set":
                st = "{}" + ITFDiff.format_path(path[2:])
            case "sequence":
                st = f"[{path[1]}]" + ITFDiff.format_path(path[2:])
            case "object":
                st = ITFDiff.format_path(path[1:])
            case _:
                raise RuntimeError(f"{path} : no match")
        return st
