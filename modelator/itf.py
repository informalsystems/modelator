import json
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Dict, List, Tuple

import deepdiff
import tabulate


@dataclass
class ITFRecord:
    record: Dict

    def __init__(self, data) -> None:
        self.record = {}
        for k, v in data.items():
            self.record[k] = ITF.parse(v)

    def pretty(self) -> str:
        record = ", ".join(
            map(lambda x: f"{x[0]} |-> {x[1].pretty()}", self.record.items())
        )
        result = f"[ {record} ]"
        return result

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return {k: v.to_json() for k, v in self.record.items()}


@dataclass
class ITFFunctionEntry:
    key: Any
    value: Any

    def __init__(self, key, value):
        self.key = key
        self.value = value

    def pretty(self):
        return f"{self.value}"

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return [self.key.to_json(), self.value.to_json()]


@dataclass
class ITFFunction:
    function: Dict

    def __init__(self, data: List[Tuple[Any, Any]]) -> None:
        self.function = {}
        for (k, v) in sorted(data):
            (key, value) = (ITF.parse(k), ITF.parse(v))
            self.function[key.pretty()] = ITFFunctionEntry(key, value)

    def pretty(self) -> str:
        func_str = ", ".join(
            map(
                lambda x: f"<<{x.key.pretty()}, {x.value.pretty()}>>",
                self.function.values(),
            )
        )
        result = f"SetAsFun({{{func_str}}})"
        return result

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return {"#map": [entry.to_json() for entry in self.function.values()]}


@dataclass
class ITFSet:
    set: List

    def __init__(self, data) -> None:
        self.set = []
        for v in sorted(data):
            self.set.append(ITF.parse(v))

    def pretty(self) -> str:
        set_str = ", ".join(map(lambda x: x.pretty(), self.set))
        result = f"{{{set_str}}}"
        return result

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return {"#set": [elem.to_json() for elem in self.set]}


@dataclass
class ITFSequence:
    sequence: List

    def __init__(self, data) -> None:
        self.sequence = []
        for v in data:
            self.sequence.append(ITF.parse(v))

    def pretty(self) -> str:
        seq_str = ", ".join(map(lambda x: x.pretty(), self.sequence))
        result = f"<<{seq_str}>>"
        return result

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return [elem.to_json() for elem in self.sequence]


@dataclass
class ITFObject:
    object: Any

    def __init__(self, data):
        self.object = data

    def pretty(self) -> str:
        match self.object:
            case str():
                result = f'"{self.object}"'
            case _:
                result = f"{self.object}"
        return result

    def __repr__(self):
        return self.pretty()

    def to_json(self):
        return self.object


@dataclass
class ITF:
    itf: ITFRecord | ITFFunction | ITFSequence | ITFSet | ITFObject

    def __init__(self, data):
        self.itf = ITF.parse(data)

    @staticmethod
    def parse(data) -> ITFRecord | ITFFunction | ITFSequence | ITFSet | ITFObject:
        match data:
            case dict():
                if "#map" in data:
                    return ITFFunction(data["#map"])
                if "#set" in data:
                    return ITFSet(data["#set"])
                data = {k: v for (k, v) in data.items() if not k.startswith("#")}
                return ITFRecord(data)
            case list():
                return ITFSequence(data)
            case _:
                return ITFObject(data)

    @staticmethod
    def from_itf_json(path) -> List["ITF"]:
        with open(path) as f:
            data = json.load(f)
        return [ITF(state) for state in data["states"]]

    @staticmethod
    def diff(itfs: List["ITF"]) -> List[List[Tuple[str, Any, Any]]]:
        def format_path(path):
            if len(path) == 0:
                return ""
            match path[0]:
                case "record":
                    st = f".{path[1]}" + format_path(path[2:])
                case "function":
                    st = f"({path[1]})" + format_path(path[3:])
                case "set":
                    st = "{}" + format_path(path[2:])
                case "sequence":
                    st = f"[{path[1]}]" + format_path(path[2:])
                case "object":
                    st = format_path(path[1:])
                case _:
                    raise RuntimeError(f"{path} : no match")
            return st

        trace_diff = []
        for i in range(1, len(itfs)):
            current_diff = []
            ddiff = deepdiff.DeepDiff(
                itfs[i - 1].itf, itfs[i].itf, ignore_order=True, view="tree"
            )
            for vs in ddiff.values():
                for v in vs:
                    l_path = v.path(output_format="list")
                    t1 = None if isinstance(v.t1, deepdiff.helper.NotPresent) else v.t1
                    t2 = None if isinstance(v.t2, deepdiff.helper.NotPresent) else v.t2
                    current_diff.append((format_path(l_path), t1, t2))
            trace_diff.append(sorted(current_diff))
        return trace_diff

    @staticmethod
    def flatten(
        itfs: List["ITF"], diff: bool = True
    ) -> List[Dict[str, List[Tuple[str, Any, Any]]]]:
        def format_path(path: List[str]) -> List[str]:
            if len(path) == 0:
                return []
            match path[0]:
                case "record":
                    st = [f".{path[1]}"] + format_path(path[2:])
                case "function":
                    st = [f"({path[1]})"] + format_path(path[3:])
                case "set":
                    st = ["{}"] + format_path(path[2:])
                case "sequence":
                    st = [f"[{path[1]}]"] + format_path(path[2:])
                case "object":
                    st = format_path(path[1:])
                case _:
                    raise RuntimeError(f"{path} : no match")
            return st

        trace_diff = []
        if diff:
            iterator = zip(itfs[:], itfs[1:])
        else:
            iterator = zip([ITF({}) for _ in itfs], itfs[:])

        for (old, new) in iterator:
            current_diff = defaultdict(list)
            ddiff = deepdiff.DeepDiff(old.itf, new.itf, ignore_order=True, view="tree")
            for vs in ddiff.values():
                for v in vs:
                    l_path = v.path(output_format="list")
                    t1 = None if isinstance(v.t1, deepdiff.helper.NotPresent) else v.t1
                    if not diff:
                        assert t1 is None
                    t2 = None if isinstance(v.t2, deepdiff.helper.NotPresent) else v.t2
                    formatted_path = format_path(l_path)
                    if diff:
                        root_key = formatted_path[0]
                    else:
                        root_key = None
                    current_diff[root_key].append(("".join(formatted_path), t1, t2))
            trace_diff.append(current_diff)
        return trace_diff

    @staticmethod
    def markdown(itfs: List["ITF"], diff: bool = True) -> str:
        def md_sanitize(x: str) -> str:
            return x.replace("|", "\\|")

        st = "# ITF"
        if diff:
            st += "-Diff"
        st += " Markdown\n\n"

        for (i, e_step_dict) in enumerate(ITF.flatten(itfs, diff)):
            if diff:
                st += f"## Step {i+1} to Step {i+2}\n\n"
            else:
                st += f"## Step {i+1}\n\n"
            st += "<details open>\n\n"
            st += "<summary>Variables</summary>\n\n"
            for (root_key, li) in e_step_dict.items():
                if diff:
                    st += "<details open>\n\n"
                    st += f"<summary><code>{root_key.removeprefix('.')}</code></summary>\n\n"
                    st += "\n|KeyPath|Old|New|\n"
                    st += "|-|-|-|\n"
                    for (k, u, v) in li:
                        st += f"|`{md_sanitize(k.removeprefix('.'))}`"
                        st += f"|`{md_sanitize(str(u))}`"
                        st += f"|`{md_sanitize(str(v))}`"
                        st += "|\n"
                    st += "\n</details>\n"
                else:
                    st += "\n|KeyPath|Value|\n"
                    st += "|-|-|\n"
                    for (k, _, v) in li:
                        st += f"|`{md_sanitize(k.removeprefix('.'))}`"
                        st += f"|`{md_sanitize(str(v))}`"
                        st += "|\n"
                    st += "\n"
            st += "\n"
            st += "</details>\n\n"
        return st

    @staticmethod
    def print_diff(itfs: List["ITF"], **kargs):
        for each_step in ITF.diff(itfs):
            print(
                tabulate.tabulate(
                    each_step, headers=["path", "prev_state", "next_state"], **kargs
                )
            )
            print()

    def __repr__(self):
        return " /\\ ".join((f"({k} = {v})" for (k, v) in self.itf.record.items()))

    def to_json(self):
        return self.itf.to_json()
