import json
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
    def diff(itfs: List["ITF"]):
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
