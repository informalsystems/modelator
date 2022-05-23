from dataclasses import dataclass
from typing import Any, Dict, List, Tuple


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
                lambda x: f"<<{x['key'].pretty()}, {x['value'].pretty()}>>",
                self.function.values(),
            )
        )
        result = f"SetAsFun({{{func_str}}})"
        return result

    def __repr__(self):
        return self.pretty()


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

    def __repr__(self):
        return " /\\ ".join((f"({k} = {v})" for (k, v) in self.itf.record.items()))
