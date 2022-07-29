from typing import List, Optional
from tomlkit import boolean


class CheckResult:
    def __init__(
        self,
        is_ok: boolean,
        error_msg: Optional[str] = None,
        traces: List[str] = [],
        trace_paths: List[str] = [],
    ) -> None:
        self.is_ok = is_ok
        self.error_msg = error_msg
        self.traces = traces
        self.trace_paths = trace_paths

    def __repr__(self) -> str:
        if self.is_ok:
            return f"CheckResult(success, {self.traces}, {self.trace_paths})"
        else:
            return f"CheckResult(failed, {self.error_msg}, {self.traces}, {self.trace_paths})"
