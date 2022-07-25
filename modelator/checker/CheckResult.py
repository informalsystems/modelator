from typing import List, Optional
from tomlkit import boolean


class CheckResult:

    def __init__(self, is_ok: boolean, error_msg: Optional[str] = None, traces: List[str] = []) -> None:
        self.is_ok = is_ok
        self.error_msg = error_msg
        self.traces = traces

    def __repr__(self) -> str:
        if self.is_ok:
            return f"CheckResult(success, {self.traces})"
        else:
            return f"CheckResult(failed, {self.error_msg}, {self.traces})"