from datetime import datetime
from io import StringIO
from threading import Lock
from typing import List, Optional


class ModelResult:
    """
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - example sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    """

    def __init__(
        self,
        model,
        all_operators=None,
        parsing_error: Optional[str] = None,
        typing_error: Optional[str] = None,
    ) -> None:
        self._model = model
        self._time = datetime.now()
        self._in_progress_operators = (
            list(all_operators) if all_operators is not None else []
        )
        self._finished_operators = []
        self._successful = []
        self._unsuccessful = []
        self._traces = {}
        # unlike traces in self._traces and self._trace_paths, these are not bound to any predicate/invariant
        self._simulation_traces = set()
        self._simulation_traces_paths = set()
        self._trace_paths = {}
        self.lock = Lock()
        self.parsing_error = parsing_error
        self.typing_error = typing_error
        self.operator_errors = {}

    def model(self):
        """
        returns the model on which the action was executed
        """
        return self._model

    def time(self):
        return self._time

    def inprogress(self):
        """
        Returns the list of operators for which the action has not completed yet
        """
        return sorted(self._in_progress_operators)

    def successful(self):
        """
        Returns the list of operators for which the action was successful
        """
        return sorted(self._successful)

    def unsuccessful(self):
        """
        Returns the list of operators for which the action was unsuccessful
        """
        return sorted(self._unsuccessful)

    def traces(self, operator):
        """
        Traces associated with the result of applying an action to the operator, if available.
        Availability depends on action type, and its success for the operator.
        If available, at least one trace is guaranteed to exist.
        """
        return self._traces[operator] if operator in self._traces else None

    def all_traces(self):
        return self._traces

    def trace_paths(self, operator) -> List[str]:
        """
        The list of trace files associated with an operator as a result of running the checker.
        """
        return self._trace_paths[operator] if operator in self._trace_paths else []

    def add_trace_paths(self, operator: str, trace_paths: List[str]):
        self._trace_paths[operator] = trace_paths

    def progress(self, operator):
        """
        returns a progress measure between 0 and 1 (inclusive)
        for any operator on which the action is executed.
        """
        if operator in self._finished_operators:
            return 1
        else:
            return 0

    def _write_traces(self, s, indent, op):
        trace = self.traces(op)
        if trace:
            s.write(f"{indent}Trace: {trace}\n")

        trace_paths = self.trace_paths(op)
        if trace_paths:
            s.write(f"{indent}Trace files: {' '.join(trace_paths)}\n")

    def __str__(self):
        indent = " " * 4
        s = StringIO()

        if self.parsing_error:
            s.write("Parsing error 💥\n")
            s.write(f"{indent}{self.parsing_error}\n")
        elif self.typing_error:
            s.write("Type checking error 💥\n")
            s.write(f"{indent}{self.typing_error}\n")
        else:
            for op in self.inprogress():
                s.write(f"- {op} ⏳\n")

            for op in self.successful():
                s.write(f"- {op} OK ✅\n")

                self._write_traces(s, indent, op)

            for op in self.unsuccessful():
                s.write(f"- {op} FAILED ❌\n")

                if op in self.operator_errors and self.operator_errors[op]:
                    error = str(self.operator_errors[op]).replace("\n", f"{indent}\n")
                    s.write(f"{indent}{error}\n")

                self._write_traces(s, indent, op)

            s.write("Simulation completed✅\n")
            if len(self._simulation_traces_paths) > 0:
                s.write(
                    f"{indent}Trace files: {' '.join(self._simulation_traces_paths)}\n"
                )
            else:
                for trace_path in self._simulation_traces_paths:
                    s.write(f"{indent}Trace: {trace_path}\n")

        string = s.getvalue()
        s.close()
        return string
