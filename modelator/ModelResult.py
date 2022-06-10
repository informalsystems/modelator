from datetime import datetime
from threading import Lock


class ModelResult:
    """
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - example sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    """

    def __init__(
        self, model, all_operators=None, parsing_error=False, typing_error=False
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
        self.lock = Lock()
        self.parsing_error = parsing_error
        self.typing_error = typing_error

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
        return self._in_progress_operators

    def successful(self):
        """
        Returns the list of operators for which the action was successful
        """
        return self._successful

    def unsuccessful(self):
        """
        Returns the list of operators for which the action was unsuccessful
        """
        return self._unsuccessful

    def traces(self, operator):
        """
        Traces associated with the result of applying an action to the operator, if available.
        Availability depends on action type, and its success for the operator.
        If available, at least one trace is guaranteed to exist.
        """
        return self._traces[operator] if operator in self._traces else None

    def all_traces(self):
        return self._traces

    def progress(self, operator):
        """
        returns a progress measure between 0 and 1 (inclusive)
        for any operator on which the action is executed.
        """
        if operator in self._finished_operators:
            return 1
        else:
            return 0
