class ModelResult:
    """
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - example sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    """

    def __init__(self, model) -> None:
        self.model = model

    def model(self):
        """
        returns the model on which the action was executed
        """
        return self.model

    def time(self):
        """
        Time when the action was executed
        """
        pass

    def inprogress(self):
        """
        Returns the list of operators for which the action has not completed yet
        """
        pass

    def successful(self):
        """
        Returns the list of operators for which the action was successful
        """
        pass

    def unsuccessful(self):
        """
        Returns the list of operators for which the action was unsuccessful
        """
        pass

    def traces(self, operator):
        """
        Traces associated with the result of applying an action to the operator, if available.
        Availability depends on action type, and its success for the operator.
        If available, at least one trace is guaranteed to exist.
        """
        pass

    def progress(self, operator):
        """
        returns a progress measure between 0 and 1 (inclusive)
        for any operator on which the action is executed.
        """
        pass
