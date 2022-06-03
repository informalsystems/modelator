from datetime import datetime 


class ModelResult:
    '''
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - example sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    '''

    def __init__(self, model, inprogress=list(), successful=list(), unsuccessful=list(), traces={}, progress=0):
        self._model = model
        self._time = datetime.now()
        self._inprogress = inprogress
        self._successful = successful
        self._unsuccessful = unsuccessful
        self._traces = traces
        self._progress = progress

    def model(self):
        '''
        returns the model on which the action was executed
        '''
        return self._model

    def time(self):
        '''
        Time when the action was executed
        '''
        return str(self._time)

    def inprogress(self):
        '''
        Returns the list of operators for which the action has not completed yet
        '''
        return self._inprogress

    def successful(self):
        '''
        Returns the list of operators for which the action was successful
        '''
        return self._successful

    def unsuccessful(self):
        '''
        Returns the list of operators for which the action was unsuccessful
        '''
        return self._unsuccessful

    def traces(self, operator):
        '''
        Traces associated with the result of applying an action to the operator, if available.
        Availability depends on action type, and its success for the operator.
        If available, at least one trace is guaranteed to exist.
        '''
        if operator not in self._traces:
            return None
        return self._traces[operator]

    def progress(self, operator):
        '''
        returns a progress measure between 0 and 1 (inclusive)
        for any operator on which the action is executed.
        '''
        return self._progress


class ModelMonitor:
    '''
    Monitor for actions done with the model 
    '''

    def on_parse_start(self, res: ModelResult):
        pass

    def on_parse_finish(self, res: ModelResult):
        pass

    def on_sample_start(self, res: ModelResult):
        pass

    def on_sample_update(self, res: ModelResult):
        pass

    def on_sample_finish(self, res: ModelResult):
        pass

    def on_check_start(self, res: ModelResult):
        pass

    def on_check_update(self, res: ModelResult):
        pass

    def on_check_finish(self, res: ModelResult):
        pass
