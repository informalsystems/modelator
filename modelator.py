# Modelator API

class Model:
    '''
    Model is the main interface class for working with models
    A valid model must have both init and next predicates defined.
    '''

    @classmethod
    def parse_file(cls, file, init = 'Init', next = 'Next'):
        '''
        Attempts to parse the given file, and returns the parsed model on success.
        Raises an exception on error.

        m = Model.parse_file('HourClock.tla')
        '''
        pass


    def instantiate(self, constants):
        '''
        Instantiates model constants, if any. The parameter should be a dict.

        m.instantiate({ 'N_PROC': 2, 'USERS': { 'alice', 'bob' } })
        '''
        pass

    def sample(self, examples = None, constants = None):
        '''
        Sample `examples` from the model; 
            `examples` can be either a name of a single operator, or a list of operator names.
            When omitted, all operators with names prefixed/suffixed with `Ex` or `Example` will be collected.
        All model constants should be instantiated, either by 
            a previous `instantiate()` call, or via the `constants` argument.
            Any constant given via `constants` overrides the same constant provided via `instantiate()`.
        Returns ModelResult summarizing the sampling; it can be also accessed via `last_sample()`.

        result = m.sample(['ExThreeHours', 'ExFullRun'])
        for op in result.successful():
            print(f"Example for {op}: {result.traces(op)[0]}")
        for op in result.unsuccessful():
            print(f"Sampling for {op} failed")
        '''
        pass

    def last_sample(self):
        '''
        returns the result of the last application of `sample()`
        (chronological order)
        '''
        pass

    def all_samples(self):
        '''
        returns the list of results from all applications of `sample()`
        '''
        pass

    def check(self, invariants = None, constants = None):
        '''
        Check `invariants` from the model; 
            `invariants` can be either a name of a single operator, or a list of operator names.
            When omitted, all operators with names prefixed/suffixed with `Inv` or `Invariant` will be collected.
        All model constants should be instantiated, either by 
            a previous `instantiate()` call, or via the `constants` argument.
            Any constant given via `constants` overrides the same constant provided via `instantiate()`.
        Returns ModelResult summarizing the checking; it can be also accessed via `last_check()`.

        result = m.check(['InvNoOverflow', 'InvNoUnderflow'])
        for op in result.successful():
            print(f"Invariant checking for {op} succeeded")
        for op in result.unsuccessful():
            print(f"Invariant {op} violated; counterexample: {result.traces(op)[0]}")
        '''
        pass

    def last_check(self):
        '''
        returns the result of the last application of `check()`
        '''
        pass

    def all_checks(self):
        '''
        returns the list of results from all applications of `check()`
        (chronological order)
        '''
        pass


class ModelResult:
    '''
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - operator sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    '''
    def model(self) -> Model:
        '''
        Model on which the actions were executed
        '''
        pass

    def time(self):
        '''
        Time when the actions were executed
        '''
        pass

    def successful(self):
        '''
        Returns the list of operators for which the action was successful
        '''
        pass

    def unsuccessful(self):
        '''
        Returns the list of operators for which the action was unsuccessful
        '''
        pass

    def traces(self, operator):
        '''
        Traces associated with the result of applying an action to the operator, if available.
        Availability depends on action type, and its success for the operator.
        If available, at least one trace is guaranteed to exist.
        '''
        pass


class Trace:
    '''
    Trace is a sequence of model steps. 
    '''


m = Model.parse_file('HourClock.tla')
m.instantiate({
    'N_PROC': 2,
    'USERS': { 'alice', 'bob' }
})

result = m.sample(['ExThreeHours', 'ExFullRun'])
for op in result.successful():
    print(f"Example for {op}: {result.traces(op)[0]}")
for op in result.unsuccessful():
    print(f"Sampling for {op} failed")

result = m.check(['InvNoOverflow', 'InvNoUnderflow'], constants = { 'USERS': { 'alice', 'bob', 'carol' } })
for op in result.successful():
    print(f"Invariant checking for {op} succeeded")
for op in result.unsuccessful():
    print(f"Invariant {op} violated; counterexample: {result.traces(op)[0]}")


class ModelShell(Model):
    '''
    Model class from modelator.shell namespace.
    Implements all functions from Model, but with the following differences:
      - each call is non-blocking, and returns immediately.
      - callbacks can be registered for any action
      - on (partial) completion of any action, corresponding callbacks will be triggered.

    Additionally, `auto` methods are provided, which are auto-triggered on model updates.
    '''

    @classmethod
    def auto_parse_file(cls, file, init = 'Init', next = 'Next'):
        '''
        Same as `parse_file`, but it attempts to parse the file whenever it changes on the disk.
        If the parsing is successful, further `auto` actions will be triggered.

        m = Model.auto_parse_file('HourClock.tla')
        '''
        pass

    def auto_sample(self, examples = None, constants = None):
        '''
        Same as `sample`, but executed automatically on every model update.
        '''

    def auto_check(self, invariants = None, constants = None):
        '''
        Same as `check`, but executed automatically on every model update.
        '''


class ModelExperimental(Model):
    '''
    Optional, experimental methods that might be added later
    '''

    def modules(self):
        '''
        returns a dictionary from module names to their content 
        '''
        pass

    def main_module(self):
        '''
        returns the name of the main module
        '''
        pass