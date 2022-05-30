# Modelator API

from xmlrpc.client import Boolean

class Model:
    '''
    Model is the main interface class for working with models
    A valid model has to have both initial and next predicates defined.
    '''

    @classmethod
    def parse_file(cls, file, init = 'Init', next = 'Next'):
        '''
        Attempts to parse the given file, and returns the parsed model on success.
        Raises an exception on error.
        '''
        return Model()

    @classmethod
    def parse_source(cls, source, init = 'Init', next = 'Next'):
        '''
        Attempts to parse the given model source, and returns the parsed model on success.
        Raises an exception on error.
        '''
        return Model()

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

    def instantiate(self, constants):
        '''
        Instantiates model constants, if any. The parameter should be a dict.
        '''
        pass


    
    def sample(self, operator, constants = None) -> Boolean:
        '''
        Sample a TLA+ operator (should be present in the model)
        All model constants should be instantiated, either by 
        a previous `instantiate()` call, or via supplied argument.
        Returns True, if sampling was successful; an example can be collected via `examples()`.
        '''

    def samples(self):
        pass
    

class Trace:
    '''
    Trace is a sequence of model steps. 
    '''

class ModelSample:
    def model(self) -> Model:
        '''
        model on which the sample was taken
        '''
        pass

    def time(self):
        '''
        time when the sample was taken
        '''
        pass

    def success(self) -> Boolean:
        '''
        Whether the sample was successful
        (interpretation depends on sample type)
        '''
        pass

    def traces(self):
        '''
        Traces associated with this sample, if available
        (availability depends on sample type and success)
        '''
        pass



m = Model.parse_file('HourClock.tla')
m.instantiate({
    'N_PROC': 2,
    'USERS': { 'alice', 'bob' }
})
if m.sample('ExThreeHours'):
    print(m.last_sample().traces()[0])
else:
    print("Could not sample an example")

if m.check('InvNoOverflow'):
    print('Invariant holds')
else:
    print(f"Invariant violated. Counterexample: {m.last_check().traces()[0]}")
