# Modelator API
# (WIP) API documentation, not a real interface


class Model:
    """
    Model is the main interface class for working with models
    A valid model must have both init and next predicates defined.
    """

    @classmethod
    def parse_file(cls, file, init="Init", next="Next"):
        """
        Attempts to parse the given file, and returns the parsed model on success.
        Raises an exception on error.

        m = Model.parse_file('HourClock.tla')
        """
        pass

    def typecheck(self):
        """ """
        pass

    def instantiate(self, constants):
        """
        Instantiates model constants, if any. The parameter should be a dict.

        m.instantiate({ 'N_PROC': 2, 'USERS': { 'alice', 'bob' } })
        """
        pass

    def sample(self, examples=None, constants=None):
        """
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
        """
        pass

    def last_sample(self):
        """
        returns the result of the last application of `sample()`
        (chronological order)
        """
        pass

    def all_samples(self):
        """
        returns the list of results from all applications of `sample()`
        """
        pass

    def check(
        self, invariants=None, constants=None, checker="apalache", checker_params=None
    ):
        """
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
        """
        pass

    def last_check(self):
        """
        returns the result of the last application of `check()`
        """
        pass

    def all_checks(self):
        """
        returns the list of results from all applications of `check()`
        (chronological order)
        """
        pass

    def add_monitor(self, monitor):
        """
        Add a monitor to track actions on this model
        """
        pass

    def remove_monitor(self, monitor):
        """
        Removes a previously added monitor
        """
        pass

    def start_html_monitor(self, filename):
        """
        Start monitoring model actions in HTML file.
        """

    def stop_html_monitor(self, filename):
        """
        Stop monitoring model actions in HTML file.
        """

    def start_markdown_monitor(self, filename):
        """
        Start monitoring model actions in Markdown file.
        """

    def stop_markdown_monitor(self, filename):
        """
        Stop monitoring model actions in Markdown file.
        """


class ModelResult:
    """
    A result of running some action on a set of model operators
    Different actions can have different outcomes:
     - example sampling is successful when a trace satisfying it can be produced.
     - invariant checking is successful when a trace violating it can't be produced.
    """

    def model(self):
        """
        returns the model on which the action was executed
        """
        pass

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


class Trace:
    """
    Trace is a sequence of model states, each state assigning values to state variables.
    """

    def as_tla(self):
        """
        Returns a list with trace states.
        Each state is represented by a dict from variable name to a its value in TLA+ format.
        """

    def as_tla_diff(self):
        """
        Returns a list, where each element is a diff between trace states.
        Thus, it is always 1 element less than the number of states in the trace.
        Each diff element is a dict from a changed state component
        to the tuple with the old and the new value of this component.
        """
        pass


from modelator import *

m = Model.parse_file("HourClock.tla")
m.instantiate({"N_PROC": 2, "USERS": {"alice", "bob"}})

result = m.sample(["ExThreeHours", "ExFullRun"])
for op in result.successful():
    print(f"Example for {op}: {result.traces(op)[0].as_tla()}")
for op in result.unsuccessful():
    print(f"Sampling for {op} failed")

result = m.check(
    ["InvNoOverflow", "InvNoUnderflow"], constants={"USERS": {"alice", "bob", "carol"}}
)
for op in result.successful():
    print(f"Invariant checking for {op} succeeded")
for op in result.unsuccessful():
    print(f"Invariant {op} violated; counterexample: {result.traces(op)[0]}")


class ModelMonitor:
    """
    Monitor for actions done with the model
    """

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


class HtmlModelMonitor(ModelMonitor):
    """
    A model monitor that stores all model action updates to HTML file
    """

    def __init__(self, filename):
        super().__init__()


class MarkdownModelMonitor(ModelMonitor):
    """
    A model monitor that stores all model action updates to Markdown file
    """

    def __init__(self, filename):
        super().__init__()


class ModelShell(Model):
    """
    Model class from modelator.shell namespace.
    Implements all functions from Model, but with the following differences:
      - each call is non-blocking, and returns immediately.
      - callbacks can be registered for any action
      - on (partial) completion of any action, corresponding callbacks will be triggered.

    Additionally, `auto` methods are provided, which are auto-triggered on model updates.
    """

    def auto_sample(self, examples=None, constants=None):
        """
        Same as `sample`, but executed automatically on every model update.
        """

    def auto_check(self, invariants=None, constants=None):
        """
        Same as `check`, but executed automatically on every model update.
        """


# top-level functions from modelator.shell


def auto_parse_file(file, init="Init", next="Next"):
    """
    Same as `parse_file`, but it attempts to parse the file whenever it changes on the disk.
    If the parsing is successful, further `auto` actions will be triggered.
    """
    pass


def auto_evaluate_file(
    file, init="Init", next="Next", examples=None, invariants=None, constants=None
):
    """
    Combines in one call `auto_parse_file`, `auto_sample`, `auto_check`.
    """
    pass


def stop_auto_file(file):
    """
    Stop monitoring started previously by `auto_parse_file` or  `auto_evaluate_file`.
    """
    pass


def start_shell_monitor():
    """
    Takes control of the terminal, and overlays the status information
    on any model actions in it.
    """
    pass


def stop_shell_monitor():
    """
    Releases control of the terminal, and removes all status overlays.
    """
    pass


def start_html_monitor(filename):
    """
    Starts monitoring status of all model actions in HTML file
    """
    pass


def stop_html_monitor(filename):
    """
    Stops monitoring status of model actions in HTML file
    """
    pass


def start_markdown_monitor(filename):
    """
    Starts monitoring status of all model actions in Markdown file
    """
    pass


def stop_markdown_monitor(filename):
    """
    Stops monitoring status of model actions in Markdown file
    """
    pass


from modelator.shell import *

start_modelator_shell()
start_html_monitor("status.html")
auto_evaluate_file("HourClock.tla")


class ModelExperimental(Model):
    """
    Optional, experimental methods that might be added later
    """

    def modules(self):
        """
        returns a dictionary from module names to their content
        """
        pass

    def main_module(self):
        """
        returns the name of the main module
        """
        pass
