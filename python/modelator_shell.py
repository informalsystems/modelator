from inspect import trace
import os
from typing import List
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.check import check_apalache, check_tlc
from modelator.utils import shell_helpers, tla_helpers
from modelator import constants
import traceback

apalache = constants.APALACHE
tlc = constants.TLC


class ModelatorShell:
    def __init__(self, model_file_name: str = None, autoload: bool = True) -> None:
        """
        Constructs the modelator shell object.

        Parameters
        ----------
            model_file_name : str
                path to the main .tla file under inspection in the shell (absolute path, or relative to
                `modelator_shell` file)
            autoload : bool
                if True, the shell will re-load the file each time an action is called.
        """

        self.model_file_name = model_file_name
        self.autoload = autoload
        self._latest_exception = ""
        if self.autoload is True and self.model_file_name is not None:
            self.model = self.load(self.model_file_name)

        # self.init_state = None
        # self.next = None
        # self.property = None

    def __str__(self) -> str:
        if self.model_file_name is not None:
            return "Modelator instance for the model {}".format(self.model_file_name)
        else:
            return (
                "Modelator instance without a model (use 'load' to load a model file)"
            )

    def __repr__(self) -> str:
        return "{}({!r})".format(self.__class__.__name__, self.__dict__)

    def load(self, file_to_load: str):
        """
        Loads the file `file_to_load` and saves it under `self.model`.
        It also loads all other relevant files
        (as provided by the function `tla_helpers.get_auxiliary_tla_files`) and stores them to
        `self.files`.

        Parameters
        ----------
        file_to_load : str
                path to the main .tla file under inspection in the shell (absolute path, or relative to
                `modelator_shell` file)

        """

        self.model_file_name = file_to_load
        self.model = open(file_to_load).read()
        self.files = tla_helpers.get_auxiliary_tla_files(self.model_file_name)

    def parse(self):
        """
        Parses the model (from the file `self.model_file_name`).
        It prints the error message if the file does not parse.
        """

        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()

        res, msg = parse(os.path.basename(self.model_file_name), self.files)
        if res is True:
            print("File {} successfully parsed.".format(self.model_file_name))
        else:
            msg.file_path = os.path.abspath(self.model_file_name)
            print(msg)

    def typecheck(self):
        """
        Typechecks the model (from the file `self.model_file_name`).
        Typechecking is only relevant for working with Apalache (not TLC).
        It prints the error message if the file does not parse.
        """

        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()
        res, msg = typecheck(os.path.basename(self.model_file_name), self.files)
        if res is True:
            print("File {} typechecks.".format(self.model_file_name))
        else:
            msg.file_path = os.path.abspath(self.model_file_name)
            print(msg)

    def check(
        self,
        checker: str = constants.APALACHE,
        config_file_name: str = None,
        invariants: List[str] = constants.DEFAULT_INVARIANTS,
        init_state_predicate: str = constants.DEFAULT_INIT,
        next_state_predicate: str = constants.DEFAULT_NEXT,
    ):
        """
        Checks whether the model is correct (with respect to specified invariants).

        Parameteres:
        -----------
        checker : str
            can be either 'apalache' or 'tlc' and determines which checker to use. Defaults to 'apalache'
        config_file_name : str
            A configuration file. If specified, this is where relevant information about initial state, next predicate
            and invariants is taken from
        invariants : List[str]
            A list of invariants to check. Defaults to ['Inv']. Only relevant if `config_file_name` is None.
        init_state_predicate : str
            The name of the predicate (from the model) which defines the initial state. Defaults to 'Init'. Only relevant if `config_file_name` is None.
        next_state_predicate : str
            The name of the predicate (from the model) which defines state transitions. Defaults to 'Next'. Only relevant if `config_file_name` is None.

        """

        # check that the model on which shell is working is set
        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()

        if config_file_name is not None:
            assert config_file_name in self.files
            args = {constants.CONFIG: config_file_name}

        else:
            args_config_file = self._basic_args_to_config_string(
                init=init_state_predicate,
                next=next_state_predicate,
                invariants=invariants,
            )
            args_config_file_name = "generated_config.cfg"
            args = {constants.CONFIG: args_config_file_name}
            self.files[args_config_file_name] = args_config_file

        if checker == constants.TLC:
            args.update(self._set_additional_tlc_args())
            try:
                res, msg, cex = check_tlc(
                    tla_file_name=os.path.basename(self.model_file_name),
                    files=self.files,
                    args=args,
                )
            except Exception as e:
                print("Problem running TLC: {}".format(e))
                self._latest_exception = traceback.format_exc()
                return

        else:  # if checker is Apalache

            args.update(self._set_additional_apalache_args())
            basic_info = args
            try:
                res, msg, cex = check_apalache(
                    os.path.basename(self.model_file_name),
                    self.files,
                    args=args,
                )
            except Exception as e:
                print("Problem runing Apalache: {}".format(e))
                self._latest_exception = traceback.format_exc()
                return

        if res is True:
            print("Invariants {} hold".format(invariants))
        else:
            msg.file_path = self.model_file_name
            print(msg)

    def stacktrace(self):
        print(self._latest_exception)

    def _check_if_model_exists(self):
        if self.model_file_name is None or (
            self.autoload is False and self.model is None
        ):
            print("ERROR: Model is not set yet. Use command `load(<model_file>.tla)`")
            return False
        else:
            return True

    def _load_if_needed(self):

        if self.autoload is True:
            self.load(self.model_file_name)

    def _set_additional_apalache_args(self):
        apalache_args = {}
        apalache_args[constants.APALACHE_NUM_STEPS] = 10
        return apalache_args

    def _set_additional_tlc_args(self):
        tlc_args = {}
        return tlc_args

    def _basic_args_to_config_string(self, init: str, next: str, invariants: str):
        return "INIT {}\nNEXT {}\nINVARIANTS\n{}".format(
            init, next, "  \n".join(invariants)
        )


def clear():
    os.system("cls" if os.name == "nt" else "clear")


def start():
    m = ModelatorShell()
    m.load("modelator/samples/Hello.tla")
    return m
