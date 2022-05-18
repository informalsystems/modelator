import os
from typing import List
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.check import check_apalache, check_tlc
from modelator.utils import shell_helpers, tla_helpers
from modelator import constants

apalache = constants.APALACHE
tlc = constants.TLC


class Modelator:
    def __init__(self, model_file_name=None, autoload=True) -> None:

        self.model_file_name = model_file_name
        self.autoload = autoload
        if self.autoload is True and self.model_file_name is not None:
            self.model = self.load_model(self.model_file_name, print_info=False)

        # self.config_args = shell_helpers.ConfigValues()
        self.config_args = {}

        self.init_state = None
        self.next = None
        self.invariant = None

    def __repr__(self) -> str:
        if self.model_file_name is not None:
            return "Modelator instance for the model {}".format(self.model_file_name)
        else:
            return (
                "Modelator instance without a model (use 'load' to load a model file)"
            )

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
            self.load_model(self.model_file_name, print_info=False)

    def _set_default_basic_args(self):
        if self.init_state is None:
            self.init_state = "Init"
        if self.next is None:
            self.next = "Next"
        if self.invariant is None:
            self.invariant = "Inv"

    def _set_apalache_args(self):
        apalache_args = {}
        if constants.INIT not in self.config_args:
            apalache_args[constants.INIT] = self.init_state
        if constants.NEXT not in self.config_args:
            apalache_args[constants.NEXT] = self.next
        if constants.INVARIANT not in self.config_args:
            apalache_args[constants.INVARIANT] = self.invariant
        if constants.APALACHE_NUM_STEPS not in self.config_args:
            apalache_args[constants.APALACHE_NUM_STEPS] = 10
        return apalache_args

    def _set_tlc_args(self):
        tlc_args = {}
        basic_info = {}
        args_config_file_name = "config_args_file.cfg"

        if constants.INIT not in self.config_args:
            basic_info[constants.INIT] = self.init_state
        if constants.NEXT not in self.config_args:
            basic_info[constants.NEXT] = self.next
        if constants.INVARIANT not in self.config_args:
            basic_info[constants.INVARIANT] = self.invariant

        tlc_args["config"] = args_config_file_name
        args_config_file = self._default_args_to_config_string()
        self.files[args_config_file_name] = args_config_file

        return tlc_args, basic_info

    def _default_args_to_config_string(self):
        return "INIT {}\nNEXT {}\n INVARIANT {}".format(
            self.init_state, self.next, self.invariant
        )

    def load_model(self, file_to_load: str, print_info: bool = True):

        self.model_file_name = file_to_load
        self.model = open(file_to_load).read()
        self.directory = os.path.dirname(os.path.abspath(self.model_file_name))

        self.files = tla_helpers.get_auxiliary_tla_files(self.model_file_name)

        if print_info is True:
            print(
                "Loaded file {}.\n Its content is:\n{}".format(
                    self.model_file_name, self.model
                )
            )

    def parse(self):
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
        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()
        res, msg = typecheck(os.path.basename(self.model_file_name), self.files)
        if res is True:
            print("File {} typechecks.".format(self.model_file_name))
        else:
            msg.file_path = os.path.abspath(self.model_file_name)
            print(msg)

    def check(self, checker: str = constants.APALACHE, config_file_name: str = None):
        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()
        self._set_default_basic_args()

        if checker == constants.TLC:
            args, basic_info = self._set_tlc_args()
            res, msg, cex = check_tlc(
                tla_file_name=os.path.basename(self.model_file_name),
                files=self.files,
                args=args,
            )
        else:

            args = self._set_apalache_args()
            basic_info = args
            res, msg, cex = check_apalache(
                os.path.basename(self.model_file_name),
                self.files,
                args=args,
            )

        if res is True:
            print(
                "Invariant {} is never violated".format(basic_info[constants.INVARIANT])
            )
        else:
            msg.file_path = self.model_file_name
            if msg.error_category == constants.CHECK:
                msg.problem_description = (
                    "Invariant {} violated.\nCounterexample is {}".format(
                        basic_info[constants.INVARIANT], str(cex)
                    )
                )
            print(msg)


def clear():
    os.system("cls" if os.name == "nt" else "clear")


def start():
    m = Modelator()
    m.load_model("modelator/samples/Hello.tla")
    return m
