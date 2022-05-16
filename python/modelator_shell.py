import os
from typing import List
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.check import check_apalache
from modelator.utils import shell_helpers, tla_helpers
from modelator import constants


class Modelator:
    def __init__(self, model_file_name=None, autoload=True) -> None:

        self.model_file_name = model_file_name
        self.autoload = autoload
        if self.autoload is True and self.model_file_name is not None:
            self.model = self.load_model(self.model_file_name, print_info=False)

        self.config_args = shell_helpers.ConfigValues()
        self.config_args[constants.INIT] = "Init"
        self.config_args[constants.NEXT] = "Next"
        self.config_args[constants.INVARIANT] = "Inv"
        self.config_args[constants.APALACHE_NUM_STEPS] = 5
        # self.config_file_name = None
        # self.config = None

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

    def check(self):
        if self._check_if_model_exists() is False:
            return

        self._load_if_needed()
        res, msg, cex = check_apalache(
            os.path.basename(self.model_file_name),
            self.files,
            apalache_args=self.config_args,
        )

        if res is True:
            print(
                "Invariant {} is never violated (after {} steps)".format(
                    self.config_args[constants.INVARIANT],
                    self.config_args[constants.APALACHE_NUM_STEPS],
                )
            )
        else:
            msg.file_path = self.model_file_name
            if msg.error_category == constants.CHECK:
                msg.problem_description = (
                    "Invariant {} violated.\nCounterexample is {}".format(
                        self.config_args[constants.INVARIANT], str(cex)
                    )
                )
            print(msg)


def exp():
    print("check this type: samples/HelloFlawed.tla")
    print("check this type: modelator/samples/HelloFlawed.tla")
    print("check this type: python/modelator/samples/HelloFlawed.tla")
    print(
        "check this type: /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla"
    )


def clear():
    os.system("cls" if os.name == "nt" else "clear")


def start():
    m = Modelator()
    m.load_model("modelator/samples/Hello.tla")
    return m
