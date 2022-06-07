from .. import CONSTANTS
from modelator.utils.model_exceptions import ModelError


def shell(func):
    def inner_func(*args, **kwargs):
        if CONSTANTS.SHELL_ACTIVE is True:

            try:
                ret = func(*args, **kwargs)
                return ret
            except ModelError as e:
                print(e)

        else:
            return func(*args, **kwargs)

    return inner_func
