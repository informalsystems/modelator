from .. import const_values
from modelator.utils.model_exceptions import ModelError


def shell(func):
    def inner_func(*args, **kwargs):
        if const_values.SHELL_ACTIVE is True:

            try:
                ret = func(*args, **kwargs)
                return ret
            except ModelError as e:
                print(e)

        else:
            return func(*args, **kwargs)

    return inner_func
