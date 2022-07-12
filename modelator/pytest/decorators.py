"""
The following implemented pattern is influenced by [`pytest-bdd`](https://github.com/pytest-dev/pytest-bdd/blob/master/pytest_bdd/steps.py).

But it is not the only one using this pattern.
As an another example, [`hypothesis`](https://hypothesis.readthedocs.io/en/latest/quickstart.html) is also using the same patterns.
"""

import json
from inspect import signature
from typing import Callable

import pytest
from pytest import FixtureRequest

from modelator.Model import Model


def dict_get_keypath(data, property_path=None):
    """Return the value at nested keys at a dictionary

    Example:
        data = {"key1": {"key2": 3}}
        assert dict_get_keypath(data, "key1.key2") == 3
    """
    if property_path is not None:
        keys = property_path.split(".")
        for key in keys:
            match data:
                case dict():
                    data = data[key]
                case list():
                    data = data[int(key)]
    return data


def get_args(func: Callable):
    """Get the arguments of a python methods as a list of strings"""
    params = signature(func).parameters.values()
    return [param.name for param in params if param.kind == param.POSITIONAL_OR_KEYWORD]


def itf(filepath: str, keypath=None):
    """ITF decorator.

    It takes a ITF Json file and keypath.

    Keypath is used to find the tag value at each step of ITF Json.
    The tag values are used to match with appropriate @step decorated methods.
    """

    def decorator(func: Callable) -> Callable:
        with open(filepath, encoding="utf-8") as f:
            trace = json.load(f)["states"]

        # step_fixtures are the fixtures tagged to ITF steps
        if keypath is None:
            # if no tag
            step_fixtures = ["mbt_step"]
        else:
            # collect all fixtures
            step_fixtures = [f"mbt_{dict_get_keypath(step, keypath)}" for step in trace]

        # explicitly use step_fixtures in pytest
        @pytest.mark.usefixtures(*step_fixtures)
        def wrapper(request: FixtureRequest):
            for step in trace:
                try:
                    if keypath is None:
                        step_func = request.getfixturevalue("mbt_step")
                    else:
                        step_func = request.getfixturevalue(
                            f"mbt_{dict_get_keypath(step, keypath)}"
                        )
                    # prepare the kwargs for this method
                    # if the argument is a ITF trace variable, read it from step
                    # else it is a fixture
                    kwargs = {
                        arg: step[arg] if arg in step else request.getfixturevalue(arg)
                        for arg in get_args(step_func)
                    }
                    step_func(**kwargs)
                except pytest.FixtureLookupError as ex:
                    raise RuntimeError("fixture not found") from ex
            # lastly execute the top method, annotated by @itf
            kwargs = {arg: request.getfixturevalue(arg) for arg in get_args(func)}
            func(**kwargs)

        return wrapper

    return decorator


def mbt(tlapath: str, keypath=None, **kwargs):
    """MBT decorator.

    It takes a TLA+ specification and keypath.

    Keypath is used to find the tag value at each step of ITF Json.
    The tag values are used to match with appropriate @step decorated methods.

    Any other parameters are passed to Modelator.Model.Model.check()
    """

    def decorator(func: Callable) -> Callable:
        m = Model.parse_file(file_name=tlapath)
        res = m.check(**kwargs)
        cex_itfs = res.all_traces()

        if keypath is None:
            step_fixtures = ["mbt_step"]
        else:
            step_fixtures = list(
                set(
                    f"mbt_{dict_get_keypath(step.to_json(), keypath)}"
                    for trace in cex_itfs.values()
                    for step in trace
                )
            )

        @pytest.mark.usefixtures(*step_fixtures)
        def wrapper(request: FixtureRequest):
            for trace in cex_itfs.values():
                for step_itf in trace:
                    step = step_itf.to_json()
                    try:
                        if keypath is None:
                            step_func = request.getfixturevalue("mbt_step")
                        else:
                            step_func = request.getfixturevalue(
                                f"mbt_{dict_get_keypath(step, keypath)}"
                            )
                        kwargs = {
                            arg: step[arg]
                            if arg in step
                            else request.getfixturevalue(arg)
                            for arg in get_args(step_func)
                        }
                        step_func(**kwargs)
                    except pytest.FixtureLookupError as ex:
                        raise RuntimeError("fixture not found") from ex
                # execute the top method, annotated by @mbt
                kwargs = {arg: request.getfixturevalue(arg) for arg in get_args(func)}
                func(**kwargs)

        return wrapper

    return decorator


def step(action_name=None):
    """Step decorator.

    It tags a ITF trace step to a python method.

    While iterating the ITF traces, a method will be executed if pytest is at its tagged ITF step.

    step() may not take any value. In that case, any ITF step will be tagged to that method.
    """

    def decorator(func: Callable) -> Callable:
        if action_name is None:
            fixture_name = "mbt_step"
        else:
            fixture_name = f"mbt_{action_name}"
        return pytest.fixture(name=fixture_name)(lambda: func)

    return decorator
