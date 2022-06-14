import json
from inspect import signature
from typing import Callable

import pytest
from pytest import FixtureRequest

from modelator.Model import Model


def dict_get_keypath(data, property_path=None):
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
    params = signature(func).parameters.values()
    return [param.name for param in params if param.kind == param.POSITIONAL_OR_KEYWORD]


def itf(filepath: str, keypath=None):
    def decorator(func: Callable) -> Callable:
        with open(filepath, encoding="utf-8") as f:
            trace = json.load(f)["states"]

        if keypath is None:
            step_fixtures = ["mbt_step"]
        else:
            step_fixtures = [f"mbt_{dict_get_keypath(step, keypath)}" for step in trace]

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
                    kwargs = {
                        arg: step[arg] if arg in step else request.getfixturevalue(arg)
                        for arg in get_args(step_func)
                    }
                    step_func(**kwargs)
                except pytest.FixtureLookupError as ex:
                    raise RuntimeError("fixture not found") from ex
            kwargs = {arg: request.getfixturevalue(arg) for arg in get_args(func)}
            func(**kwargs)

        return wrapper

    return decorator


def mbt(tlapath: str, keypath=None, **kwargs):
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
                kwargs = {arg: request.getfixturevalue(arg) for arg in get_args(func)}
                func(**kwargs)

        return wrapper

    return decorator


def step(action_name=None):
    def decorator(func: Callable) -> Callable:
        if action_name is None:
            fixture_name = "mbt_step"
        else:
            fixture_name = f"mbt_{action_name}"
        return pytest.fixture(name=fixture_name)(lambda: func)

    return decorator
