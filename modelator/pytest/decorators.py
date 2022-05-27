import json
from inspect import signature
from typing import Callable

import pytest
from pytest import FixtureRequest


def dummy_itf_collector(_tlapath, _cfgpath):
    return []


def get_args(func: Callable):
    params = signature(func).parameters.values()
    return [param.name for param in params if param.kind == param.POSITIONAL_OR_KEYWORD]


def itf(filepath: str):
    def decorator(func: Callable) -> Callable:
        with open(filepath, encoding="utf-8") as f:
            trace = json.load(f)["states"]
        step_fixtures = [f"mbt_{e['action']['name']}" for e in trace]

        @pytest.mark.usefixtures(*step_fixtures)
        def wrapper(request: FixtureRequest):
            for step in trace:
                action_name = step["action"]["name"]
                try:
                    step_func = request.getfixturevalue(f"mbt_{action_name}")
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


def mbt(tlapath: str, cfgpath: str):
    def decorator(func: Callable) -> Callable:
        cex_itfs = dummy_itf_collector(tlapath, cfgpath)

        @pytest.mark.usefixtures("request")
        def wrapper(request: FixtureRequest):
            for filepath in cex_itfs:
                itf(filepath)(func)(request)

        return wrapper

    return decorator


def step(action_name):
    def decorator(func: Callable) -> Callable:
        fixture_name = f"mbt_{action_name}"
        return pytest.fixture(name=fixture_name)(lambda: func)

    return decorator
