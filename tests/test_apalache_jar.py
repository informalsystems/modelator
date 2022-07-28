import appdirs
import os
import pytest
import subprocess
import uuid
from modelator import const_values
from modelator.utils.apalache_jar import apalache_jar_exists, apalache_jar_download, apalache_jar_version


def _setup_temp_dir(expected_version: str):
    """
    Create a temporary directory (that will be removed at the end of the test).
    Return the directory and the expected location of the jar file.
    """
    test_download_dir = os.path.join(
        appdirs.user_data_dir(__package__), "tests" + str(uuid.uuid4()), "checkers"
    )
    subprocess.run(["rm", "-rf", test_download_dir])
    subprocess.run(["mkdir", "-p", test_download_dir])
    jar_path = os.path.join(test_download_dir, "apalache", "lib", f"apalache-{expected_version}.jar")

    return test_download_dir, jar_path


def _clean_dir(temp_dir):
    subprocess.run(["rm", "-rf", temp_dir])


def test_version_non_existing_jar_file():
    test_download_dir, jar_path = _setup_temp_dir("0.25.10")

    version = apalache_jar_version(jar_path)
    assert version is None

    _clean_dir(test_download_dir)


@pytest.mark.network
def test_download_ok():
    expected_version = "0.25.10"
    test_download_dir, jar_path = _setup_temp_dir(expected_version)
    assert not apalache_jar_exists(jar_path, expected_version)

    apalache_jar_download(test_download_dir, expected_version, sha256_checksum=None)
    assert apalache_jar_exists(jar_path, expected_version)

    version = apalache_jar_version(jar_path)
    assert version == expected_version

    _clean_dir(test_download_dir)


@pytest.mark.network
def test_download_wrong_checksum():
    expected_version = "0.25.1"
    test_download_dir, jar_path = _setup_temp_dir(expected_version)
    wrong_expected_checksum = const_values.APALACHE_SHA_CHECKSUMS["0.25.0"]

    with pytest.raises(AssertionError):
        apalache_jar_download(test_download_dir, expected_version, wrong_expected_checksum)
    assert not apalache_jar_exists(jar_path, expected_version)

    _clean_dir(test_download_dir)


@pytest.mark.network
def test_download_different_version():
    expected_version = "0.25.1"
    test_download_dir, jar_path = _setup_temp_dir(expected_version)
    correct_expected_checksum = const_values.APALACHE_SHA_CHECKSUMS[expected_version]

    apalache_jar_download(test_download_dir, expected_version, correct_expected_checksum)
    assert apalache_jar_exists(jar_path, expected_version)

    version = apalache_jar_version(jar_path)
    assert version == expected_version

    _clean_dir(test_download_dir)


def test_download_non_existing_version():
    non_existing_version = "25.0"
    test_download_dir, jar_path = _setup_temp_dir(non_existing_version)

    with pytest.raises(ValueError):
        apalache_jar_download(
            test_download_dir, non_existing_version, sha256_checksum=None
        )
    assert not apalache_jar_exists(jar_path, non_existing_version)

    _clean_dir(test_download_dir)
