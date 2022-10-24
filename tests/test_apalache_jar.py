import os

import pytest

from modelator import const_values
from modelator.utils.apalache_jar import (
    apalache_jar_download,
    apalache_jar_exists,
    apalache_jar_version,
)


def _setup_temp_dir(tmp_path, expected_version: str):
    """
    Create a temporary directory for downloading the jar files. The directory
    will be automatically removed at the end of the test. Return the directory
    and the expected location of the jar file.
    """
    test_download_dir = tmp_path / "checkers"
    jar_path = os.path.join(
        test_download_dir, "apalache", "lib", f"apalache-{expected_version}.jar"
    )

    return test_download_dir, jar_path


def test_version_non_existing_jar_file(tmp_path):
    _, jar_path = _setup_temp_dir(tmp_path, "0.25.10")

    version = apalache_jar_version(jar_path)
    assert version is None


@pytest.mark.network
def test_download_ok(tmp_path):
    expected_version = "0.25.10"
    test_download_dir, jar_path = _setup_temp_dir(tmp_path, expected_version)
    assert not apalache_jar_exists(jar_path, expected_version)

    apalache_jar_download(test_download_dir, expected_version, sha256_checksum=None)
    assert apalache_jar_exists(jar_path, expected_version)

    version = apalache_jar_version(jar_path)
    assert version == expected_version


@pytest.mark.network
def test_download_wrong_checksum(tmp_path):
    expected_version = "0.25.1"
    test_download_dir, jar_path = _setup_temp_dir(tmp_path, expected_version)
    wrong_expected_checksum = const_values.APALACHE_SHA_CHECKSUMS["0.25.0"]

    with pytest.raises(AssertionError):
        apalache_jar_download(
            test_download_dir, expected_version, wrong_expected_checksum
        )
    assert not apalache_jar_exists(jar_path, expected_version)


@pytest.mark.network
def test_download_different_version(tmp_path):
    expected_version = "0.25.1"
    test_download_dir, jar_path = _setup_temp_dir(tmp_path, expected_version)
    correct_expected_checksum = const_values.APALACHE_SHA_CHECKSUMS[expected_version]

    apalache_jar_download(
        test_download_dir, expected_version, correct_expected_checksum
    )
    assert apalache_jar_exists(jar_path, expected_version)

    version = apalache_jar_version(jar_path)
    assert version == expected_version


def test_download_non_existing_version(tmp_path):
    non_existing_version = "25.0"
    test_download_dir, jar_path = _setup_temp_dir(tmp_path, non_existing_version)

    with pytest.raises(ValueError):
        apalache_jar_download(
            test_download_dir, non_existing_version, sha256_checksum=None
        )
    assert not apalache_jar_exists(jar_path, non_existing_version)
