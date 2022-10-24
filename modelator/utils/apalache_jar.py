import hashlib
import io
import logging
import os
import subprocess
import zipfile
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import urlopen

from .. import const_values


def apalache_jar_build_path(checkers_dir: str, version: str) -> str:
    return os.path.join(
        checkers_dir,
        "apalache",
        "lib",
        f"apalache-{version}.jar",
    )


def apalache_jar_version(jar_path=const_values.DEFAULT_APALACHE_JAR) -> str:
    """
    Return the version of the `jar_path`.
    """
    try:
        version = subprocess.check_output(
            ["java", "-jar", jar_path, "version"], text=True, stderr=subprocess.STDOUT
        ).strip()
        return version
    except subprocess.CalledProcessError:
        logging.warning("Error while checking the existence of the jar file")
        return None


def apalache_jar_exists(jar_path: str, expected_version: str) -> bool:
    """
    Check for existence of the `expected_version` of the Apalache uber jar at
    the location `jar_path`.
    """

    logging.debug(f"Checking for jar file at {jar_path}")
    if not Path(jar_path).is_file():
        return False

    version = apalache_jar_version(jar_path)
    if version is None:
        return False

    if version != expected_version:
        logging.debug(
            f"Current existing version is {version} and we are looking for {expected_version}"
        )
        return False

    return True


def apalache_jar_download(
    download_location=const_values.DEFAULT_CHECKERS_LOCATION,
    expected_version=const_values.DEFAULT_APALACHE_VERSION,
    sha256_checksum=None,
):
    """
    Download the `expected_version` of Apalache's uber jar release file to `download_location`.
    Raise an exception if the checksum for the expected version is missing.
    """
    if sha256_checksum is None:
        try:
            sha256_checksum = const_values.APALACHE_SHA_CHECKSUMS[expected_version]
        except KeyError as k_err:
            checksum_url = const_values.apalache_checksum_url(expected_version)
            try:
                with urlopen(checksum_url) as zip_response:
                    for line in zip_response.readlines():
                        if b"apalache.zip" in line:
                            sha256_checksum, _ = line.decode().split()
                    if sha256_checksum is None:
                        raise ValueError(
                            "SHA Checksum is missing from Apalache release. Check Apalache repository to debug."
                        ) from k_err
            except HTTPError as h_err:
                if h_err.code == 404:
                    raise ValueError(
                        "SHA Checksum is missing. Add it manually to `const_values.APALACHE_SHA_CHECKSUMS`"
                    ) from h_err
                raise ValueError(
                    f"Error while fetching the checksum: ({h_err.code}) {h_err.reason}"
                ) from h_err

    release_url = const_values.apalache_release_url(expected_version)

    logging.debug(f"Downloading {release_url} to {download_location}...")
    with urlopen(release_url) as zip_response:
        data = zip_response.read()
        assert sha256_checksum == hashlib.sha256(data).hexdigest()

        with zipfile.ZipFile(io.BytesIO(data)) as zip_file:
            jar_relative_path = "apalache/lib/apalache.jar"
            zip_file.extract(member=jar_relative_path, path=download_location)
            extracted_jar_path = f"{download_location}/{jar_relative_path}"

            final_jar_path = apalache_jar_build_path(
                download_location, expected_version
            )
            os.rename(extracted_jar_path, final_jar_path)
            logging.debug(f"Downloaded version {expected_version} to {final_jar_path}")
