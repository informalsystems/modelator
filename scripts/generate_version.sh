#!/usr/bin/env bash

set -euo pipefail
set -o xtrace

[ -z $1 ] && echo "No update component provided." && exit 1

# get rust-version
LAST_RUST_VERSION=$(grep -i '^version = ' "$RUST_DIR/modelator/Cargo.toml" | sed 's|^version = "\([^\"]\+\)"|\1|g')

# get python-version
LAST_PYTHON_VERSION=$(grep -i '^version = ' "$PYTHON_DIR/pyproject.toml" | sed 's|^version = "\([^"]\+\)"|\1|g')

# get golang-version
# skip

# get last release tag
LAST_RELEASE_VERSION=$(grep '^## v' CHANGELOG.md | head -1 | sed 's|^## v||g')

echo "Python version $LAST_PYTHON_VERSION"
echo "Rust version $LAST_RUST_VERSION"
echo "Release version $LAST_RELEASE_VERSION"

if [[ "$LAST_RELEASE_VERSION" != "$LAST_RUST_VERSION" || "$LAST_RELEASE_VERSION" != "$LAST_PYTHON_VERSION" ]]; then
    echo "Versions did not the match. Exiting."
    exit 2
fi

function semver_update {
    [ -z $1 ] && [ -z $2 ] && exit 2
    patch_version=$(cut -d'.' -f3 <<< $2)
    minor_version=$(cut -d'.' -f2 <<< $2)
    major_version=$(cut -d'.' -f1 <<< $2)
    case $1 in
        patch)
            echo $major_version.$minor_version.$(( patch_version + 1 ))
            ;;
        minor)
            echo $major_version.$(( minor_version + 1 )).0
            ;;
        major)
            echo $(( major_version + 1 )).0.0
            ;;
    esac
}

echo "RELEASE_VERSION=$(semver_update $1 $LAST_RELEASE_VERSION)" >> $GITHUB_ENV
