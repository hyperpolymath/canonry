#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# canonry-ci-toolchain.sh - provision the Agda toolchain for the Canonry proof
# gate (.github/workflows/canonry.yml) on an ubuntu-24.04 runner.
#
# The pinned profile is:
#   agda-bin     2.6.3-1build1
#   agda-stdlib  1.7.3-1
# The script installs those two packages, registers the standard library for
# Agda, and prints the versions that are in use. It needs sudo and the
# RUNNER_TEMP variable that GitHub Actions sets. It fails loudly on any error.
set -euo pipefail

: "${RUNNER_TEMP:?RUNNER_TEMP must be set (GitHub Actions sets it)}"

AGDA_BIN_VERSION="2.6.3-1build1"
AGDA_STDLIB_VERSION="1.7.3-1"

sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  "agda-bin=${AGDA_BIN_VERSION}" \
  "agda-stdlib=${AGDA_STDLIB_VERSION}"

# Agda writes an interface file beside each library source that it checks.
# /usr/share/agda-stdlib belongs to root, so the runner user cannot write
# there, and the check fails with "Failed to write interface". Use a copy that
# the runner user owns. The shipped interface files are not copied: they were
# built without the flags of the proof gate.
lib_dir="${RUNNER_TEMP}/agda-stdlib"
rm -rf "${lib_dir}"
cp -r /usr/share/agda-stdlib "${lib_dir}"
find "${lib_dir}" -name '*.agdai' -delete

# Register the standard library: a library file, a libraries list, a defaults list.
# The library file must not be in a parent directory of the checkout: Agda
# would take it as the project file and drop the checkout from its search path.
lib_file="${RUNNER_TEMP}/standard-library.agda-lib"
printf 'name: standard-library\ninclude: %s\n' "${lib_dir}" > "${lib_file}"

mkdir -p "${HOME}/.agda"
printf '%s\n' "${lib_file}" > "${HOME}/.agda/libraries"
printf 'standard-library\n' > "${HOME}/.agda/defaults"

agda --version
dpkg-query -W agda-bin agda-stdlib
