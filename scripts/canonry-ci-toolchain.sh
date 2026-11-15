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

# Register the standard library: a library file, a libraries list, a defaults list.
lib_file="${RUNNER_TEMP}/standard-library.agda-lib"
printf 'name: standard-library\ninclude: /usr/share/agda-stdlib\n' > "${lib_file}"

mkdir -p "${HOME}/.agda"
printf '%s\n' "${lib_file}" >> "${HOME}/.agda/libraries"
printf 'standard-library\n' >> "${HOME}/.agda/defaults"

agda --version
dpkg-query -W agda-bin agda-stdlib
