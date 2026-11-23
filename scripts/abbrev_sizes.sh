#!/usr/bin/env bash
# List the library's `abbrev` type synonyms by the size of their body as a tree and in memory
# (see scripts/AbbrevSizes.lean).
#
#   scripts/abbrev_sizes.sh                 # every type synonym, largest tree first
#   scripts/abbrev_sizes.sh --min 1000000   # only those whose tree has at least that many nodes
#
# A tree far larger than the term in memory marks a synonym whose instances spell out other
# synonyms again and again; AGENTS.md asks for a `def` with its own instances instead.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build RiemannMasullo >/dev/null
modules=$(find RiemannMasullo -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##')
lake env lean --run scripts/AbbrevSizes.lean "$@" $modules
