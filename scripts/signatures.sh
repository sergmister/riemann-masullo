#!/usr/bin/env bash
# Print the signature of every declaration in the library (see scripts/Signatures.lean).
#
#   scripts/signatures.sh > new.txt
#   scripts/signatures.sh --all > new.txt               # private definitions too (see Signatures.lean)
#   scripts/signatures.sh --compare old.txt new.txt     # lists declarations whose statement changed
#
# The comparison allows new declarations: adding a lemma or finishing a proof is fine, but
# changing or removing what others build on is not. Exit status 1 if anything changed or was
# removed.
#
#   scripts/signatures.sh --sorry-in-defs [file]        # lists definitions whose body has a sorry,
#                                                       # and declarations with one in the statement
#
# A definition must not contain `sorry`, even in a proof field: its body would change when the
# proof is filled in, and everything stated with it would shift. A statement must not contain
# one either: it says nothing, and its hash moves with every edit to the file, because such a
# `sorry` carries its source position. Exit status 1 if there are any.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = --compare ]; then
  old=${2:?old signatures}; new=${3:?new signatures}
  changed=$(awk 'FILENAME == ARGV[1] { sig[$2]=$0; next } ($2 in sig) && sig[$2] != $0 { print $2 }' "$old" "$new")
  removed=$(awk 'FILENAME == ARGV[1] { seen[$2]=1; next } !($2 in seen) { print $2 }' "$new" "$old")
  [ -z "$changed" ] || { echo "statement or definition changed:"; echo "$changed" | sed 's/^/  /'; }
  [ -z "$removed" ] || { echo "removed:"; echo "$removed" | sed 's/^/  /'; }
  [ -z "$changed$removed" ]
  exit
fi
if [ "${1:-}" = --sorry-in-defs ]; then
  if [ -n "${2:-}" ]; then bad=$(awk '$NF == "SORRY" { print $2 }' "$2")
  else bad=$("$0" | awk '$NF == "SORRY" { print $2 }'); fi
  [ -z "$bad" ] || { echo "definitions containing sorry, or declarations with one in their statement:"; echo "$bad" | sed 's/^/  /'; }
  [ -z "$bad" ]
  exit
fi
all=; [ "${1:-}" = --all ] && all=--all
lake build RiemannMasullo >/dev/null
modules=$(find RiemannMasullo -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##')
lake env lean --run scripts/Signatures.lean $all $modules
