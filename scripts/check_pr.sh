#!/usr/bin/env bash
# Integrator's tool: check a pull request that did not come from the launcher, such as one from
# a fork, without trusting its code.
#
#   scripts/check_pr.sh <number>
#
# It merges the pull request into a copy of the current main in a scratch worktree and, under
# bwrap with no network and no home directory, runs the lint, the build and the signature dump.
# It then reports which files changed, whether any existing declaration's statement changed,
# whether a definition contains `sorry`, and how many `sorry`s were added. Nothing is pushed or
# merged; read the diff and decide.
set -euo pipefail
n=${1:?usage: check_pr.sh <pull request number>}
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"
command -v bwrap >/dev/null || { echo "bwrap (bubblewrap) is required" >&2; exit 2; }
wt="$(dirname "$main")/$(basename "$main")-wt/pr-$n"
# CHECK_PR_NO_FETCH=1 when the caller (scripts/triage_prs.sh) has already fetched everything,
# so that several checks can run side by side without contending for git's ref locks.
[ -n "${CHECK_PR_NO_FETCH:-}" ] || git fetch -q origin main "+pull/$n/head:refs/remotes/origin/pr-$n"
base=$(git rev-parse --verify "${CHECK_PR_BASE:-origin/main}^{commit}")
head=$(git rev-parse --verify "${CHECK_PR_HEAD:-origin/pr-$n}^{commit}")
[ -d "$wt" ] && git worktree remove --force "$wt"
# A detached worktree: creating a branch would write to .git/config, which checks running side
# by side would fight over.
git worktree add -q --detach "$wt" "$base"
trap 'cd "$main"; git worktree remove --force "$wt" 2>/dev/null || true' EXIT
cd "$wt"
mkdir -p .lake .agent && ln -sfn "$main/.lake/packages" .lake/packages

echo "checking $head against $base"
files=$(git diff --name-only "$base...$head")
echo "files changed:"; echo "$files" | sed 's/^/  /'
stray=$(echo "$files" | awk '!/^RiemannMasullo\/.*\.lean$/ || /^RiemannMasullo\/External\//')
[ -z "$stray" ] || { echo "REFUSED: changes outside the library; read these by hand before running anything:"; echo "$stray" | sed 's/^/  /'; exit 1; }
git merge -q --no-edit "$head" || { echo "REFUSED: does not merge cleanly into main"; exit 1; }

# Compare the merged candidate with main so existing imports are allowed.
if lean --run "$main/scripts/CheckImportAll.lean" "$base" HEAD; then
  :
else
  status=$?
  if [ "$status" = 3 ]; then
    echo 'REFUSED: adds `import all`. Use ordinary imports and expose the required lemmas (see AGENTS.md).'
    exit 1
  fi
  if [ "$status" = 4 ]; then
    echo 'REFUSED: invalid Lean import header'
    exit 1
  fi
  echo 'could not check the import policy' >&2
  exit 2
fi

# Reuse the launcher's build as a starting point. Copy under its lock so that a
# seed refresh cannot change the files mid-copy. Lake still builds the exact
# baseline and merged sources below.
seed="$(dirname "$wt")/seed"
seeded=0
if [ -f "$seed/.lake/built-at" ]; then
  if (
    flock -s -w 5 8 &&
    seed_head=$(git -C "$seed" rev-parse --verify HEAD) &&
    git merge-base --is-ancestor "$seed_head" "$base" &&
    git diff --quiet "$seed_head" "$base" -- lean-toolchain lake-manifest.json lakefile.lean lakefile.toml &&
    cp -a --reflink=auto "$seed/.lake/build" .lake/build &&
    echo "starting from the local seed build at ${seed_head:0:12}"
  ) 8>>"$main/.agent/seed.lock"; then
    seeded=1
  else
    rm -rf .lake/build
  fi
fi

# A conflict needs no Lean build. On a cache miss, return to trusted main before
# running the baseline build, then restore the exact merge for the sandbox.
basefile="$main/.agent/base/pinned-main-$base.txt"
if [ ! -s "$basefile" ]; then
  merged=$(git rev-parse HEAD)
  git checkout -q --detach "$base"
  [ "$seeded" = 0 ] || python3 scripts/ci/prune_build.py >/dev/null
  mkdir -p "$main/.agent/base"
  scripts/signatures.sh >"$basefile.$$"
  mv "$basefile.$$" "$basefile"
  git checkout -q --detach "$merged"
fi
[ "$seeded" = 0 ] || python3 "$main/scripts/ci/prune_build.py" --root "$wt" >/dev/null
cp "$basefile" .agent/base.txt
echo "sorries added: $(git diff "$base" HEAD | grep -E '^\+[^+]' | grep -cw sorry || true)"

sandboxed() {
  bwrap --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --tmpfs /run --tmpfs "$HOME" \
    --ro-bind "$HOME/.elan" "$HOME/.elan" --ro-bind "$main/.lake/packages" "$main/.lake/packages" \
    --bind "$wt" "$wt" --chdir "$wt" --unshare-net --die-with-parent "$@"
}
if sandboxed bash -c 'scripts/lint.sh && lake build && scripts/signatures.sh >.agent/head.txt' >.agent/build.txt 2>&1; then
  echo "lint and build: pass"
else
  echo "lint or build: FAIL"; tail -n 20 .agent/build.txt; exit 1
fi
status=0
if "$main/scripts/signatures.sh" --compare "$wt/.agent/base.txt" "$wt/.agent/head.txt"; then
  echo "statements: none of $(wc -l <.agent/base.txt) existing declarations changed"
else
  status=1
fi
if "$main/scripts/signatures.sh" --sorry-in-defs "$wt/.agent/head.txt"; then
  echo "definitions: none contains sorry"
else
  status=1
fi
exit "$status"
