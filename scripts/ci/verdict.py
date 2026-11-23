#!/usr/bin/env python3
"""Check a pull request against main and say what should happen to it.

    scripts/ci/verdict.py --work DIR --base SHA --head SHA [--pr N] [--out DIR]
                          [--base-signatures FILE]

The verdict is the one scripts/triage_prs.sh computes on the merger's machine:

    merge   it builds on top of main, passes the lint, changes or removes no existing
            declaration, puts no `sorry` in a definition, and does nothing but fill in proofs
            and add lemmas in existing files of the library
    read    it passes, but a person should look first: a new `sorry` (a split or new
            statements), a new file or definition, an attribute, anything outside the library
    fail    it does not merge into main, build, pass the lint, or keep existing statements,
            or it makes a type synonym exponentially large (see LARGE_SYNONYM)
    error   the check itself could not be carried out (main does not build, say); this says
            nothing about the pull request

Nothing here comes from the pull request except the commit being judged. This script, the lint,
the signature dump, the lakefile, the toolchain file and the manifest are the base's: DIR is a
checkout of main at SHA `--base` with its dependencies already fetched, and this file is run
from a checkout of main too (it may be the same one). The pull request must already be in DIR's
object store (`git fetch origin pull/N/head`); it is never checked out as a whole.

Order of work, and why:
  1. The list of changed files is read from git. Anything that is not an ordinary Lean file
     of the library ends the check with `read`: nothing from such a pull request is built here,
     because a lakefile, a toolchain file or a script could change what "builds" means.
  2. Whether the change is plain proof text is decided from the text (plain_proof.py, and
     main's scripts/proof_review.sh), before any of it is built. Nothing found later can turn
     `read` back into `merge`.
  3. Main is built, its type synonyms measured (scripts/AbbrevSizes.lean) and its signatures
     taken, unless `--base-signatures` supplies the signatures. This is
     main's own code and runs as any build of main does.
  4. The pull request is merged into the tree and the result is linted, built and dumped,
     each step in its own sandbox (sandbox.sh): no network, a read-only file system apart from
     the build directory, an empty environment. The outputs are read as text.

Writes verdict.json and summary.md to `--out` (default: DIR/.agent/verdict) and prints the
verdict. Exit status: 0 for merge and read, 1 for fail, 2 for error.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import plain_proof

TOOLS = Path(__file__).resolve().parent.parent.parent   # the checkout this script is in
SHA = re.compile(r"[0-9a-f]{40}")
SORRY_WARNING = re.compile(r"^warning: (RiemannMasullo/\S+\.lean):\d+:\d+: declaration uses `sorry`\s*$", re.M)
SIGNATURE_LINE = re.compile(
    r"(theorem|def|opaque|axiom|inductive|constructor|recursor|quot) (\S+) \d+( \d+)?( SORRY)?")
BUILD_MINUTES = 45
# A type synonym whose body is this many nodes as a tree spells out other synonyms again and again
# in its instance terms; parts of Lean walk those terms as trees and stop finishing (#5398, #5716).
# A pull request fails if it adds such a synonym or makes one larger than on main.
LARGE_SYNONYM = 10 ** 8


# Remarks for the summary that do not change the verdict: a measurement that could not run
# must not stop the automatic merge of every pull request at once.
NOTES = []


class Stop(Exception):
    """The verdict is known."""
    def __init__(self, verdict, reasons, log=""):
        super().__init__(verdict)
        self.verdict, self.reasons, self.log = verdict, reasons, log


def run(cmd, cwd=None, timeout=None, check=False, text=True):
    return subprocess.run(cmd, cwd=cwd, timeout=timeout, check=check, text=text,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)


class Check:
    def __init__(self, work, base, head):
        self.work, self.base, self.head = Path(work).resolve(), base, head
        self.sandbox = str(TOOLS / "scripts/ci/sandbox.sh")
        self.merge_base = None
        self.files = []

    def git(self, *args, check=True, text=True):
        cmd = ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false",
               "-c", "user.name=ci", "-c", "user.email=ci@invalid", *args]
        result = subprocess.run(cmd, cwd=self.work, stdin=subprocess.DEVNULL, capture_output=True, text=text)
        if check and result.returncode:
            raise Stop("error", [f"git {args[0]} failed"], str(result.stderr)[-2000:])
        return result

    def lake(self, *cmd, timeout=None, sandboxed=True, quiet=False):
        """Run a command in the work tree; returns (status, output).

        The output is what the command wrote to stdout and stderr together, or with `quiet`
        to stdout alone when it succeeds.

        Everything runs in the sandbox (sandbox.sh) once the pull request is in the tree.
        `sandboxed=False` is for main's own code before that: the first build of a fresh
        checkout has to write next to the dependencies (their compiled lakefiles, Lake's file
        hashes) and may fetch a dependency's prebuilt files, which the sandbox does not allow.
        """
        prefix = [self.sandbox, str(self.work), str(TOOLS), "--"] if sandboxed else []
        try:
            result = subprocess.run([*prefix, *cmd], cwd=self.work,
                                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE if quiet else subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired as late:
            return None, (late.stdout or b"").decode("utf-8", "replace")
        if quiet and result.returncode:
            return result.returncode, (result.stdout + result.stderr).decode("utf-8", "replace")
        return result.returncode, result.stdout.decode("utf-8", "replace")

    # 1. What the pull request changes.

    def changed_files(self):
        if self.git("rev-parse", "HEAD").stdout.strip() != self.base:
            raise Stop("error", ["the work tree is not at the base commit"])
        if self.git("status", "--porcelain", "--untracked-files=no").stdout.strip():
            raise Stop("error", ["the work tree has local changes"])
        found = self.git("merge-base", self.base, self.head, check=False)
        if found.returncode:
            raise Stop("fail", ["the pull request shares no history with main"])
        self.merge_base = found.stdout.strip()
        raw = self.git("diff", "--raw", "-z", "--no-renames", "--no-abbrev",
                       self.merge_base, self.head, text=False).stdout.split(b"\0")
        entries = []
        for meta, path in zip(raw[0::2], raw[1::2]):
            old_mode, new_mode, old_sha, new_sha, status = meta.decode("ascii").lstrip(":").split()
            entries.append(dict(path=path.decode("utf-8", "backslashreplace"), status=status,
                                old_mode=old_mode, new_mode=new_mode, old=old_sha, new=new_sha))
        if not entries:
            raise Stop("read", ["the pull request changes no file"])
        self.files = [e["path"] for e in entries]
        outside = [e["path"] for e in entries if not (
            plain_proof.library_file(e["path"])
            and e["status"] in ("A", "M", "D")
            and e["old_mode"] in ("100644", "000000") and e["new_mode"] in ("100644", "000000"))]
        if outside:
            shown = ", ".join(repr(p) for p in outside[:10]) + (" ..." if len(outside) > 10 else "")
            raise Stop("read", ["it changes files outside the library, or files that are not ordinary "
                                f"Lean files ({shown}): nothing was built or checked"])
        return entries

    # 2. Is it plain proof text?

    def blob(self, sha):
        size = int(self.git("cat-file", "-s", sha).stdout)
        if size > plain_proof.MAX_FILE_BYTES:
            return None
        return self.git("cat-file", "blob", sha, text=False).stdout

    def held_back(self, entries):
        """Reasons, from the text alone, that a person should read this pull request."""
        reasons, files = [], []
        for e in entries:
            if e["status"] == "A":
                reasons.append(f"new file {e['path']}")
                new = self.blob(e["new"])
                if new is not None and re.search(rb"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", new):
                    reasons.append(f"{e['path']}: adds a `sorry`")
            elif e["status"] == "D":
                reasons.append(f"deletes {e['path']}")
            else:
                old, new = self.blob(e["old"]), self.blob(e["new"])
                if old is None or new is None:
                    reasons.append(f"{e['path']} is too large to check")
                    continue
                files.append((e["path"], old, new))
        reasons += plain_proof.classify_change(files)
        # The local scripts' own rules, from main's copy, so that this never merges what they
        # would hold back, whatever is added there later. It reads the diff; it runs nothing.
        review = TOOLS / "scripts/proof_review.sh"
        if review.is_file():
            done = subprocess.run(["bash", str(review), self.base, self.head], cwd=self.work, text=True,
                                  stdin=subprocess.DEVNULL, capture_output=True)
            if done.returncode:
                raise Stop("error", ["scripts/proof_review.sh could not read the diff"], done.stderr)
            if done.stdout.strip():
                reasons.append("scripts/proof_review.sh: " + done.stdout.strip())
        return reasons

    def lint_text(self, entries):
        """The lint, on the pull request's own versions of the files, before anything is built."""
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "RiemannMasullo").mkdir()
            for e in entries:
                if e["status"] == "D":
                    continue
                data = self.blob(e["new"])
                if data is None:
                    continue
                target = Path(tmp) / e["path"]
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            result = run([str(TOOLS / "scripts/lint.sh"), tmp])
        if result.returncode == 1:
            raise Stop("fail", ["the lint found a forbidden construct (see AGENTS.md)"], result.stdout)
        if result.returncode:
            raise Stop("error", ["the lint could not run"], result.stdout)

    # 3 and 4. Build.

    def build(self, sandboxed=True):
        return self.lake("lake", "build", timeout=BUILD_MINUTES * 60, sandboxed=sandboxed)

    def modules(self):
        found = []
        for root, _dirs, names in os.walk(self.work / "RiemannMasullo"):
            for name in names:
                if name.endswith(".lean"):
                    rel = (Path(root) / name).relative_to(self.work)
                    found.append(".".join(rel.with_suffix("").parts))
        return sorted(found)

    def signatures(self):
        status, out = self.lake("lake", "env", "lean", "--run", str(TOOLS / "scripts/Signatures.lean"),
                                "--all", *self.modules(), timeout=1200, quiet=True)
        return (out if status == 0 else None), out

    def synonym_sizes(self):
        """Tree sizes of the type synonyms of at least LARGE_SYNONYM nodes, or None if the
        measurement did not run (scripts/AbbrevSizes.lean)."""
        script = TOOLS / "scripts/AbbrevSizes.lean"
        if not script.is_file():
            return None
        status, out = self.lake("lake", "env", "lean", "--run", str(script), "--min", str(LARGE_SYNONYM),
                                *self.modules(), timeout=300, quiet=True)
        return parse_sizes(out) if status == 0 else None

    def keywords_current(self):
        """Whether the checked-in list of command keywords matches main as just built."""
        status, out = self.lake("lake", "env", "lean", "--run", str(TOOLS / "scripts/ci/CommandKeywords.lean"),
                                *self.modules(), timeout=1200, quiet=True)
        listed = (TOOLS / "scripts/ci/command_keywords.txt").read_text(encoding="utf-8")
        listed = "".join(line + "\n" for line in listed.split("\n") if line and not line.startswith("#"))
        return status == 0 and out == listed, out

    def docstrings_inert(self):
        """Whether main leaves doc comments as plain text (the option `doc.verso` is not used).

        plain_proof.py ignores comments. With Verso docstrings Lean elaborates code inside them.
        """
        sources = [self.work / "lakefile.toml", self.work / "lakefile.lean"]
        sources += [self.work / (m.replace(".", "/") + ".lean") for m in self.modules()]
        return not any(b"doc.verso" in path.read_bytes() for path in sources if path.is_file())

    def base_state(self, supplied):
        result = run([str(TOOLS / "scripts/lint.sh"), str(self.work)])
        if result.returncode:
            raise Stop("error", ["main itself does not pass the lint"], result.stdout)
        if not self.docstrings_inert():
            raise Stop("error", ["main sets the option doc.verso, which makes Lean elaborate code inside doc "
                                 "comments; scripts/ci/plain_proof.py ignores comments and has to be revised first"])
        status, log = self.build(sandboxed=False)
        if status is None:
            raise Stop("error", [f"building main did not finish in {BUILD_MINUTES} minutes, so the pull "
                                 "request could not be checked; this is not a fault of the pull request"], log)
        if status != 0:
            raise Stop("error", ["main itself does not build at this commit, so the pull request "
                                 "could not be checked"], log)
        current, out = self.keywords_current()
        if not current:
            raise Stop("error", ["scripts/ci/command_keywords.txt is out of date on main, so pull requests "
                                 "cannot be judged from their text: run scripts/ci/keywords.sh --write on main"], out)
        sizes = self.synonym_sizes()
        if supplied:
            return supplied, log, sizes
        dump, out = self.signatures()
        if dump is None:
            raise Stop("error", ["the signature dump of main failed"], out)
        return dump, log, sizes

    def merge(self, entries):
        merged = self.git("merge", "--no-commit", "--no-ff", self.head, check=False)
        if merged.returncode:
            self.git("merge", "--abort", check=False)
            raise Stop("fail", ["it does not merge cleanly into main: merge main into the branch "
                                "and resolve the conflicts"], merged.stdout + merged.stderr)
        touched = self.git("diff", "--name-only", "-z", "--no-renames", self.base).stdout.split("\0")
        strays = [p for p in touched if p and p not in self.files]
        if strays:
            raise Stop("error", ["merging changed files the pull request does not list"], "\n".join(strays))

    def held_back_after_merge(self, entries):
        """The text check again, on what the merge made of each file main has changed too.

        A pull request is judged on its own diff, but what lands is that diff applied to main's
        version of the file, where the same lines can sit in a different command.
        """
        reasons = []
        scanner = plain_proof.Scanner()
        for e in entries:
            if e["status"] != "M":
                continue
            ours = self.git("rev-parse", f"{self.base}:{e['path']}", check=False).stdout.strip()
            if ours == e["old"] or not SHA.fullmatch(ours):
                continue       # main has the version the pull request started from
            old, new = self.blob(ours), (self.work / e["path"]).read_bytes()
            if old is None or len(new) > plain_proof.MAX_FILE_BYTES:
                reasons.append(f"{e['path']} is too large to check")
                continue
            reasons += [f"{e['path']} (merged with main): {detail}"
                        for _kind, detail in plain_proof.classify(old, new, scanner)]
        return reasons


def parse_sizes(text):
    """{synonym: tree size} from the output of scripts/AbbrevSizes.lean."""
    sizes = {}
    for line in text.split("\n"):
        fields = line.split("\t")
        if len(fields) >= 3 and fields[2].isdigit():
            sizes[fields[0]] = int(fields[2])
    return sizes


def grown_synonyms(base, head):
    """The synonyms of `head` (all at least LARGE_SYNONYM) that are new or larger than in `base`."""
    return sorted(n for n, size in head.items() if size >= LARGE_SYNONYM and size > base.get(n, 0))


def compare(base, head):
    """(changed, removed, added other than theorems, malformed lines) between two dumps.

    The dumps are made with `--all`, so they list private definitions too; the caller treats
    those apart (names beginning `_private.`).
    """
    def table(text):
        rows, bad = {}, []
        for line in text.split("\n"):
            if not line:
                continue
            m = SIGNATURE_LINE.fullmatch(line)
            if m:
                rows.setdefault(m.group(2), []).append(line)
            else:
                bad.append(line)
        return rows, bad
    old, _ = table(base)
    new, bad = table(head)
    changed = sorted(n for n in old if n in new and old[n] != new[n])
    removed = sorted(n for n in old if n not in new)
    added = sorted(n for n in new if n not in old and any(not l.startswith("theorem ") for l in new[n]))
    return changed, removed, added, bad


def sorry_counts(log):
    counts = {}
    for path in SORRY_WARNING.findall(log):
        counts[path] = counts.get(path, 0) + 1
    return counts


def names(items, limit=12):
    return ", ".join(items[:limit]) + (f" and {len(items) - limit} more" if len(items) > limit else "")


def decide(check, supplied_base):
    entries = check.changed_files()
    held = check.held_back(entries)
    check.lint_text(entries)
    # A conflict is reported before the long build of main, when git can tell without a work tree.
    probe = check.git("merge-tree", "--write-tree", "--no-messages", check.base, check.head, check=False)
    if probe.returncode == 1:
        raise Stop("fail", ["it does not merge cleanly into main: merge main into the branch and "
                            "resolve the conflicts"])
    candidate = probe.stdout.strip()
    if probe.returncode or not SHA.fullmatch(candidate):
        raise Stop("error", ["could not compute the candidate merge tree"], probe.stderr)
    imports = run(["lean", "--run", str(TOOLS / "scripts/CheckImportAll.lean"),
                   check.base, candidate], cwd=check.work, timeout=60)
    if imports.returncode == 3:
        raise Stop("fail", ["it adds `import all`: use ordinary imports and expose the required lemmas "
                             "(see AGENTS.md)"], imports.stdout)
    if imports.returncode == 4:
        raise Stop("fail", ["it has an invalid Lean import header"], imports.stdout)
    if imports.returncode:
        raise Stop("error", ["the import policy check could not be carried out"], imports.stdout)
    base_dump, base_log, base_sizes = check.base_state(supplied_base)
    check.merge(entries)
    held += [r for r in check.held_back_after_merge(entries) if r not in held]
    result = run([str(TOOLS / "scripts/lint.sh"), str(check.work)])
    if result.returncode:
        raise Stop("fail", ["the lint found a forbidden construct (see AGENTS.md)"], result.stdout)
    status, log = check.build()
    if status is None:
        raise Stop("fail", [f"the build did not finish in {BUILD_MINUTES} minutes"], log)
    if status != 0:
        raise Stop("fail", ["it does not build on top of main"], log)
    head_dump, out = check.signatures()
    if head_dump is None:
        raise Stop("fail", ["the signature dump failed after the build"], out)
    head_sizes = check.synonym_sizes()

    changed, removed, added, bad = compare(base_dump, head_dump)
    # A private definition cannot be mentioned by a public statement of a `module` file, so
    # reworking one is not a changed statement; but it is not a finished proof and nothing else.
    private = sorted(n for n in changed + removed if n.startswith("_private."))
    changed = [n for n in changed if not n.startswith("_private.")]
    removed = [n for n in removed if not n.startswith("_private.")]
    failures = []
    if changed:
        failures.append("it changes the statement or definition of existing declarations: " + names(changed))
    if removed:
        failures.append("it removes existing declarations: " + names(removed))
    already = {l.split(" ")[1] for l in base_dump.split("\n") if l.endswith(" SORRY")}
    sorry_defs = sorted({l.split(" ")[1] for l in head_dump.split("\n") if l.endswith(" SORRY")} - already)
    if sorry_defs:
        failures.append("definitions contain `sorry`, or declarations have one in their statement: "
                        + names(sorry_defs))
    if base_sizes is not None and head_sizes is not None:
        grown = grown_synonyms(base_sizes, head_sizes)
        if grown:
            failures.append("type synonyms of over 10^8 nodes as a tree, new or larger than on main: "
                            + names(grown) + ". Make them defs with their own instances (AGENTS.md, #5398)")
    else:
        NOTES.append("the size of type synonyms could not be measured (scripts/AbbrevSizes.lean), "
                     "so new or grown synonyms were not checked")
    if failures:
        raise Stop("fail", failures, log)

    # Checks that do not rest on the text, in case the text was read wrong.
    if private:
        held.append("it changes or removes private definitions: " + names(private))
    if added:
        held.append("it adds declarations that are not theorems: " + names(added))
    if bad:
        held.append("the signature dump has lines that could not be read")
    before, after = sorry_counts(base_log), sorry_counts(log)
    more = sorted(p for p in after if after[p] > before.get(p, 0))
    if more:
        held.append("Lean reports more declarations using `sorry` than on main in " + names(more))
    if held:
        raise Stop("read", held, log)
    raise Stop("merge", [], log)


NEXT = {
    "merge": "It only fills in proofs and adds lemmas, and Lean has checked them. It will be merged "
             "automatically if `main` has not changed the same files in the meantime.",
    "read": "It passes, but it is not only finished proofs, so the integrator will read it before merging.",
    "fail": "It cannot be merged as it is. Fix what is listed below and push again.",
    "error": "The check could not be carried out. This says nothing about the pull request; the "
             "check can be run again.",
}


def clean(text, limit):
    """Text from the pull request or the build, made safe to show inside a code block."""
    text = re.sub(r"[^\x09\x0a\x20-\x7e -\U0010ffff]", "?", text).replace("```", "'''")
    return text if len(text) <= limit else "...\n" + text[-limit:]


def report(args, verdict, reasons, log):
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    reasons = [clean(r, 600).replace("\n", " ") for r in reasons[:40]] + (
        ["(more reasons not shown)"] if len(reasons) > 40 else [])
    data = dict(schema=1, verdict=verdict, pr=args.pr, head_sha=args.head, base_sha=args.base, reasons=reasons,
                notes=list(NOTES))
    (out / "verdict.json").write_text(json.dumps(data, indent=1) + "\n")
    lines = [f"## Verdict: `{verdict}`", "", NEXT[verdict], "",
             f"Checked commit `{args.head[:12]}` against `main` at `{args.base[:12]}`, "
             "with the checker, lakefile and toolchain of `main`.", ""]
    if reasons:
        lines += ["```", *reasons, "```", ""]
    if NOTES:
        lines += ["Notes (they do not change the verdict):", "", *[f"- {clean(n, 600)}" for n in NOTES], ""]
    if log and verdict in ("fail", "error"):
        tail = "\n".join(clean(log, 6000).split("\n")[-60:])
        lines += ["<details><summary>Last lines of the output</summary>", "", "```", tail, "```", "", "</details>", ""]
    (out / "summary.md").write_text("\n".join(lines))
    print(f"verdict: {verdict}")
    for reason in reasons:
        print(f"  {reason}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--work", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--pr", type=int, default=0)
    parser.add_argument("--out")
    parser.add_argument("--base-signatures")
    args = parser.parse_args()
    args.out = args.out or str(Path(args.work) / ".agent/verdict")
    try:
        if not (SHA.fullmatch(args.base) and SHA.fullmatch(args.head)):
            raise Stop("error", ["--base and --head must be full commit ids"])
        supplied = Path(args.base_signatures).read_text() if args.base_signatures else None
        decide(Check(args.work, args.base, args.head), supplied)
    except Stop as stop:
        verdict, reasons, log = stop.verdict, stop.reasons, stop.log
    except Exception as problem:  # the check broke: never report that as the pull request's fault
        verdict, reasons, log = "error", [f"the check stopped unexpectedly ({type(problem).__name__})"], repr(problem)
    report(args, verdict, reasons, log)
    return {"merge": 0, "read": 0, "fail": 1}.get(verdict, 2)


if __name__ == "__main__":
    sys.exit(main())
