"""Automatic proof selection respects per-file capacity; listings keep overflow visible."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "next_issue.py"
LOW = "RiemannMasullo/AppA/Sec1.lean"
HIGH = "RiemannMasullo/Ch02/Sec1.lean"

FAKE_GH = """#!/usr/bin/env python3
import json, pathlib, sys
data = json.loads(pathlib.Path(__file__).with_name("responses.json").read_text())
if any("/pulls?" in arg for arg in sys.argv[1:]):
    print("\\n".join(data["pulls"]))
elif any("/issues?" in arg for arg in sys.argv[1:]):
    for row in data["issues"]:
        print(json.dumps(row))
else:
    sys.exit("unexpected gh invocation")
"""


def issue(number, path=LOW, *labels):
    return dict(number=number, labels=list(labels),
                body=f"<!-- sorry: {path}::theorem_{number} -->")


class NextIssueCapacityTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        (self.root / "scripts").mkdir()
        self.script = self.root / "scripts/next_issue.py"
        shutil.copyfile(SOURCE, self.script)
        for path, text in ((LOW, ""), (HIGH, "import RiemannMasullo.AppA.Sec1\n")):
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        gh = self.bin / "gh"
        gh.write_text(FAKE_GH, encoding="utf-8")
        gh.chmod(0o755)

    def select(self, issues, *args, pulls=()):
        (self.bin / "responses.json").write_text(
            json.dumps(dict(issues=issues, pulls=list(pulls))), encoding="utf-8")
        env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ.get("PATH", ""))
        result = subprocess.run(
            [sys.executable, str(self.script), "proof", *args],
            cwd=self.root, env=env, capture_output=True, text=True, timeout=10,
        )
        self.assertEqual(result.stderr, "")
        return result.returncode, result.stdout

    def saturated(self):
        return [issue(n, LOW, "claimed") for n in (1, 2, 3)] + [issue(4)]

    def test_no_assignment_when_all_files_are_full(self):
        self.assertEqual(self.select(self.saturated()), (1, ""))

    def test_full_low_file_does_not_hide_available_higher_file(self):
        self.assertEqual(self.select(self.saturated() + [issue(5, HIGH)]), (0, "5\n"))

    def test_last_slot_is_available(self):
        rows = [issue(n, LOW, "claimed") for n in (1, 2)] + [issue(3), issue(5, HIGH)]
        self.assertEqual(self.select(rows), (0, "3\n"))

    def test_no_free_issues(self):
        rows = [issue(1, LOW, "claimed"), issue(2, LOW, "blocked"),
                issue(3, LOW, "stuck"), issue(4, LOW, "gap")]
        self.assertEqual(self.select(rows), (1, ""))

    def test_list_shows_overflow_after_available_choices(self):
        self.assertEqual(
            self.select(self.saturated() + [issue(5, HIGH)], "--list"),
            (0, f"#5\t{HIGH}\t(in flight there: 0)\n#4\t{LOW}\t(in flight there: 3)\n"),
        )

    def test_list_still_shows_saturated_files(self):
        self.assertEqual(
            self.select(self.saturated(), "--list"),
            (0, f"#4\t{LOW}\t(in flight there: 3)\n"),
        )

    def test_open_pull_request_counts_towards_capacity(self):
        rows = [issue(n, LOW, "claimed") for n in (1, 2)] + [issue(3), issue(4)]
        self.assertEqual(self.select(rows, pulls=("prover/3",)), (1, ""))


if __name__ == "__main__":
    unittest.main()
