"""Signature comparisons reject removals, including an empty new dump."""
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "signatures.sh"


class SignaturesCompareTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.old = self.root / "old.txt"
        self.new = self.root / "new.txt"

    def compare(self, old, new):
        self.old.write_text(old, encoding="utf-8")
        self.new.write_text(new, encoding="utf-8")
        result = subprocess.run(
            ["bash", str(SCRIPT), "--compare", str(self.old), str(self.new)],
            capture_output=True, text=True,
        )
        self.assertEqual(result.stderr, "")
        return result

    def test_unchanged(self):
        result = self.compare("theorem Example.a 123\n", "theorem Example.a 123\n")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")

    def test_changed_statement(self):
        result = self.compare("theorem Example.a 123\n", "theorem Example.a 456\n")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "statement or definition changed:\n  Example.a\n")

    def test_added_declaration(self):
        result = self.compare("theorem Example.a 123\n",
                              "theorem Example.a 123\ntheorem Example.b 456\n")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")

    def test_removed_declaration(self):
        result = self.compare("theorem Example.a 123\ntheorem Example.b 456\n",
                              "theorem Example.a 123\n")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "removed:\n  Example.b\n")

    def test_empty_new_dump_reports_every_removal(self):
        result = self.compare("theorem Example.a 123\ntheorem Example.b 456\n", "")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "removed:\n  Example.a\n  Example.b\n")

    def test_empty_old_dump_allows_additions(self):
        result = self.compare("", "theorem Example.a 123\n")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")

    def test_both_dumps_empty(self):
        result = self.compare("", "")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
