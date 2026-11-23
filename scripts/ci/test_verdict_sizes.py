"""A pull request fails when it adds a type synonym of at least LARGE_SYNONYM nodes as a tree, or
makes one larger than on main; synonyms already that large on main do not hold it up."""
import json
import tempfile
import types
import unittest
from pathlib import Path

import verdict
from verdict import LARGE_SYNONYM, grown_synonyms, parse_sizes

BIG = LARGE_SYNONYM


class SynonymSizesTest(unittest.TestCase):
    def test_parse(self):
        text = ("RiemannMasullo.A\tRiemannMasullo.Ch01.Sec1\t300000000\t2000\t0\t5\tSubtype\n"
                "RiemannMasullo.B\tRiemannMasullo.Ch01.Sec2\t100000000\t900\t0\t0\tHasQuotient.Quotient\n"
                "\n"
                "not a line of the script\n")
        self.assertEqual(parse_sizes(text), {"RiemannMasullo.A": 300000000, "RiemannMasullo.B": 100000000})

    def test_new_synonym_fails(self):
        self.assertEqual(grown_synonyms({}, {"X": BIG}), ["X"])

    def test_existing_synonym_of_the_same_size_passes(self):
        self.assertEqual(grown_synonyms({"X": 3 * BIG}, {"X": 3 * BIG}), [])

    def test_existing_synonym_that_grows_fails(self):
        self.assertEqual(grown_synonyms({"X": 3 * BIG}, {"X": 4 * BIG}), ["X"])

    def test_synonym_that_shrinks_passes(self):
        self.assertEqual(grown_synonyms({"X": 3 * BIG}, {"X": 2 * BIG}), [])

    def test_synonym_that_crosses_the_threshold_fails(self):
        # main lists only synonyms above the threshold, so one below it is absent from `base`
        self.assertEqual(grown_synonyms({}, {"Y": BIG + 1, "X": 2 * BIG}), ["X", "Y"])


class NotesTest(unittest.TestCase):
    """A measurement that could not run is reported without changing the verdict."""
    def test_note_is_shown_and_verdict_kept(self):
        verdict.NOTES[:] = ["the size of type synonyms could not be measured"]
        try:
            with tempfile.TemporaryDirectory() as out:
                args = types.SimpleNamespace(out=out, pr=1, head="a" * 40, base="b" * 40)
                verdict.report(args, "merge", [], "")
                data = json.loads((Path(out) / "verdict.json").read_text())
                self.assertEqual(data["verdict"], "merge")
                self.assertEqual(data["notes"], ["the size of type synonyms could not be measured"])
                self.assertIn("could not be measured", (Path(out) / "summary.md").read_text())
        finally:
            verdict.NOTES.clear()


if __name__ == "__main__":
    unittest.main()
