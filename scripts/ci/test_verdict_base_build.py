"""How verdict.py reports a build of main that times out or fails."""

from pathlib import Path
import importlib.util
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("verdict", Path(__file__).resolve().parent / "verdict.py")
verdict = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verdict)


class BaseBuildTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.check = verdict.Check(temp.name, "0" * 40, "1" * 40)
        lint = mock.patch.object(verdict, "run", return_value=mock.Mock(returncode=0, stdout=""))
        lint.start()
        self.addCleanup(lint.stop)

    def stop_reasons(self, build_status):
        with mock.patch.object(self.check, "build", return_value=(build_status, "log")):
            with self.assertRaises(verdict.Stop) as stopped:
                self.check.base_state(None)
        self.assertEqual(stopped.exception.verdict, "error")
        return " ".join(stopped.exception.reasons)

    def test_timeout_is_not_reported_as_a_broken_main(self):
        reasons = self.stop_reasons(None)
        self.assertIn(f"did not finish in {verdict.BUILD_MINUTES} minutes", reasons)
        self.assertNotIn("does not build", reasons)

    def test_failed_build_is_still_reported_as_one(self):
        self.assertIn("main itself does not build", self.stop_reasons(1))


if __name__ == "__main__":
    unittest.main()
