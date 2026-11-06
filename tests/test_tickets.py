import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "tickets", Path(__file__).resolve().parents[1] / "scripts/tickets.py"
)
tickets = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(tickets)


# [utest->req~github-tracking~1]
class TicketTests(unittest.TestCase):
    def test_public_issue_creation_never_accesses_private_project(self):
        with (
            tempfile.NamedTemporaryFile() as body,
            patch.object(tickets, "gh", return_value="https://github.com/kbak/clafer-semantics/issues/7") as gh,
            patch.object(tickets, "track") as tracking,
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            tickets.main(["create", "--title", "Public contribution",
                          "--body-file", body.name, "--no-project"])
        tracking.assert_not_called()
        self.assertEqual(gh.call_count, 1)
        self.assertEqual(gh.call_args.args[:2], ("issue", "create"))
        self.assertIn("https://github.com/kbak/clafer-semantics/issues/7", output.getvalue())

    def test_public_issue_close_never_accesses_private_project(self):
        with (
            patch.object(tickets, "gh", return_value="closed") as gh,
            patch.object(tickets, "track") as tracking,
            contextlib.redirect_stdout(io.StringIO()),
        ):
            tickets.main(["close", "7", "--no-project"])
        tracking.assert_not_called()
        self.assertEqual(gh.call_args.args[:3], ("issue", "close", 7))

    def test_public_issue_failure_is_not_hidden(self):
        with (
            tempfile.NamedTemporaryFile() as body,
            patch.object(tickets, "gh", side_effect=subprocess.CalledProcessError(1, ["gh"])),
            patch.object(tickets, "track") as tracking,
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                tickets.main(["create", "--title", "Public contribution",
                              "--body-file", body.name, "--no-project"])
        tracking.assert_not_called()

    def test_track_uses_live_field_and_option_ids(self):
        for status, display in (("todo", "Todo"), ("ready", "Ready"),
                                ("in-progress", "In Progress"), ("done", "Done")):
            with (
                self.subTest(status=status),
                patch.object(
                    tickets,
                    "gh",
                    side_effect=[
                        {"url": "https://github.com/kbak/clafer-semantics/issues/7"},
                        {"id": "ITEM"},
                        {"fields": [{
                            "id": "FIELD", "name": "Status",
                            "options": [{"id": "WRONG", "name": "Unrelated"},
                                        {"id": "OPTION", "name": display}],
                        }]},
                        "",
                    ],
                ) as gh,
                contextlib.redirect_stdout(io.StringIO()) as output,
            ):
                tickets.main(["track", "7", "--status", status])
            self.assertIn("--single-select-option-id", gh.call_args.args)
            self.assertEqual(gh.call_args.args[-1], "OPTION")
            self.assertEqual(gh.call_args.args[3], "ITEM")
            self.assertIn(display, output.getvalue())

    def test_ready_requires_an_existing_project_option(self):
        with patch.object(tickets, "gh", side_effect=[
            {"url": "url"}, {"id": "ITEM"},
            {"fields": [{"id": "FIELD", "name": "Status",
                         "options": [{"id": "TODO", "name": "Todo"}]}]},
        ]) as gh:
            with self.assertRaises(StopIteration):
                tickets.main(["track", "7", "--status", "ready"])
        self.assertEqual(gh.call_count, 3)  # Never silently fall back to Todo.

    def test_creation_retains_url_when_project_fails(self):
        output = io.StringIO()
        failure = subprocess.CalledProcessError(
            1, ["gh"], stderr="Project access denied"
        )
        with (
            tempfile.NamedTemporaryFile() as body,
            patch.object(
                tickets,
                "gh",
                return_value="https://github.com/kbak/clafer-semantics/issues/7",
            ) as gh,
            patch.object(tickets, "track", side_effect=failure),
            contextlib.redirect_stdout(output),
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                tickets.main(
                    [
                        "create",
                        "--title",
                        "a `literal` $(title)",
                        "--body-file",
                        body.name,
                    ]
                )
        self.assertIn("tickets.py track 7", output.getvalue())
        self.assertEqual(gh.call_count, 1)
        self.assertIn("a `literal` $(title)", gh.call_args.args)

    def test_failed_close_does_not_mark_done(self):
        with (
            patch.object(
                tickets, "gh", side_effect=subprocess.CalledProcessError(1, ["gh"])
            ),
            patch.object(tickets, "track") as tracking,
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                tickets.main(["close", "7"])
        tracking.assert_not_called()

    def test_edit_keeps_body_file_as_argument(self):
        with (
            tempfile.NamedTemporaryFile() as body,
            patch.object(tickets, "gh", return_value="updated") as gh,
            contextlib.redirect_stdout(io.StringIO()),
        ):
            tickets.main(
                ["edit", "7", "--body-file", body.name, "--add-label", "semantics"]
            )
        self.assertIn(Path(body.name), gh.call_args.args)
        self.assertIn("semantics", gh.call_args.args)

    def test_missing_status_is_a_failure(self):
        with patch.object(
            tickets, "gh", side_effect=[{"url": "url"}, {"id": "ITEM"}, {"fields": []}]
        ):
            with self.assertRaises(StopIteration):
                tickets.track(7, "todo")

    def test_gh_failure_propagates(self):
        with patch.object(
            tickets.subprocess,
            "run",
            side_effect=subprocess.CalledProcessError(1, ["gh"]),
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                tickets.gh("issue", "list")


if __name__ == "__main__":
    unittest.main()
