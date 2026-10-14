#!/usr/bin/env python3
"""Tests for the merge gate. CI runs them on every pull request, because this
is the code that decides who may write to the repository."""
import unittest

from merge_policy import MAX_FILES, at_commit, blocked, path_verdict


class PathVerdict(unittest.TestCase):
    def test_mathematics_merges(self):
        self.assertIsNone(path_verdict(["Results/Ramsey.lean"]))
        self.assertIsNone(path_verdict(["Problems/Collatz.lean"]))

    def test_everything_else_waits(self):
        for path in (".github/workflows/merge.yml", "scripts/merge_policy.py",
                     "scripts/CheckAxioms.lean", "RULES.md", "README.md",
                     "lakefile.toml", "lean-toolchain", "lake-manifest.json",
                     "LICENSE", ".gitignore"):
            self.assertIsNotNone(path_verdict([path]), path)

    def test_one_bad_path_blocks_everything(self):
        self.assertIsNotNone(
            path_verdict(["Results/Fine.lean", "scripts/merge_policy.py"]))

    def test_prefix_is_not_substring(self):
        self.assertIsNotNone(path_verdict(["Results_evil/x.lean"]))

    def test_empty_is_not_mergeable(self):
        self.assertIsNotNone(path_verdict([]))

    def test_too_many_files_is_held_not_half_read(self):
        self.assertIsNotNone(
            path_verdict([f"Results/R{i}.lean" for i in range(MAX_FILES)]))


def pull_request(**overrides):
    """A pull request the gate would merge, unless a test spoils it."""
    pr = {"state": "open", "draft": False, "head": {"sha": "abc"},
          "base": {"ref": "main"}, "mergeable": True, "labels": []}
    pr.update(overrides)
    return pr


MATHS = ["Results/Ramsey.lean"]


def verdict(**overrides):
    return blocked(pull_request(**overrides), "abc", MATHS)


class Blocked(unittest.TestCase):
    def test_merges_a_clean_pull_request(self):
        self.assertIsNone(verdict())

    def test_holds_a_moved_head(self):
        # Green on an old commit must never merge a newer one.
        self.assertIsNotNone(blocked(pull_request(), "def", MATHS))

    def test_holds_drafts_and_closed(self):
        self.assertIsNotNone(verdict(draft=True))
        self.assertIsNotNone(verdict(state="closed"))

    def test_holds_other_base_branches(self):
        self.assertIsNotNone(verdict(base={"ref": "release"}))

    def test_holds_conflicts_and_hold_label(self):
        self.assertIsNotNone(verdict(mergeable=False))
        self.assertIsNotNone(verdict(labels=[{"name": "Hold"}]))

    def test_holds_non_mathematics_when_all_else_is_fine(self):
        self.assertIsNotNone(
            blocked(pull_request(), "abc", ["scripts/merge_policy.py"]))

    def test_unknown_mergeable_state_still_merges(self):
        # GitHub computes `mergeable` asynchronously; None must not block.
        self.assertIsNone(verdict(mergeable=None))


class AtCommit(unittest.TestCase):
    FORK = {"number": 1, "head": {"sha": "abc", "repo": {"fork": True}}}
    OTHER = {"number": 2, "head": {"sha": "zzz"}}

    def test_finds_a_fork_pull_request_by_head_sha(self):
        # The reason this exists: /commits/{sha}/pulls returns [] for a commit
        # that lives in a fork, which silently skipped the first real PR.
        self.assertEqual(at_commit([self.FORK, self.OTHER], "abc"), [self.FORK])

    def test_ignores_other_commits(self):
        self.assertEqual(at_commit([self.OTHER], "abc"), [])

    def test_empty_list(self):
        self.assertEqual(at_commit([], "abc"), [])

    def test_tolerates_missing_head(self):
        self.assertEqual(at_commit([{"number": 3}], "abc"), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
