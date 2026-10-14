#!/usr/bin/env python3
"""Merge a pull request the Referee passed, if it only touches mathematics.

Runs from the default branch, in a job that never checks out pull request code
(see .github/workflows/merge.yml). Correctness is already settled by the time
this runs: the kernel accepted the result. The only question left is whether
this pull request is allowed to change the files it changes.

Usage: GH_TOKEN=... GITHUB_REPOSITORY=owner/repo HEAD_SHA=... merge_policy.py
"""
import json
import os
import sys
import urllib.error
import urllib.request

API = "https://api.github.com"

# Mathematics merges itself. Everything not listed here waits for a person,
# which deliberately includes scripts/, .github/, RULES.md and the pinned
# versions: a pull request able to edit the gate could edit its own gate.
MERGEABLE_DIRS = ("Results/", "Problems/")


def api(path, method="GET", body=None):
    data = json.dumps(body).encode() if body is not None else None
    request = urllib.request.Request(f"{API}{path}", data=data, method=method)
    request.add_header("Authorization", f"Bearer {os.environ['GH_TOKEN']}")
    request.add_header("Accept", "application/vnd.github+json")
    if data:
        request.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(request) as response:
        return json.loads(response.read() or b"null")


# One page of the files endpoint. A pull request bigger than this is held
# rather than half-read: a truncated list could hide a path that must not merge.
MAX_FILES = 100

# One page of open pull requests. Beyond this a pull request simply waits for a
# later Referee run rather than being merged, which is the safe direction.
MAX_OPEN = 100


def path_verdict(paths):
    """Why these paths may not merge themselves, or None if they may."""
    if not paths:
        return "changes no files"
    if len(paths) >= MAX_FILES:
        return f"changes {len(paths)} files, too many to check in one page"
    for path in paths:
        if not path.startswith(MERGEABLE_DIRS):
            return f"touches {path}, which is not mathematics"
    return None


def at_commit(open_prs, head_sha):
    """Open pull requests whose head is exactly this commit.

    Matching by head SHA rather than asking /commits/{sha}/pulls, because that
    endpoint returns nothing when the commit lives in a fork, and forks are
    where contributions come from.
    """
    return [pr for pr in open_prs if pr.get("head", {}).get("sha") == head_sha]


def blocked(pr, head_sha, paths):
    """Why this pull request may not merge itself, or None if it may."""
    if pr["state"] != "open":
        return f"is {pr['state']}"
    if pr.get("draft"):
        return "is a draft"
    if pr["head"]["sha"] != head_sha:
        return "moved on after the Referee ran"
    if pr["base"]["ref"] != "main":
        return f"targets {pr['base']['ref']}"
    if pr.get("mergeable") is False:
        return "conflicts with main"
    if any(label["name"].lower() == "hold" for label in pr.get("labels", [])):
        return "is labelled hold"
    return path_verdict(paths)


def main():
    repo = os.environ["GITHUB_REPOSITORY"]
    head_sha = os.environ["HEAD_SHA"]

    candidates = at_commit(
        api(f"/repos/{repo}/pulls?state=open&per_page={MAX_OPEN}"), head_sha)
    if not candidates:
        print(f"No open pull request at {head_sha[:12]}; nothing to merge.")
        return 0

    for stub in candidates:
        number = stub["number"]
        # The list endpoint omits `mergeable`, so re-read the pull request.
        pr = api(f"/repos/{repo}/pulls/{number}")
        files = api(f"/repos/{repo}/pulls/{number}/files"
                    f"?per_page={MAX_FILES}")
        paths = [f["filename"] for f in files]
        reason = blocked(pr, head_sha, paths)
        if reason:
            print(f"HOLD  #{number}: {reason}")
            continue
        print(f"MERGE #{number}: {pr['title']}")
        try:
            api(f"/repos/{repo}/pulls/{number}/merge", "PUT",
                {"merge_method": "merge"})
            print(f"      merged #{number}")
        except urllib.error.HTTPError as err:
            # Unmergeable or the base moved: the next Referee run retries.
            detail = (err.read() or b"").decode()[:200]
            print(f"      refused: {err.code} {detail}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
