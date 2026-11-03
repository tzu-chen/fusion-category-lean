# Pushing to the connected GitHub repository

There is no credential helper in this workspace, so **shell `git push` cannot work**:

```
$ git push omm main
fatal: could not read Username for 'https://github.com': terminal prompts disabled
```

Push goes through the platform connector instead:

1. Refresh the tracking ref: `github_fetch` (branch `main`).
2. `github_push` with `branch: "main"` and `commit:` the **full 40-character SHA**
   (`git rev-parse HEAD`). A truncated SHA is rejected as `branch_moved`, which
   reads like a moved branch but is the same "need a full commit id" refusal.
3. Verify against the remote itself: `git ls-remote omm refs/heads/main`.

## Do not trust `github_status` for remote state

`github_status` has reported `branches.main.oid` equal to the **local** `HEAD`
while the remote was several commits behind. It is not evidence that a push
landed. `git ls-remote omm` is the authoritative check.

## Workflow files cannot be pushed through the connector

GitHub refuses to let an App create or update files under `.github/workflows/`
without a `workflows` permission, and this platform's connection does not hold
it. A push containing a workflow file is rejected with:

```
! <sha>:refs/heads/main [remote rejected] (refusing to allow a GitHub App
  to create or update workflow `.github/workflows/<f>` without `workflows` permission)
```

So a workflow file stays untracked in the working tree and must be committed by
a person (GitHub web editor, or a push with credentials that carry workflow
scope). The batch-B2 CI file
(`.github/workflows/fusion-category-ci.yml`, 167 lines, complete and
self-contained) is in this state: keep it in the working tree, and when
landing it, commit it separately from everything else so the rest of the work
can still be pushed.

## If a push is genuinely rejected

A "cannot push" is often a stale local tracking ref, not a diverged remote:
compare `git rev-parse HEAD` with `git ls-remote omm refs/heads/main`, then
`github_fetch` and rebase onto `omm/main` if the remote really moved.
