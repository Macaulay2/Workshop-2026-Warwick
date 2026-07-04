# History Transplant: repo A → repo B

Status: **paused** ("we'll come back to this"). This summarizes the `copy-file-with-history.sh` work for a fresh agent.

## Goal
Copy **`gfanInterface.m2`** with its full commit history from repo **A** into repo **B**, without bringing any other files, using `git-filter-repo`.

- **A** = `Macaulay2/Workshop-2026-Warwick`, branch `Tropical`, file at **repo root**: `gfanInterface.m2`
- **B** = `antonleykin/M2` (an M2 fork), file belongs at **`M2/Macaulay2/packages/gfanInterface.m2`**
- Prereq: `git-filter-repo` installed (`/opt/homebrew/bin/git-filter-repo`)

## The script: `copy-file-with-history.sh`
Lives at repo root. Parameterized via env vars (`FILE`, `SRC_URL`, `SRC_BRANCH`, `DST_URL`, `DST_BRANCH`, `NEW_BRANCH`, `DST_PATH`, `ALLOW_FRESH_IMPORT`). Works in a throwaway `mktemp -d` dir and **never pushes automatically** — it prints the push command.

Flow:
1. Fresh clone A (`--single-branch`); `git filter-repo --path FILE --path-rename FILE:DST_PATH` → history reduced to only F, relocated to B's path.
2. Clone B; create a **new branch** (`NEW_BRANCH`) off `DST_BRANCH`.
3. **Precondition**: verify B's F equals A's *initial* commit of F (shared origin). F was copied B→A then evolved in A, so B must match A's FIRST commit, not A's tip. Handles already-at-tip and diverged cases distinctly.
4. Merge filtered A history: `--allow-unrelated-histories -X theirs` (A wins conflicts), then assert merged F == A's tip blob.
5. Print inspection + manual push commands.

## Current defaults
- `DST_BRANCH=development` (a clean pre-import base on B, was at `f10ddee`)
- `NEW_BRANCH=import-gfanInterface-history`
- `DST_PATH=M2/Macaulay2/packages/gfanInterface.m2`

## Gotchas already fixed (don't re-hit these)
- **`Tropical` vs `TROPICAL`** both exist on A → ref collision on macOS case-insensitive FS breaks filter-repo. Fixed with `--single-branch --branch` on both clones.
- **Path**: B uses `M2/Macaulay2/...`, not `Macaulay2/...`. Script aborts if F absent in B (likely wrong path) unless `ALLOW_FRESH_IMPORT=1`.
- **Precondition** must compare B to A's *initial* commit, not tip. Confirmed B's blob `3d9d586` == A's first commit `357eba4 "Add files via upload"`.
- Merge conflicts on F resolved via `-X theirs` + post-merge blob assertion.

## Two "unexpected commits" on B — expected, not bugs
Inherent to a with-history unrelated-repo merge:
- **A's root commit** (`357eba4`) grafts a disconnected second root → GitHub shows "doesn't belong to this branch".
- **The synthetic merge commit** created by `git merge` (not present in A).
Avoiding them would require squashing A into one commit, losing per-commit history.

## What has been pushed / committed
- **Pushed to B**: branch `import-gfanInterface-history` (tip `683d259`), based on `development`, carrying A's ~37-commit history. B's other branches untouched.
- **Earlier stray push**: import once landed on B's `gfanInterface` branch (`882c7ed`), but that branch has since moved to `70510e2` (changed outside this work).
- **Script commits** on local `Tropical` branch (`36ac70c`, `37ef3ae`, `171cd8c`, plus earlier) — **NOT pushed** to the Workshop repo.

## Open / possible next steps
- Decide final home in B (PR `import-gfanInterface-history` into a mainline branch?).
- Optionally reconcile/clean the stray `gfanInterface` branch state on B.
- Push the script commits to the Workshop repo if desired.
