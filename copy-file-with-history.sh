#!/usr/bin/env bash
#
# copy-file-with-history.sh
#
# Transplant a single file F, together with its full commit history, from a
# remote repo A into a remote repo B using git-filter-repo. Only F's history is
# copied; no other files from A are brought along. The file may be relocated to
# a different path in B via DST_PATH.
#
# The two histories are unrelated (no common ancestor), so the import is a merge
# with --allow-unrelated-histories. The script NEVER pushes: it prints the exact
# push command for you to run after inspecting the result.
#
# Usage:
#   ./copy-file-with-history.sh
#     runs with the guinea-pig defaults below; or override via environment:
#   FILE=path/in/A DST_PATH=path/in/B SRC_URL=... SRC_BRANCH=... \
#   DST_URL=... DST_BRANCH=... ./copy-file-with-history.sh

set -euo pipefail

# ---- Parameters (guinea-pig defaults; override via environment) ----
FILE="${FILE:-gfanInterface.m2}"                                            # path of F in A
SRC_URL="${SRC_URL:-https://github.com/Macaulay2/Workshop-2026-Warwick.git}"
SRC_BRANCH="${SRC_BRANCH:-Tropical}"
DST_URL="${DST_URL:-https://github.com/antonleykin/M2.git}"
DST_BRANCH="${DST_BRANCH:-gfanInterface}"
DST_PATH="${DST_PATH:-Macaulay2/packages/gfanInterface.m2}"                 # where F should land in B

command -v git-filter-repo >/dev/null 2>&1 || {
    echo "ERROR: git-filter-repo not found on PATH." >&2
    echo "Install it (e.g. 'brew install git-filter-repo') and retry." >&2
    exit 1
}

WORK="$(mktemp -d)"
trap 'echo; echo "Working directory left in place for inspection: $WORK"' EXIT
echo "Working in $WORK"
echo "Copying '$FILE' (branch $SRC_BRANCH of A)  ->  '$DST_PATH' (branch $DST_BRANCH of B)"
echo

# ---- 1. Fresh clone of A, filter to just F, rename to B's path ----
echo "==> Cloning A and filtering to '$FILE'"
git clone "$SRC_URL" "$WORK/src"
git -C "$WORK/src" checkout "$SRC_BRANCH"
# git-filter-repo wants a fresh clone; --force acknowledges we made it ourselves.
# --path keeps only F; --path-rename rewrites every commit so F lives at DST_PATH.
git -C "$WORK/src" filter-repo \
    --path "$FILE" \
    --path-rename "$FILE:$DST_PATH" \
    --force
echo "    filtered history now contains only '$DST_PATH'"
echo

# ---- 2. Clone B ----
echo "==> Cloning B"
git clone "$DST_URL" "$WORK/dst"
git -C "$WORK/dst" checkout "$DST_BRANCH"
echo

# ---- 2a. PRECONDITION CHECK: F on A must match F on B (if B already has it) ----
echo "==> Precondition check: F on A vs F on B"
SRC_BLOB="$(git -C "$WORK/src" rev-parse "HEAD:$DST_PATH")"
if DST_BLOB="$(git -C "$WORK/dst" rev-parse "HEAD:$DST_PATH" 2>/dev/null)"; then
    if [ "$SRC_BLOB" = "$DST_BLOB" ]; then
        echo "    OK: F is byte-identical in A and B (blob $SRC_BLOB)."
    else
        echo "    ABORT: '$DST_PATH' exists in B but differs from A's version." >&2
        echo "      A blob: $SRC_BLOB" >&2
        echo "      B blob: $DST_BLOB" >&2
        echo "      inspect: git -C $WORK/dst diff $DST_BLOB $SRC_BLOB" >&2
        exit 2   # refuse to proceed; the user resolves the divergence deliberately
    fi
else
    echo "    note: B has no '$DST_PATH' yet; nothing to compare, importing fresh."
fi
echo

# ---- 2b. Pull in the filtered history and merge (unrelated histories) ----
echo "==> Merging filtered history into B"
git -C "$WORK/dst" remote add filtered "$WORK/src"
git -C "$WORK/dst" fetch filtered "$SRC_BRANCH"
if ! git -C "$WORK/dst" merge --allow-unrelated-histories --no-edit \
        -m "Import $FILE with history from Workshop-2026-Warwick" \
        "filtered/$SRC_BRANCH"; then
    echo >&2
    echo "    Merge stopped with conflicts (B already tracks '$DST_PATH')." >&2
    echo "    To accept A's incoming version, run:" >&2
    echo "      git -C $WORK/dst checkout --theirs $DST_PATH" >&2
    echo "      git -C $WORK/dst add $DST_PATH" >&2
    echo "      git -C $WORK/dst commit --no-edit" >&2
    echo "    Then re-run the inspection/push steps printed above." >&2
    exit 3
fi
echo

# ---- 3. Report; leave the push to the user ----
echo "==> Done. Merged into $WORK/dst on branch $DST_BRANCH."
echo
echo "Inspect the imported history:"
echo "  git -C $WORK/dst log --oneline -- $DST_PATH"
echo "  git -C $WORK/dst log --follow --format='%an %ad %s' -- $DST_PATH | tail"
echo
echo "When satisfied, push to B with:"
echo "  git -C $WORK/dst push origin $DST_BRANCH"
