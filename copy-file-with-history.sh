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
DST_BRANCH="${DST_BRANCH:-development}"                                     # existing branch in B to base the work on
NEW_BRANCH="${NEW_BRANCH:-import-gfanInterface-history}"                    # new branch created in B; the merge lands here
DST_PATH="${DST_PATH:-M2/Macaulay2/packages/gfanInterface.m2}"              # where F should land in B

command -v git-filter-repo >/dev/null 2>&1 || {
    echo "ERROR: git-filter-repo not found on PATH." >&2
    echo "Install it (e.g. 'brew install git-filter-repo') and retry." >&2
    exit 1
}

WORK="$(mktemp -d)"
trap 'echo; echo "Working directory left in place for inspection: $WORK"' EXIT
echo "Working in $WORK"
echo "Copying '$FILE' (branch $SRC_BRANCH of A)  ->  '$DST_PATH' (new branch $NEW_BRANCH of B, based on $DST_BRANCH)"
echo

# ---- 1. Fresh clone of A, filter to just F, rename to B's path ----
echo "==> Cloning A and filtering to '$FILE'"
# --single-branch avoids fetching sibling refs that may collide on a
# case-insensitive filesystem (e.g. both 'Tropical' and 'TROPICAL' exist),
# which would otherwise break git-filter-repo's ref rewriting.
git clone --single-branch --branch "$SRC_BRANCH" "$SRC_URL" "$WORK/src"
# git-filter-repo wants a fresh clone; --force acknowledges we made it ourselves.
# --path keeps only F; --path-rename rewrites every commit so F lives at DST_PATH.
git -C "$WORK/src" filter-repo \
    --path "$FILE" \
    --path-rename "$FILE:$DST_PATH" \
    --force
echo "    filtered history now contains only '$DST_PATH'"
echo

# ---- 2. Clone B and branch off for the import ----
echo "==> Cloning B and creating new branch '$NEW_BRANCH' off '$DST_BRANCH'"
git clone --single-branch --branch "$DST_BRANCH" "$DST_URL" "$WORK/dst"
# Do the import on a NEW branch so B's existing branch is never modified;
# the result is reviewed/PR'd from $NEW_BRANCH.
git -C "$WORK/dst" checkout -b "$NEW_BRANCH"
echo

# ---- 2a. PRECONDITION CHECK: B must sit at A's INITIAL version of F ----
# The workflow is "F was copied from B into A, then evolved in A". So B's
# current content should equal A's *first* commit of F (the shared origin),
# NOT A's tip (A is intentionally ahead). We verify common origin, then the
# merge advances B to A's tip carrying all intermediate history.
echo "==> Precondition check: B is at A's initial version of F"
SRC_INITIAL_COMMIT="$(git -C "$WORK/src" log --reverse --format='%H' -- "$DST_PATH" | head -1)"
SRC_INITIAL_BLOB="$(git -C "$WORK/src" rev-parse "$SRC_INITIAL_COMMIT:$DST_PATH")"
SRC_TIP_BLOB="$(git -C "$WORK/src" rev-parse "HEAD:$DST_PATH")"
if DST_BLOB="$(git -C "$WORK/dst" rev-parse "HEAD:$DST_PATH" 2>/dev/null)"; then
    if [ "$DST_BLOB" = "$SRC_INITIAL_BLOB" ]; then
        echo "    OK: B matches A's initial commit of F ($SRC_INITIAL_COMMIT, blob $SRC_INITIAL_BLOB)."
        echo "        A has since evolved F; the merge will advance B to A's tip."
    elif [ "$DST_BLOB" = "$SRC_TIP_BLOB" ]; then
        echo "    OK: B already matches A's tip version of F (blob $SRC_TIP_BLOB); nothing new to import."
    else
        echo "    ABORT: B's F is neither A's initial nor A's tip version." >&2
        echo "      B blob         : $DST_BLOB" >&2
        echo "      A initial blob : $SRC_INITIAL_BLOB ($SRC_INITIAL_COMMIT)" >&2
        echo "      A tip blob     : $SRC_TIP_BLOB" >&2
        echo "      B has diverged from the shared origin; reconcile manually." >&2
        echo "      inspect: git -C $WORK/dst diff $DST_BLOB $SRC_INITIAL_BLOB" >&2
        exit 2   # refuse to proceed; the user resolves the divergence deliberately
    fi
elif [ "${ALLOW_FRESH_IMPORT:-0}" = "1" ]; then
    echo "    note: B has no '$DST_PATH' yet; ALLOW_FRESH_IMPORT=1, importing fresh."
else
    # A missing file is usually a wrong DST_PATH, not a genuine fresh import.
    # Refuse by default so a typo can't masquerade as "nothing to compare".
    echo "    ABORT: B has no file at '$DST_PATH'." >&2
    echo "      This usually means DST_PATH is wrong. Existing gfanInterface.m2 paths in B:" >&2
    git -C "$WORK/dst" ls-tree -r --name-only "$DST_BRANCH" \
        | grep -i "$(basename "$FILE")" | sed 's/^/        /' >&2 \
        || echo "        (none found)" >&2
    echo "      If a genuinely fresh import is intended, re-run with ALLOW_FRESH_IMPORT=1." >&2
    exit 2
fi
echo

# ---- 2b. Pull in the filtered history and merge (unrelated histories) ----
# Both sides "add" F (B at the shared origin, A at its evolved tip), so the
# merge conflicts on content. The precondition proved B is A's ancestor, so
# A's version must win: -X theirs auto-resolves every conflict to the incoming
# (filtered A) side.  Note: -X theirs only affects F here, since F is the only
# path the two histories share.
echo "==> Merging filtered history into '$NEW_BRANCH' (A's version wins on conflict)"
git -C "$WORK/dst" remote add filtered "$WORK/src"
git -C "$WORK/dst" fetch filtered "$SRC_BRANCH"
if ! git -C "$WORK/dst" merge --allow-unrelated-histories --no-edit \
        -X theirs \
        -m "Import $FILE with history from Workshop-2026-Warwick" \
        "filtered/$SRC_BRANCH"; then
    echo >&2
    echo "    Merge failed unexpectedly. Inspect: git -C $WORK/dst status" >&2
    exit 3
fi

# Safety: after the merge, B's F must exactly equal A's tip version.
POST_BLOB="$(git -C "$WORK/dst" rev-parse "HEAD:$DST_PATH")"
if [ "$POST_BLOB" != "$SRC_TIP_BLOB" ]; then
    echo "    ABORT: after merge, F does not match A's tip." >&2
    echo "      merged blob: $POST_BLOB   A tip blob: $SRC_TIP_BLOB" >&2
    exit 4
fi
echo "    OK: merged F matches A's tip (blob $SRC_TIP_BLOB)."
echo

# ---- 3. Report; leave the push to the user ----
echo "==> Done. Imported history onto new branch '$NEW_BRANCH' in $WORK/dst."
echo "    ('$DST_BRANCH' in B was used only as the base and is left unmodified.)"
echo
echo "Inspect the imported history:"
echo "  git -C $WORK/dst log --oneline -- $DST_PATH"
echo "  git -C $WORK/dst log --follow --format='%an %ad %s' -- $DST_PATH | tail"
echo
echo "When satisfied, push the NEW branch to B with:"
echo "  git -C $WORK/dst push -u origin $NEW_BRANCH"
