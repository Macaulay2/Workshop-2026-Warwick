#!/usr/bin/env bash
#
# replay-file-history-via-patches.sh
#
# Transplant a single file F's commit history from repo A into repo B by
# replaying A's per-commit changes as PATCHES onto a fresh branch of B, instead
# of grafting A's history with an unrelated-histories merge.
#
# Why patches (vs. filter-repo + merge):
#   * No disconnected second root commit on B.
#   * No synthetic "unrelated histories" merge commit.
#   * History is replayed LINEARLY: A's merge commits are flattened, each
#     file-touching commit becomes one clean commit carrying only F's change,
#     with the ORIGINAL author, date and message preserved.
#
# Precondition: B's current F must equal A's INITIAL commit of F (shared
# origin). F was copied B->A then evolved in A, so B sits at A's first version.
#
# The script NEVER pushes: it prints the exact push command after building the
# branch locally so you can inspect it first.

set -euo pipefail

# ---- Parameters (override via environment) ----
FILE="${FILE:-gfanInterface.m2}"                                            # path of F in A (repo root)
SRC_DIR="${SRC_DIR:-$(pwd)}"                                                # local checkout of A (this repo)
SRC_BRANCH="${SRC_BRANCH:-Tropical}"                                        # branch of A carrying F's history
DST_URL="${DST_URL:-https://github.com/antonleykin/M2.git}"
DST_BRANCH="${DST_BRANCH:-development}"                                     # base branch in B (sits at A's initial F)
NEW_BRANCH="${NEW_BRANCH:-replay-gfanInterface-history}"                    # fresh branch created in B
DST_PATH="${DST_PATH:-M2/Macaulay2/packages/gfanInterface.m2}"             # where F lives in B

WORK="$(mktemp -d)"
DST="$WORK/dst"
PATCHES="$WORK/patches"
mkdir -p "$PATCHES"
trap 'echo; echo "Working directory left for inspection: $WORK"' EXIT

echo "Replaying history of '$FILE' (A:$SRC_BRANCH) -> '$DST_PATH' (B:$NEW_BRANCH off $DST_BRANCH)"
echo "  A = $SRC_DIR"
echo "  B = $DST_URL"
echo

# ---- 1. Clone B, branch off the base ----
echo "==> Cloning B and creating fresh branch '$NEW_BRANCH' off '$DST_BRANCH'"
git clone --single-branch --branch "$DST_BRANCH" "$DST_URL" "$DST"
git -C "$DST" checkout -b "$NEW_BRANCH"
echo

# ---- 2. Compute A's ordered file-touching commits + reference blobs ----
echo "==> Reading A's history for '$FILE'"
# Portable (bash 3.2 / macOS) array fill; no mapfile.
COMMITS=()
while IFS= read -r _c; do
    COMMITS+=("$_c")
done < <(git -C "$SRC_DIR" log --reverse --format='%H' "$SRC_BRANCH" -- "$FILE")
[ "${#COMMITS[@]}" -gt 0 ] || { echo "ERROR: no commits touch '$FILE' in A." >&2; exit 1; }

A_INIT="${COMMITS[0]}"
A_TIP="${COMMITS[${#COMMITS[@]}-1]}"
A_INIT_BLOB="$(git -C "$SRC_DIR" rev-parse "${A_INIT}:${FILE}")"
A_TIP_BLOB="$(git -C "$SRC_DIR" rev-parse "${A_TIP}:${FILE}")"
echo "    ${#COMMITS[@]} file-touching commits; init=$A_INIT (blob $A_INIT_BLOB) tip=$A_TIP (blob $A_TIP_BLOB)"
echo

# ---- 2a. Precondition: B's F == A's INITIAL blob ----
echo "==> Precondition: B's '$DST_PATH' equals A's initial version of F"
B_BLOB="$(git -C "$DST" rev-parse "HEAD:${DST_PATH}" 2>/dev/null || true)"
if [ -z "$B_BLOB" ]; then
    echo "    ABORT: B has no file at '$DST_PATH' (wrong DST_PATH?)." >&2
    exit 2
fi
if [ "$B_BLOB" = "$A_INIT_BLOB" ]; then
    echo "    OK: B matches A's initial blob ($A_INIT_BLOB). Replaying subsequent commits."
elif [ "$B_BLOB" = "$A_TIP_BLOB" ]; then
    echo "    B already matches A's tip blob; nothing to replay."
    exit 0
else
    # B has diverged from A's initial state: it carries its own commit(s) on F
    # after the shared origin. Linear patch-replay can't handle this — the
    # commits would need to be MERGED into B's evolved F, which this script
    # deliberately does not do (yet).
    echo "    ABORT: B's F has diverged from A's initial version." >&2
    echo "      B blob         : $B_BLOB" >&2
    echo "      A initial blob : $A_INIT_BLOB ($A_INIT)" >&2
    echo "      A tip blob     : $A_TIP_BLOB ($A_TIP)" >&2
    echo "      B appears to have its own commit(s) on F past the shared origin." >&2
    echo "      Replaying A's history would require MERGING into B's evolved F," >&2
    echo "      which this script does not support. Reconcile manually." >&2
    exit 2
fi
echo

# ---- 3. Replay each subsequent commit as a patch ----
# The base commit (COMMITS[0]) is already B's current state, so start at index 1.
# For each commit C we diff F from the PREVIOUS file-state to C, rewrite the
# path to B's DST_PATH, apply it, and commit with C's original metadata.
echo "==> Replaying ${#COMMITS[@]} commits (skipping the base) as patches"
applied=0
prev="${COMMITS[0]}"
for ((i = 1; i < ${#COMMITS[@]}; i++)); do
    cur="${COMMITS[$i]}"
    idx=$(printf '%04d' "$i")

    # Skip no-op steps where F is byte-identical (e.g. a merge that didn't touch F).
    prev_blob="$(git -C "$SRC_DIR" rev-parse "${prev}:${FILE}")"
    cur_blob="$(git -C "$SRC_DIR" rev-parse "${cur}:${FILE}")"
    if [ "$prev_blob" = "$cur_blob" ]; then
        prev="$cur"
        continue
    fi

    patch="$PATCHES/${idx}.patch"
    # Diff only F between consecutive file-states, then relocate the path to B.
    git -C "$SRC_DIR" diff "$prev" "$cur" -- "$FILE" \
        | sed "s#a/${FILE}#a/${DST_PATH}#g; s#b/${FILE}#b/${DST_PATH}#g" \
        > "$patch"

    git -C "$DST" apply --index "$patch"

    # Preserve original author, author date, committer date and message.
    AUTHOR_NAME="$(git -C "$SRC_DIR" log -1 --format='%an' "$cur")"
    AUTHOR_EMAIL="$(git -C "$SRC_DIR" log -1 --format='%ae' "$cur")"
    AUTHOR_DATE="$(git -C "$SRC_DIR" log -1 --format='%aI' "$cur")"
    COMMIT_DATE="$(git -C "$SRC_DIR" log -1 --format='%cI' "$cur")"
    MSG="$(git -C "$SRC_DIR" log -1 --format='%B' "$cur")"

    GIT_COMMITTER_DATE="$COMMIT_DATE" \
    git -C "$DST" commit --quiet \
        --author="$AUTHOR_NAME <$AUTHOR_EMAIL>" \
        --date="$AUTHOR_DATE" \
        -m "$MSG"

    # Assert we reproduced A's exact blob at this commit.
    got="$(git -C "$DST" rev-parse "HEAD:${DST_PATH}")"
    if [ "$got" != "$cur_blob" ]; then
        echo "    ERROR at $cur ($idx): B blob $got != A blob $cur_blob" >&2
        exit 3
    fi
    applied=$((applied + 1))
    prev="$cur"
done
echo "    applied $applied patch commits"
echo

# ---- 4. Final assertion + report ----
FINAL="$(git -C "$DST" rev-parse "HEAD:${DST_PATH}")"
if [ "$FINAL" != "$A_TIP_BLOB" ]; then
    echo "ERROR: final B blob $FINAL != A tip blob $A_TIP_BLOB" >&2
    exit 3
fi
echo "==> SUCCESS: B's '$DST_PATH' now matches A's tip blob ($A_TIP_BLOB)."
echo
echo "New branch '$NEW_BRANCH' built in: $DST"
echo "Inspect:  git -C $DST log --oneline $DST_BRANCH..$NEW_BRANCH"
echo "          git -C $DST log --oneline -- $DST_PATH"
echo
echo "When satisfied, push with:"
echo "  git -C $DST push origin $NEW_BRANCH"
