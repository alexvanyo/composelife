#!/usr/bin/env bash
#
# Copyright 2026 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

set -euo pipefail

BASE_REF="${1:-HEAD}"
MODULE="${2:-}"
echo "Comparing screenshots against base ref: $BASE_REF (module: ${MODULE:-all})"

WORKTREE_DIR=".gradle/compare-base-worktree"
rm -rf "$WORKTREE_DIR"
git worktree prune 2>/dev/null || true

cleanup() {
    echo "Cleaning up temporary worktree and local snapshot images..."
    git worktree remove --force "$WORKTREE_DIR" 2>/dev/null || rm -rf "$WORKTREE_DIR"
    git worktree prune 2>/dev/null || true
    find . -name "*.png" -path "*/snapshots/*" -delete 2>/dev/null || true
}
trap cleanup EXIT

echo "Creating temporary git worktree at $WORKTREE_DIR for $BASE_REF..."
git worktree add --detach "$WORKTREE_DIR" "$BASE_REF"

RECORD_TASK="recordRoborazzi"
COMPARE_TASK="compareRoborazzi"
if [ -n "$MODULE" ]; then
    RECORD_TASK=":$MODULE:recordRoborazzi"
    COMPARE_TASK=":$MODULE:compareRoborazzi"
fi

echo "Recording baseline screenshots on $BASE_REF using $RECORD_TASK..."
(cd "$WORKTREE_DIR" && ./gradlew "$RECORD_TASK")

echo "Copying baseline images to local workspace..."
python3 -c '
import os, shutil
src_root = ".gradle/compare-base-worktree"
for root, dirs, files in os.walk(src_root):
    if "snapshots" in root:
        rel_dir = os.path.relpath(root, src_root)
        os.makedirs(rel_dir, exist_ok=True)
        for f in files:
            if f.endswith(".png"):
                shutil.copy2(os.path.join(root, f), os.path.join(rel_dir, f))
'

echo "Running $COMPARE_TASK on current workspace..."
./gradlew "$COMPARE_TASK" || true

echo "Comparison complete! Check build/outputs/roborazzi/ directories for visual diffs and reports."
