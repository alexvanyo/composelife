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

PREFIX="${HOME}/.lean-custom"
REPO="https://github.com/alexvanyo/lean4.git"
REF="av/jvm"
FORCE=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --prefix)
      PREFIX="$2"
      shift 2
      ;;
    --repo)
      REPO="$2"
      shift 2
      ;;
    --ref)
      REF="$2"
      shift 2
      ;;
    --force)
      FORCE=true
      shift
      ;;
    -h|--help)
      echo "Usage: $0 [--prefix <dir>] [--repo <url>] [--ref <branch-or-commit>] [--force]"
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      exit 1
      ;;
  esac
done

PREFIX="${PREFIX/#\~/$HOME}"

# Resolve the commit SHA of the target ref
TARGET_SHA=""
if [[ "$REF" =~ ^[0-9a-f]{40}$ ]]; then
  TARGET_SHA="$REF"
else
  TARGET_SHA=$(git ls-remote "$REPO" "refs/heads/$REF" | awk '{print $1}')
  if [[ -z "$TARGET_SHA" ]]; then
    TARGET_SHA=$(git ls-remote "$REPO" "$REF" | head -n1 | awk '{print $1}')
  fi
fi

if [[ -z "$TARGET_SHA" ]]; then
  echo "Error: Could not resolve git SHA for ref '$REF' from $REPO" >&2
  exit 1
fi

COMMIT_FILE="${PREFIX}/.lean-commit"
LEAN_BIN="${PREFIX}/bin/lean"

if [[ "$FORCE" = false && -x "$LEAN_BIN" && -f "$COMMIT_FILE" ]]; then
  CURRENT_SHA=$(cat "$COMMIT_FILE" 2>/dev/null || true)
  if [[ "$CURRENT_SHA" == "$TARGET_SHA" ]]; then
    echo "Custom Lean binary at $LEAN_BIN is already up to date ($TARGET_SHA)."
    exit 0
  fi
fi

echo "Building custom Lean compiler ($REF @ $TARGET_SHA) into $PREFIX..."

command -v cmake >/dev/null 2>&1 || { echo "Error: cmake is required but not installed." >&2; exit 1; }
command -v make >/dev/null 2>&1 || { echo "Error: make is required but not installed." >&2; exit 1; }
command -v git >/dev/null 2>&1 || { echo "Error: git is required but not installed." >&2; exit 1; }

TEMP_DIR=$(mktemp -d)
cleanup() {
  rm -rf "$TEMP_DIR"
}
trap cleanup EXIT

echo "Fetching $REPO ($REF @ $TARGET_SHA)..."
mkdir -p "$TEMP_DIR/lean4"
(
  cd "$TEMP_DIR/lean4"
  git init -q
  git remote add origin "$REPO"
  if ! git fetch --depth 1 origin "$TARGET_SHA" 2>/dev/null; then
    git fetch --depth 1 origin "$REF"
  fi
  git checkout -q --detach FETCH_HEAD
)

cd "$TEMP_DIR/lean4"
ACTUAL_SHA=$(git rev-parse HEAD)

echo "Configuring Lean CMake preset 'release' with install prefix $PREFIX..."
cmake --preset release -DCMAKE_INSTALL_PREFIX="$PREFIX" -DSTRIP_BINARIES=ON

NPROC=$(nproc 2>/dev/null || sysctl -n hw.logicalcpu 2>/dev/null || echo 2)
echo "Building Lean stage1 using $NPROC worker threads..."
make -C build/release stage1 -j"$NPROC"

echo "Installing stage1 to $PREFIX..."
mkdir -p "$PREFIX"
cmake --install build/release/stage1 --prefix "$PREFIX"

echo "Stripping remaining debug symbols to reduce cache footprint..."
find "$PREFIX" -type f \( -name "*.so*" -o -name "*.a" -o -perm /111 \) -exec strip -g {} + 2>/dev/null || true

echo "$ACTUAL_SHA" > "$COMMIT_FILE"

if command -v elan >/dev/null 2>&1; then
  echo "Registering custom-lean toolchain with elan..."
  elan toolchain uninstall custom-lean 2>/dev/null || true
  elan toolchain link custom-lean "$PREFIX"
fi

echo "Successfully built custom Lean compiler at $LEAN_BIN ($ACTUAL_SHA)."
