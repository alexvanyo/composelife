#!/usr/bin/env python3
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
"""Replaces every `bv_decide?` in Lean files with `bv_check` of a stored LRAT certificate.

`bv_decide?` runs the SAT solver and writes the LRAT proof it finds next to the Lean file, as
`<File>.lean-<declaration>-<line>-<column>.lrat`. This script elaborates each file, moves those certificates to
`lrat/<File>.<full declaration name>[-<n>].lrat` beside it, and rewrites each `bv_decide?` to the `bv_check` that reads its
certificate, so later builds check the stored proof instead of running the solver.

Usage (from the repository root, after `lake build` of the files' dependencies):

    script/lean-bv-check.py algorithm/lean proofs/PopcountProofs.lean [more files...]

Rerun it after changing a goal proved by `bv_check`: put `bv_decide?` back in place of that `bv_check` first.
"""

import argparse
import collections
import os
import re
import subprocess
import sys

SUGGESTION = re.compile(r'bv_check(?: \(config := \{[^}]*\}\))? "(?P<file>[^"]+-(?P<decl>[^"-]+)-(?P<line>\d+)-(?P<col>\d+)\.lrat)"')
CHECKED = re.compile(r'bv_check(?:\s*\(config := \{[^}]*\}\))?\s*"([^"]+)"')
TACTIC = re.compile(r'bv_decide\?(?P<config>\s*\(config := \{[^}]*\}\))?')


def convert(package, path):
    source = os.path.join(package, path)
    result = subprocess.run(['lake', 'env', 'lean', path], cwd=package, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if ': error' in output:
        sys.exit(f'{path} does not elaborate:\n{output}')
    suggestions = [m.groupdict() for m in SUGGESTION.finditer(output)]
    lines = open(source).read().split('\n')
    if len(suggestions) != sum(len(TACTIC.findall(line)) for line in lines):
        sys.exit(f'{path}: every `bv_decide?` must close one goal with the SAT solver (a goal closed by normalization '
                 f'alone takes `bv_normalize` instead)\n{output}')
    directory = os.path.dirname(source)
    os.makedirs(os.path.join(directory, 'lrat'), exist_ok=True)
    base = os.path.basename(path).removesuffix('.lean')
    suggestions.sort(key=lambda s: (int(s['line']), int(s['col'])))
    # Certificates that a `bv_check` in this directory still reads are never overwritten. An existing file nothing
    # reads (left behind when a goal went back to `bv_decide?`) is replaced.
    taken = set()
    for f in os.listdir(directory):
        if f.endswith('.lean'):
            taken.update(CHECKED.findall(open(os.path.join(directory, f)).read()))
    count = collections.Counter(s['decl'] for s in suggestions)
    for s in suggestions:
        stem = f'lrat/{base}.{s["decl"]}'
        candidates = ([f'{stem}.lrat'] if count[s['decl']] == 1 else []) + [f'{stem}-{n}.lrat' for n in range(1, 1000)]
        s['name'] = next(c for c in candidates if c not in taken)
        taken.add(s['name'])
    # Rewrite from the end so that earlier columns stay valid.
    for s in reversed(suggestions):
        name = s['name']
        os.replace(os.path.join(directory, s['file']), os.path.join(directory, name))
        i, col = int(s['line']) - 1, int(s['col'])
        m = TACTIC.match(lines[i], col)
        if not m:
            sys.exit(f'{path}:{i + 1}:{col}: expected `bv_decide?`')
        lines[i] = lines[i][:col] + f'bv_check{m.group("config") or ""} "{name}"' + lines[i][m.end():]
        print(f'{path}:{i + 1}: bv_check "{name}"')
    open(source, 'w').write('\n'.join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('package', help='Lean package directory, e.g. algorithm/lean')
    parser.add_argument('files', nargs='+', help='Lean files relative to the package directory')
    args = parser.parse_args()
    for path in args.files:
        convert(args.package, path)


if __name__ == '__main__':
    main()
