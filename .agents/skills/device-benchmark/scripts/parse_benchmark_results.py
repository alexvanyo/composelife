#!/usr/bin/env python3
#
# Copyright (C) 2026 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import argparse
import glob
import json
import os
import re
import sys

BENCHMARK_LOGCAT_REGEX = re.compile(
    r"(?:NOT-AOT-COMPILED_)?(?P<name>[a-zA-Z0-9_]+(?:\.[a-zA-Z0-9_]+)?(?:\[[^\]]+\])*)"
    r"\[Metric \(timeNs\) results: median (?P<time_median>[0-9.E+-]+), "
    r"min (?P<time_min>[0-9.E+-]+), max (?P<time_max>[0-9.E+-]+), "
    r"standardDeviation: (?P<time_std>[0-9.E+-]+), "
    r"Metric \(allocationCount\) results: median (?P<alloc_median>[0-9.E+-]+), "
    r"min (?P<alloc_min>[0-9.E+-]+), max (?P<alloc_max>[0-9.E+-]+)"
)


def parse_content(content):
    results = {}
    # Try parsing as JSON first
    try:
        data = json.loads(content)
        if "benchmarks" in data:
            for b in data["benchmarks"]:
                name = b.get("name", "Unknown")
                metrics = b.get("metrics", {})
                time_ns = metrics.get("timeNs", {})
                allocs = metrics.get("allocationCount", {})
                results[name] = {
                    "time_median_ms": time_ns.get("median", 0.0) / 1e6,
                    "time_min_ms": time_ns.get("min", 0.0) / 1e6,
                    "time_max_ms": time_ns.get("max", 0.0) / 1e6,
                    "alloc_median": int(allocs.get("median", 0)),
                }
            return results
    except Exception:
        pass

    # Fallback to logcat regex matching
    for match in BENCHMARK_LOGCAT_REGEX.finditer(content):
        name = match.group("name")
        time_median = float(match.group("time_median")) / 1e6
        time_min = float(match.group("time_min")) / 1e6
        time_max = float(match.group("time_max")) / 1e6
        alloc_median = int(float(match.group("alloc_median")))
        results[name] = {
            "time_median_ms": time_median,
            "time_min_ms": time_min,
            "time_max_ms": time_max,
            "alloc_median": alloc_median,
        }

    return results


def main():
    parser = argparse.ArgumentParser(description="Parse AndroidX Benchmark outputs into Markdown table")
    parser.add_argument("paths", nargs="*", help="File paths or directories containing logcat or benchmark json")
    args = parser.parse_args()

    all_results = {}

    if not args.paths:
        content = sys.stdin.read()
        all_results.update(parse_content(content))
    else:
        for p in args.paths:
            if os.path.isdir(p):
                files = glob.glob(os.path.join(p, "**/*"), recursive=True)
            else:
                files = glob.glob(p)

            for file_path in files:
                if os.path.isfile(file_path):
                    try:
                        with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                            content = f.read()
                        all_results.update(parse_content(content))
                    except Exception as e:
                        print(f"Warning: could not read {file_path}: {e}", file=sys.stderr)

    if not all_results:
        print("No benchmark results found.", file=sys.stderr)
        sys.exit(1)

    print("| Benchmark | Median Time (ms) | Min (ms) | Max (ms) | Median Allocations |")
    print("| :--- | :--- | :--- | :--- | :--- |")
    for name, data in sorted(all_results.items()):
        print(
            f"| `{name}` | {data['time_median_ms']:.2f} ms | "
            f"{data['time_min_ms']:.2f} ms | {data['time_max_ms']:.2f} ms | "
            f"{data['alloc_median']:,} |"
        )


if __name__ == "__main__":
    main()
