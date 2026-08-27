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

"""
Standalone script to optimize OpenType CFF (.otf) fonts generated for Watch Face Format (WFF).

This script performs low-level binary bytecode optimization on Type 2 CharStrings,
strips redundant metadata and platform tables, and optimizes local subroutine bytecode
using the fontTools library.
"""

import argparse
import sys
from fontTools.ttLib import TTFont
from fontTools.cffLib.specializer import specializeProgram


def optimize_otf(otf_path: str) -> None:
    """
    Optimizes an OpenType CFF font file in place.

    Applies the following optimizations:
    1. CharString opcode compaction via specializeProgram:
       Merges consecutive orthogonal coordinate deltas into compound multi-operand
       Type 2 instructions (e.g., combining adjacent lines into grouped hlineto/vlineto/rlineto).
    2. Private Subroutines (Subrs) specialization:
       Decompiles, optimizes, and recompiles bytecode in the CFF Private Dict Subrs index,
       preserving the trailing 'return' opcode.
    3. cmap table pruning:
       Removes legacy Macintosh Roman (Platform 1, Format 0) and redundant Platform 0
       cmap subtables, retaining only the standard Windows Unicode BMP table
       (Platform 3, PlatEnc 1, Format 4) used by Android and Skia.
    4. name table minimization:
       Removes duplicate Macintosh (Platform 1) name records across all standard name IDs,
       retaining only the Windows Unicode (Platform 3) records.
    5. Metadata table stripping:
       Removes proprietary FontForge timestamp (FFTM) and unneeded glyph definition (GDEF)
       tables from the OpenType font directory.
    """
    font = TTFont(otf_path)

    # 1. Optimize CFF CharStrings
    if "CFF " in font:
        cff = font["CFF "]
        top_dict = cff.cff.topDictIndex[0]
        charstrings = top_dict.CharStrings

        for name in charstrings.keys():
            charstring = charstrings[name]
            charstring.decompile()
            charstring.program = specializeProgram(charstring.program)

        # 2. Optimize Private Subroutines (Subrs)
        if hasattr(top_dict, "Private") and hasattr(top_dict.Private, "Subrs"):
            for subr in top_dict.Private.Subrs:
                subr.decompile()
                program = subr.program
                # Preserve the trailing 'return' token when specializing subroutines
                if program and program[-1] == "return":
                    subr.program = specializeProgram(program[:-1]) + ["return"]
                else:
                    subr.program = specializeProgram(program)

    # 3. Prune cmap subtables to keep only Windows Unicode BMP (Platform 3, PlatEnc 1)
    if "cmap" in font:
        cmap = font["cmap"]
        windows_bmp_tables = [
            table
            for table in cmap.tables
            if table.platformID == 3 and table.platEncID == 1
        ]
        if windows_bmp_tables:
            cmap.tables = windows_bmp_tables

    # 4. Prune name records to keep only Windows Unicode (Platform 3)
    if "name" in font:
        name_table = font["name"]
        name_table.names = [
            record for record in name_table.names if record.platformID == 3
        ]

    # 5. Strip unneeded metadata tables (FFTM timestamp, GDEF)
    for tag in ("FFTM", "GDEF"):
        if tag in font:
            del font[tag]

    # Save optimized font in place
    font.save(otf_path)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Optimize OpenType CFF (.otf) font files for size."
    )
    parser.add_argument(
        "otf_path",
        help="Path to the .otf font file to optimize in place",
    )
    args = parser.parse_args()
    optimize_otf(args.otf_path)


if __name__ == "__main__":
    main()
