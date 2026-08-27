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
Standalone script to build OpenType CFF (.otf) watch face fonts directly using fontTools.

Replaces FontForge entirely by constructing CFF Type 2 CharStrings, cmap mappings,
and OpenType font tables in memory directly from minute contour data.
"""

import argparse
import os
import sys
from fontTools.fontBuilder import FontBuilder
from fontTools.pens.t2CharStringPen import T2CharStringPen
from fontTools.cffLib.specializer import specializeProgram

CUSTOM_CODE_POINT_START = 0x4E00
GENERATIONS_PER_MINUTE = 300
MINUTES_PER_HOUR = 60
EM_SIZE = 70


def parse_minute_data(file_path: str):
    """
    Parses a minute data file.
    Returns (gen_map, glyph_contours_dict).
    """
    gen_map = []
    glyph_contours = {}
    current_glyph = None

    with open(file_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("GEN_MAP "):
                gen_map = [int(x) for x in line[8:].split()]
            elif line.startswith("GLYPH "):
                current_glyph = int(line[6:])
                glyph_contours[current_glyph] = []
            elif line.startswith("CONTOUR "):
                coords_str = line[8:].split()
                contour = []
                for pt in coords_str:
                    x, y = pt.split(",")
                    contour.append((int(x), int(y)))
                if current_glyph is not None:
                    glyph_contours[current_glyph].append(contour)

    return gen_map, glyph_contours


def build_hour_font(hour_prefix: str, minute_dir: str, output_otf: str) -> None:
    """
    Builds a complete, optimized OpenType CFF (.otf) font for the given hour.
    """
    glyph_order = [".notdef"]
    charstrings = {}
    cmap = {}

    # Setup .notdef glyph
    notdef_pen = T2CharStringPen(EM_SIZE, None)
    notdef_cs = notdef_pen.getCharString()
    notdef_cs.decompile()
    notdef_cs.program = specializeProgram(notdef_cs.program)
    charstrings[".notdef"] = notdef_cs

    for minute in range(MINUTES_PER_HOUR):
        data_path = os.path.join(minute_dir, f"{hour_prefix}:{minute:02d}.data")
        if not os.path.exists(data_path):
            raise FileNotFoundError(f"Minute data file not found: {data_path}")

        gen_map, glyph_contours = parse_minute_data(data_path)

        # 1. Build cmap mapping for all 300 generations in this minute
        minute_base_cp = CUSTOM_CODE_POINT_START + minute * GENERATIONS_PER_MINUTE
        for gen in range(GENERATIONS_PER_MINUTE):
            canonical_idx = gen_map[gen]
            glyph_name = f"c_{minute:02d}_{canonical_idx}"
            cmap[minute_base_cp + gen] = glyph_name

        # 2. Build CharStrings for all unique canonical glyphs in this minute
        for canonical_idx, contours in glyph_contours.items():
            glyph_name = f"c_{minute:02d}_{canonical_idx}"
            pen = T2CharStringPen(EM_SIZE, None)
            for contour in contours:
                if not contour:
                    continue
                pen.moveTo(contour[0])
                for pt in contour[1:]:
                    pen.lineTo(pt)
                pen.closePath()

            cs = pen.getCharString()
            cs.decompile()
            cs.program = specializeProgram(cs.program)
            charstrings[glyph_name] = cs
            glyph_order.append(glyph_name)

    # Build OpenType CFF font
    fb = FontBuilder(unitsPerEm=EM_SIZE, isTTF=False)
    fb.setupGlyphOrder(glyph_order)
    fb.setupCharacterMap(cmap)
    fb.setupCFF(
        psName=f"GameOfLifeHour{hour_prefix}",
        fontInfo={
            "FullName": f"GameOfLifeHour{hour_prefix}",
            "FamilyName": "GameOfLifeHours",
            "Weight": "Regular",
        },
        privateDict={"defaultWidthX": EM_SIZE},
        charStringsDict=charstrings,
    )
    fb.setupHorizontalMetrics({name: (EM_SIZE, 0) for name in glyph_order})
    fb.setupHorizontalHeader(ascent=EM_SIZE, descent=0)
    fb.setupOS2(
        sTypoAscender=EM_SIZE,
        sTypoDescender=0,
        usWinAscent=EM_SIZE,
        usWinDescent=0,
    )
    fb.setupPost(keepGlyphNames=False)
    fb.setupNameTable({
        "familyName": "GameOfLifeHours",
        "styleName": "Regular",
        "psName": f"GameOfLifeHour{hour_prefix}",
    })

    # Ensure output directory exists and save
    os.makedirs(os.path.dirname(os.path.abspath(output_otf)), exist_ok=True)
    fb.save(output_otf)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build OpenType CFF (.otf) watch face font using fontTools."
    )
    parser.add_argument(
        "--hour-prefix",
        required=True,
        help="Hour prefix (e.g. 00, 01, _1)",
    )
    parser.add_argument(
        "--minute-dir",
        required=True,
        help="Directory containing minute .data files",
    )
    parser.add_argument(
        "--output-otf",
        required=True,
        help="Path for generated output .otf file",
    )
    args = parser.parse_args()

    build_hour_font(
        hour_prefix=args.hour_prefix,
        minute_dir=args.minute_dir,
        output_otf=args.output_otf,
    )


if __name__ == "__main__":
    main()
