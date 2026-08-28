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
Standalone script to build consolidated 3-hour OpenType CFF (.otf) watch face fonts.

Takes pre-extracted shape subroutines and glyph instances computed in Kotlin for 3 hours,
and compiles them into a single OpenType CFF font containing 54,000 frames.
"""

import argparse
import os
import sys
from fontTools.fontBuilder import FontBuilder
from fontTools.pens.t2CharStringPen import T2CharStringPen
from fontTools.cffLib import SubrsIndex
from fontTools.misc.psCharStrings import T2CharString
from fontTools.cffLib.specializer import specializeProgram

CUSTOM_CODE_POINT_START = 0x0100
GENERATIONS_PER_MINUTE = 300
MINUTES_PER_HOUR = 60
FRAMES_PER_HOUR = MINUTES_PER_HOUR * GENERATIONS_PER_MINUTE  # 18,000
EM_SIZE = 70
# In Type 2 CharStrings, subroutine counts < 1240 use bias 107, allowing the top 215 subroutines
# to be encoded with 1-byte operands. Crossing >= 1240 shifts the bias to 1131, penalizing all
# call sites with 2-byte operands (+1.86 MB per font). 1239 is the exact optimal threshold.
MAX_SUBROUTINES_PER_FONT = 1239


def parse_minute_data(file_path: str):
    """
    Parses a minute data file with pre-extracted shape subroutines and glyph instances.
    Returns (gen_map, subr_shapes_dict, glyph_instances_dict).
    """
    gen_map = []
    subr_shapes = {}
    glyph_instances = {}
    current_glyph = None

    with open(file_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("GEN_MAP "):
                gen_map = [int(x) for x in line[8:].split()]
            elif line.startswith("SUBR "):
                parts = line[5:].split(" ", 1)
                subr_id = int(parts[0])
                coords = []
                if len(parts) > 1:
                    for pt in parts[1].split():
                        x, y = pt.split(",")
                        coords.append((int(x), int(y)))
                subr_shapes[subr_id] = tuple(coords)
            elif line.startswith("GLYPH "):
                current_glyph = int(line[6:])
                glyph_instances[current_glyph] = []
            elif line.startswith("INST "):
                parts = line[5:].split()
                subr_id = int(parts[0])
                ox, oy = [int(c) for c in parts[1].split(",")]
                if current_glyph is not None:
                    glyph_instances[current_glyph].append((subr_id, ox, oy))

    return gen_map, subr_shapes, glyph_instances


def build_consolidated_font(
    hour_prefixes: list,
    font_name: str,
    minute_dir: str,
    output_otf: str,
) -> None:
    """
    Builds a complete, optimized 3-hour OpenType CFF (.otf) font.
    """
    glyph_order = [".notdef"]
    charstrings = {}
    cmap = {}

    # Setup .notdef glyph
    notdef_pen = T2CharStringPen(None, None)
    notdef_cs = notdef_pen.getCharString()
    charstrings[".notdef"] = notdef_cs

    # Collect all unique relative shapes and glyph instances across all 3 hours (180 minutes)
    group_subr_shapes = {}  # shape_tuple -> group_subr_id
    subr_defs = []  # list of shape_tuple
    subr_counts = []

    hours_data = []

    for hour_idx, hour_prefix in enumerate(hour_prefixes):
        for minute in range(MINUTES_PER_HOUR):
            data_path = os.path.join(minute_dir, f"{hour_prefix}:{minute:02d}.data")
            if not os.path.exists(data_path):
                raise FileNotFoundError(f"Minute data file not found: {data_path}")

            gen_map, subr_shapes, glyph_instances = parse_minute_data(data_path)
            hours_data.append((hour_idx, hour_prefix, minute, gen_map, subr_shapes, glyph_instances))

            for instances in glyph_instances.values():
                for local_subr_id, ox, oy in instances:
                    shape = subr_shapes[local_subr_id]
                    if shape not in group_subr_shapes:
                        gid = len(subr_defs)
                        group_subr_shapes[shape] = gid
                        subr_defs.append(shape)
                        subr_counts.append(1)
                    else:
                        gid = group_subr_shapes[shape]
                        subr_counts[gid] += 1

    # Select top most profitable subroutines across the 3 hours (up to bias threshold)
    sorted_subr_ids = sorted(
        range(len(subr_defs)), key=lambda i: subr_counts[i], reverse=True
    )
    top_subr_ids = sorted_subr_ids[:MAX_SUBROUTINES_PER_FONT]
    top_subr_id_map = {orig_id: new_id for new_id, orig_id in enumerate(top_subr_ids)}

    num_subrs = len(top_subr_ids)
    bias = 107 if num_subrs < 1240 else (1131 if num_subrs < 33900 else 32768)

    # 1. Compile SubrsIndex
    subrs_index = SubrsIndex()
    for orig_id in top_subr_ids:
        shape = subr_defs[orig_id]
        pen = T2CharStringPen(None, None)
        if shape:
            pen.moveTo(shape[0])
            for pt in shape[1:]:
                pen.lineTo(pt)
            pen.lineTo(shape[0])
            pen.closePath()
        cs = pen.getCharString()
        cs.decompile()
        prog = specializeProgram(cs.program)
        if prog and prog[-1] == "endchar":
            prog = prog[:-1]
        if len(prog) >= 2 and prog[1] in ("hmoveto", "vmoveto"):
            prog = prog[2:]
        elif len(prog) >= 3 and prog[2] == "rmoveto":
            prog = prog[3:]
        subr_cs = T2CharString(program=prog + ["return"])
        subrs_index.append(subr_cs)

    # 2. Build CharStrings and cmap for all 3 hours
    for hour_idx, hour_prefix, minute, gen_map, subr_shapes, glyph_instances in hours_data:
        hour_base_cp = CUSTOM_CODE_POINT_START + (hour_idx * FRAMES_PER_HOUR) + (minute * GENERATIONS_PER_MINUTE)
        for gen in range(GENERATIONS_PER_MINUTE):
            canonical_idx = gen_map[gen]
            glyph_name = f"c_{hour_prefix}_{minute:02d}_{canonical_idx}"
            cmap[hour_base_cp + gen] = glyph_name

        for canonical_idx, instances in glyph_instances.items():
            glyph_name = f"c_{hour_prefix}_{minute:02d}_{canonical_idx}"
            prog = []
            curr_x, curr_y = 0, 0
            for local_subr_id, ox, oy in instances:
                shape = subr_shapes[local_subr_id]
                orig_group_id = group_subr_shapes[shape]

                dx = ox - curr_x
                dy = oy - curr_y
                if dx == 0 and dy != 0:
                    prog.extend([dy, "vmoveto"])
                elif dy == 0 and dx != 0:
                    prog.extend([dx, "hmoveto"])
                else:
                    prog.extend([dx, dy, "rmoveto"])

                if orig_group_id in top_subr_id_map:
                    new_subr_id = top_subr_id_map[orig_group_id]
                    prog.extend([new_subr_id - bias, "callsubr"])
                else:
                    pen = T2CharStringPen(None, None)
                    if shape:
                        pen.moveTo(shape[0])
                        for pt in shape[1:]:
                            pen.lineTo(pt)
                        pen.lineTo(shape[0])
                        pen.closePath()
                    cs = pen.getCharString()
                    cs.decompile()
                    inline_prog = specializeProgram(cs.program)
                    if inline_prog and inline_prog[-1] == "endchar":
                        inline_prog = inline_prog[:-1]
                    if len(inline_prog) >= 2 and inline_prog[1] in (
                        "hmoveto",
                        "vmoveto",
                    ):
                        inline_prog = inline_prog[2:]
                    elif (
                        len(inline_prog) >= 3 and inline_prog[2] == "rmoveto"
                    ):
                        inline_prog = inline_prog[3:]
                    prog.extend(inline_prog)

                curr_x, curr_y = ox, oy

            prog.append("endchar")
            cs = T2CharString(program=prog)
            charstrings[glyph_name] = cs
            glyph_order.append(glyph_name)

    # Build OpenType CFF font
    fb = FontBuilder(unitsPerEm=EM_SIZE, isTTF=False)
    fb.setupGlyphOrder(glyph_order)
    fb.setupCharacterMap(cmap)
    fb.setupCFF(
        psName=font_name,
        fontInfo={
            "FullName": font_name,
            "FamilyName": "GameOfLifeHours",
            "Weight": "Regular",
        },
        privateDict={"defaultWidthX": EM_SIZE},
        charStringsDict=charstrings,
    )

    cff = fb.font["CFF "]
    top_dict = cff.cff.topDictIndex[0]
    top_dict.Private.Subrs = subrs_index

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
        "psName": font_name,
    })

    # Ensure output directory exists and save
    os.makedirs(os.path.dirname(os.path.abspath(output_otf)), exist_ok=True)
    fb.save(output_otf)
    print(f"Successfully generated {output_otf} with {len(glyph_order)} glyphs and {len(cmap)} cmap mappings.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build consolidated 3-hour OpenType CFF (.otf) watch face font."
    )
    parser.add_argument(
        "--hour-prefixes",
        required=True,
        help="Comma-separated hour prefixes (e.g. 00,01,02)",
    )
    parser.add_argument(
        "--font-name",
        required=True,
        help="Font PostScript name (e.g. GameOfLifeHours00_02)",
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

    hour_prefixes = [h.strip() for h in args.hour_prefixes.split(",")]

    build_consolidated_font(
        hour_prefixes=hour_prefixes,
        font_name=args.font_name,
        minute_dir=args.minute_dir,
        output_otf=args.output_otf,
    )


if __name__ == "__main__":
    main()
