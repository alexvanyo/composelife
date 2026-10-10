/-
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 -/

import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.MacroCellHash

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Grid Transformations, Metrics, and Cell Equivalence
-- =========================================================================

def translateGrid (dx dy : ℤ) (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (x + dx, y + dy))

def flipXGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (x, -y))

def flipYGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (-x, y))

def flipDiagGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (y, x))

def rotate90Grid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (-y, x))

def chebyshevDist (c1 c2 : Coord) : ℕ :=
  max (c1.1 - c2.1).natAbs (c1.2 - c2.2).natAbs

def manhattanDist (c1 c2 : Coord) : ℕ :=
  (c1.1 - c2.1).natAbs + (c1.2 - c2.2).natAbs

def cellsEqual (a b : List Coord) : Bool :=
  let da := deduplicate a
  let db := deduplicate b
  da.all (db.contains ·) && db.all (da.contains ·)

def sameCells (a b : List Coord) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

-- =========================================================================
-- Legacy Hash Definitions for Comparison / Flaw Verification
-- =========================================================================

def legacyLongHashCode (x : UInt64) : UInt32 :=
  (x ^^^ (x >>> 32)).toUInt32

def legacyLevel4Hash (nw ne sw se : UInt64) : UInt32 :=
  let h1 := legacyLongHashCode nw
  let h2 := h1 * 31 + legacyLongHashCode ne
  let h3 := h2 * 31 + legacyLongHashCode sw
  h3 * 31 + legacyLongHashCode se

def legacyCellNodeHash (level : UInt32) (nw ne sw se : UInt32) : UInt32 :=
  let h1 := level
  let h2 := h1 * 31 + nw
  let h3 := h2 * 31 + ne
  let h4 := h3 * 31 + sw
  h4 * 31 + se

def emptyNodeHashesList : List UInt32 :=
  (List.range 27).map (fun i => emptyNodeHash (i + 4))

-- =========================================================================
-- MacroCell Size and Population Counting
-- =========================================================================

def macroCellSize : MacroCell → ℕ
  | .leaf true => 1
  | .leaf false => 0
  | .node _ nw ne sw se =>
    macroCellSize nw + macroCellSize ne + macroCellSize sw + macroCellSize se

-- =========================================================================
-- Centered Expansion Mechanics
-- =========================================================================

def expandCentered : MacroCell → MacroCell
  | .leaf b =>
    let e0 := emptyNode 0
    let nw_se := MacroCell.node 1 e0 e0 e0 (.leaf b)
    let ne_sw := MacroCell.node 1 e0 e0 (.leaf b) e0
    let sw_ne := MacroCell.node 1 e0 (.leaf b) e0 e0
    let se_nw := MacroCell.node 1 (.leaf b) e0 e0 e0
    let e1 := emptyNode 1
    let q_nw := MacroCell.node 2 e1 e1 e1 nw_se
    let q_ne := MacroCell.node 2 e1 e1 ne_sw e1
    let q_sw := MacroCell.node 2 e1 sw_ne e1 e1
    let q_se := MacroCell.node 2 se_nw e1 e1 e1
    MacroCell.node 3 q_nw q_ne q_sw q_se
  | .node k nw ne sw se =>
    let ek_minus_1 := emptyNode (k - 1)
    let nw_se := MacroCell.node k ek_minus_1 ek_minus_1 ek_minus_1 nw
    let ne_sw := MacroCell.node k ek_minus_1 ek_minus_1 ne ek_minus_1
    let sw_ne := MacroCell.node k ek_minus_1 sw ek_minus_1 ek_minus_1
    let se_nw := MacroCell.node k se ek_minus_1 ek_minus_1 ek_minus_1
    let ek := emptyNode k
    let q_nw := MacroCell.node (k + 1) ek ek ek nw_se
    let q_ne := MacroCell.node (k + 1) ek ek ne_sw ek
    let q_sw := MacroCell.node (k + 1) ek sw_ne ek ek
    let q_se := MacroCell.node (k + 1) se_nw ek ek ek
    MacroCell.node (k + 2) q_nw q_ne q_sw q_se

-- =========================================================================
-- HashLife Subnodes and Geometric Decomposition
-- =========================================================================

structure HashLifeSubnodes where
  n00 : MacroCell
  n01 : MacroCell
  n02 : MacroCell
  n10 : MacroCell
  n11 : MacroCell
  n12 : MacroCell
  n20 : MacroCell
  n21 : MacroCell
  n22 : MacroCell
  deriving DecidableEq, Repr

def decomposeSubnodes (m : MacroCell) : HashLifeSubnodes :=
  match m with
  | .node _ nw ne sw se =>
    { n00 := centeredSubnode nw
    , n01 := centeredHorizontalSubnode nw ne
    , n02 := centeredSubnode ne
    , n10 := centeredVerticalSubnode nw sw
    , n11 := centeredSubSubnode m
    , n12 := centeredVerticalSubnode ne se
    , n20 := centeredSubnode sw
    , n21 := centeredHorizontalSubnode sw se
    , n22 := centeredSubnode se }
  | _ =>
    { n00 := m, n01 := m, n02 := m
    , n10 := m, n11 := m, n12 := m
    , n20 := m, n21 := m, n22 := m }

def quadrantNW (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n00 sn.n01 sn.n10 sn.n11

def quadrantNE (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n01 sn.n02 sn.n11 sn.n12

def quadrantSW (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n10 sn.n11 sn.n20 sn.n21

def quadrantSE (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n11 sn.n12 sn.n21 sn.n22

-- =========================================================================
-- Bounding Windows and Symmetries
-- =========================================================================

def central2x2Window (coords : List Coord) : List Coord :=
  coords.filter (fun (x, y) => x >= 1 && x <= 2 && y >= 1 && y <= 2)

def macroCellFlipX : MacroCell → MacroCell
  | .leaf b => .leaf b
  | .node k nw ne sw se =>
    .node k (macroCellFlipX sw) (macroCellFlipX se) (macroCellFlipX nw) (macroCellFlipX ne)

def macroCellFlipY : MacroCell → MacroCell
  | .leaf b => .leaf b
  | .node k nw ne sw se =>
    .node k (macroCellFlipY ne) (macroCellFlipY nw) (macroCellFlipY se) (macroCellFlipY sw)

-- =========================================================================
-- BitComputation Mask and Quadrant Definitions
-- =========================================================================

def mask11Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x1357 b then bitToCoord4x4 b else none
  )

def mask21Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x32BA b then bitToCoord4x4 b else none
  )

def mask12Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0x5D4C b then bitToCoord4x4 b else none
  )

def mask22Neighbors : List Coord :=
  (List.range 16).filterMap (fun b =>
    if testBit 0xEAC8 b then bitToCoord4x4 b else none
  )

def nwQuadrantBits : List ℕ :=
  [0x03, 0x06, 0x09, 0x0C, 0x07, 0x12, 0x0D, 0x18,
   0x0B, 0x0E, 0x21, 0x24, 0x0F, 0x1A, 0x25, 0x30]

def neQuadrantBits : List ℕ :=
  [0x07, 0x12, 0x0D, 0x18, 0x13, 0x16, 0x19, 0x1C,
   0x0F, 0x1A, 0x25, 0x30, 0x1B, 0x1E, 0x31, 0x34]

def swQuadrantBits : List ℕ :=
  [0x0B, 0x0E, 0x21, 0x24, 0x0F, 0x1A, 0x25, 0x30,
   0x23, 0x26, 0x29, 0x2C, 0x27, 0x32, 0x2D, 0x38]

def seQuadrantBits : List ℕ :=
  [0x0F, 0x1A, 0x25, 0x30, 0x1B, 0x1E, 0x31, 0x34,
   0x27, 0x32, 0x2D, 0x38, 0x33, 0x36, 0x39, 0x3C]

def nwQuadrantCoords : List Coord :=
  nwQuadrantBits.filterMap bitToCoord8x8

def neQuadrantCoords : List Coord :=
  neQuadrantBits.filterMap bitToCoord8x8

def swQuadrantCoords : List Coord :=
  swQuadrantBits.filterMap bitToCoord8x8

def seQuadrantCoords : List Coord :=
  seQuadrantBits.filterMap bitToCoord8x8

end Algorithm

