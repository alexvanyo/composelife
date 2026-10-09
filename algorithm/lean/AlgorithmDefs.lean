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
-- MacroCell Size, Population Counting, and Well-Formedness
-- =========================================================================

def isWellFormed : MacroCell → Prop
  | .level4Node _ _ _ _ => True
  | .cellNode nw ne sw se =>
    isWellFormed nw ∧ isWellFormed ne ∧ isWellFormed sw ∧ isWellFormed se ∧
    nw.level = ne.level ∧ ne.level = sw.level ∧ sw.level = se.level

def macroCellSize : MacroCell → ℕ
  | .level4Node nw ne sw se => (popcount64 nw + popcount64 ne + popcount64 sw + popcount64 se).toNat
  | .cellNode nw ne sw se =>
    macroCellSize nw + macroCellSize ne + macroCellSize sw + macroCellSize se

def leafToGrid (ox oy : ℤ) (leaf : UInt64) : List Coord :=
  (List.range 64).filterMap (fun b =>
    if testBit leaf.toNat b then
      match bitToCoord8x8 b with
      | some (x, y) => some (ox + x, oy + y)
      | none => none
    else none
  )

def macroCellToGrid (ox oy : ℤ) : MacroCell → List Coord
  | .level4Node nw ne sw se =>
    leafToGrid ox oy nw ++
    leafToGrid (ox + 8) oy ne ++
    leafToGrid ox (oy + 8) sw ++
    leafToGrid (ox + 8) (oy + 8) se
  | .cellNode nw ne sw se =>
    let w : ℤ := (2 : ℤ) ^ (nw.level.toNat)
    macroCellToGrid ox oy nw ++
    macroCellToGrid (ox + w) oy ne ++
    macroCellToGrid ox (oy + w) sw ++
    macroCellToGrid (ox + w) (oy + w) se

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
  deriving DecidableEq

def decomposeSubnodes (m : MacroCell) : HashLifeSubnodes :=
  match m with
  | .cellNode nw ne sw se =>
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

def quadrantNW (sn : HashLifeSubnodes) : MacroCell :=
  .cellNode sn.n00 sn.n01 sn.n10 sn.n11

def quadrantNE (sn : HashLifeSubnodes) : MacroCell :=
  .cellNode sn.n01 sn.n02 sn.n11 sn.n12

def quadrantSW (sn : HashLifeSubnodes) : MacroCell :=
  .cellNode sn.n10 sn.n11 sn.n20 sn.n21

def quadrantSE (sn : HashLifeSubnodes) : MacroCell :=
  .cellNode sn.n11 sn.n12 sn.n21 sn.n22

-- =========================================================================
-- Bounding Windows and Symmetries
-- =========================================================================

def central2x2Window (coords : List Coord) : List Coord :=
  coords.filter (fun (x, y) => x >= 1 && x <= 2 && y >= 1 && y <= 2)

def macroCellFlipX : MacroCell → MacroCell
  | .level4Node nw ne sw se => .level4Node sw se nw ne
  | .cellNode nw ne sw se =>
    .cellNode (macroCellFlipX sw) (macroCellFlipX se) (macroCellFlipX nw) (macroCellFlipX ne)

def macroCellFlipY : MacroCell → MacroCell
  | .level4Node nw ne sw se => .level4Node ne nw se sw
  | .cellNode nw ne sw se =>
    .cellNode (macroCellFlipY ne) (macroCellFlipY nw) (macroCellFlipY se) (macroCellFlipY sw)

inductive MicroCell where
  | leaf (alive : Bool)
  | node (nw ne sw se : MicroCell)
  deriving DecidableEq

def makeLevel1 (nw ne sw se : Bool) : MicroCell :=
  .node (.leaf nw) (.leaf ne) (.leaf sw) (.leaf se)

def makeLevel2 (nw ne sw se : MicroCell) : MicroCell :=
  .node nw ne sw se

def microCellToGrid (ox oy : ℤ) : MicroCell → List Coord
  | .leaf true => [(ox, oy)]
  | .leaf false => []
  | .node (.leaf nw) (.leaf ne) (.leaf sw) (.leaf se) =>
    (if nw then [(ox, oy)] else []) ++
    (if ne then [(ox + 1, oy)] else []) ++
    (if sw then [(ox, oy + 1)] else []) ++
    (if se then [(ox + 1, oy + 1)] else [])
  | .node nw ne sw se =>
    microCellToGrid ox oy nw ++
    microCellToGrid (ox + 2) oy ne ++
    microCellToGrid ox (oy + 2) sw ++
    microCellToGrid (ox + 2) (oy + 2) se

def level2ToBits (m : MicroCell) : ℕ :=
  match m with
  | .node (.node (.leaf b0) (.leaf b1) (.leaf b2) (.leaf b3))
          (.node (.leaf b4) (.leaf b5) (.leaf b6) (.leaf b7))
          (.node (.leaf b8) (.leaf b9) (.leaf b10) (.leaf b11))
          (.node (.leaf b12) (.leaf b13) (.leaf b14) (.leaf b15)) =>
    boolToNat b0 * (2^0) + boolToNat b1 * (2^1) + boolToNat b2 * (2^2) + boolToNat b3 * (2^3) +
    boolToNat b4 * (2^4) + boolToNat b5 * (2^5) + boolToNat b6 * (2^6) + boolToNat b7 * (2^7) +
    boolToNat b8 * (2^8) + boolToNat b9 * (2^9) + boolToNat b10 * (2^10) + boolToNat b11 * (2^11) +
    boolToNat b12 * (2^12) + boolToNat b13 * (2^13) + boolToNat b14 * (2^14) + boolToNat b15 * (2^15)
  | _ => 0

def bitsToLevel1 (out : ℕ) : MicroCell :=
  let b11 := (shiftRight out 0) % 2 == 1
  let b21 := (shiftRight out 1) % 2 == 1
  let b12 := (shiftRight out 2) % 2 == 1
  let b22 := (shiftRight out 3) % 2 == 1
  makeLevel1 b11 b21 b12 b22

def hashLifeStepLevel2 (m : MicroCell) : MicroCell :=
  let bits := level2ToBits m
  let out4 := computeNextGen4x4 bits
  bitsToLevel1 out4

def microCellFlipX : MicroCell → MicroCell
  | .leaf b => .leaf b
  | .node nw ne sw se => .node (microCellFlipX sw) (microCellFlipX se) (microCellFlipX nw) (microCellFlipX ne)

def microCellFlipY : MicroCell → MicroCell
  | .leaf b => .leaf b
  | .node nw ne sw se => .node (microCellFlipY ne) (microCellFlipY nw) (microCellFlipY se) (microCellFlipY sw)

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

-- =========================================================================
-- HashLife State Machine, Offset Dynamics, and Transitions
-- =========================================================================

structure HashLifeCellState where
  offset : Coord
  macroCell : MacroCell
  deriving DecidableEq

def hashLifeToGrid (st : HashLifeCellState) : List Coord :=
  macroCellToGrid st.offset.1 st.offset.2 st.macroCell

def stepOffsetDelta (level : ℕ) : ℤ :=
  (2 : ℤ) ^ (level - 2)

def expandOffsetDelta (level : ℕ) : ℤ :=
  -3 * ((2 : ℤ) ^ (level - 1))

def isConfinedToSubSubnode (m : MacroCell) : Prop :=
  macroCellSize (centeredSubSubnode m) = macroCellSize m

def needToExpand (m : MacroCell) : Bool :=
  m.level <= 4 || (macroCellSize (centeredSubSubnode m) != macroCellSize m)

def hashLifeNextGenerationStep (st : HashLifeCellState) : HashLifeCellState :=
  let nextNode := hashLifeStep st.macroCell
  let nextOffset := (st.offset.1 + stepOffsetDelta st.macroCell.level.toNat,
                     st.offset.2 + stepOffsetDelta st.macroCell.level.toNat)
  { offset := nextOffset, macroCell := nextNode }

def hashLifeNextGeneration (st : HashLifeCellState) : HashLifeCellState :=
  if needToExpand st.macroCell then
    let expandedNode := expandCentered st.macroCell
    let expandedOffset := (st.offset.1 + expandOffsetDelta st.macroCell.level.toNat,
                           st.offset.2 + expandOffsetDelta st.macroCell.level.toNat)
    hashLifeNextGenerationStep { offset := expandedOffset, macroCell := expandedNode }
  else
    hashLifeNextGenerationStep st

def hashLifeStepN : ℕ → HashLifeCellState → HashLifeCellState
  | 0, st => st
  | n + 1, st => hashLifeStepN n (hashLifeNextGeneration st)

end Algorithm

