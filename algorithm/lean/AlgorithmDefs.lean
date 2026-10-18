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
import Algorithm.FlatHashLife

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

/--
Structural well-formedness: all four children of every CellNode have the same tree depth.
Depth (rather than the UInt32 `level`) is compared so that equal levels cannot arise from
UInt32 wraparound of differently-sized subtrees; equal depths imply equal levels.
-/
def isWellFormed : MacroCell → Prop
  | .level4Node _ _ _ _ _ => True
  | .cellNode _ nw ne sw se =>
    isWellFormed nw ∧ isWellFormed ne ∧ isWellFormed sw ∧ isWellFormed se ∧
    nw.depth = ne.depth ∧ ne.depth = sw.depth ∧ sw.depth = se.depth

def macroCellSize : MacroCell → ℕ
  | .level4Node _ nw ne sw se => (popcount64 nw + popcount64 ne + popcount64 sw + popcount64 se).toNat
  | .cellNode _ nw ne sw se =>
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
  | .level4Node _ nw ne sw se =>
    leafToGrid ox oy nw ++
    leafToGrid (ox + 8) oy ne ++
    leafToGrid ox (oy + 8) sw ++
    leafToGrid (ox + 8) (oy + 8) se
  | .cellNode _ nw ne sw se =>
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
  | .cellNode _ nw ne sw se =>
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
  makeCellNode sn.n00 sn.n01 sn.n10 sn.n11

def quadrantNE (sn : HashLifeSubnodes) : MacroCell :=
  makeCellNode sn.n01 sn.n02 sn.n11 sn.n12

def quadrantSW (sn : HashLifeSubnodes) : MacroCell :=
  makeCellNode sn.n10 sn.n11 sn.n20 sn.n21

def quadrantSE (sn : HashLifeSubnodes) : MacroCell :=
  makeCellNode sn.n11 sn.n12 sn.n21 sn.n22

-- =========================================================================
-- Bounding Windows and Symmetries
-- =========================================================================

def central2x2Window (coords : List Coord) : List Coord :=
  coords.filter (fun (x, y) => x >= 1 && x <= 2 && y >= 1 && y <= 2)

def macroCellFlipX : MacroCell → MacroCell
  | .level4Node h nw ne sw se => .level4Node h sw se nw ne
  | .cellNode h nw ne sw se =>
    .cellNode h (macroCellFlipX sw) (macroCellFlipX se) (macroCellFlipX nw) (macroCellFlipX ne)

def macroCellFlipY : MacroCell → MacroCell
  | .level4Node h nw ne sw se => .level4Node h ne nw se sw
  | .cellNode h nw ne sw se =>
    .cellNode h (macroCellFlipY ne) (macroCellFlipY nw) (macroCellFlipY se) (macroCellFlipY sw)

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

-- =========================================================================
-- Flat HashLife Definitions and Representation
-- =========================================================================

def denoteLevel4 (arena : FlatHashLifeArena) (id : UInt32) : MacroCell :=
  if id.toUSize < arena.l4Count.toUSize then
    let idx := id.toNat
    makeLevel4Node arena.l4Nw[idx]! arena.l4Ne[idx]! arena.l4Sw[idx]! arena.l4Se[idx]!
  else
    emptyLevel4

def denoteCellNode (fuel : ℕ) (arena : FlatHashLifeArena) (lvl : UInt8) (id : UInt32) : MacroCell :=
  match fuel with
  | 0 => emptyLevel4
  | fuel + 1 =>
    if lvl <= 4 then
      denoteLevel4 arena id
    else if lvl == 5 then
      if id.toUSize < arena.cellCount.toUSize then
        let idx := id.toNat
        let nw := denoteLevel4 arena arena.cellNw[idx]!
        let ne := denoteLevel4 arena arena.cellNe[idx]!
        let sw := denoteLevel4 arena arena.cellSw[idx]!
        let se := denoteLevel4 arena arena.cellSe[idx]!
        makeCellNode nw ne sw se
      else
        emptyNode lvl.toNat
    else
      if id.toUSize < arena.cellCount.toUSize then
        let idx := id.toNat
        let childLvl := lvl - 1
        let nw := denoteCellNode fuel arena childLvl arena.cellNw[idx]!
        let ne := denoteCellNode fuel arena childLvl arena.cellNe[idx]!
        let sw := denoteCellNode fuel arena childLvl arena.cellSw[idx]!
        let se := denoteCellNode fuel arena childLvl arena.cellSe[idx]!
        makeCellNode nw ne sw se
      else
        emptyNode lvl.toNat

structure FlatCellState where
  offset : Coord
  level : UInt8
  nodeId : UInt32
  deriving DecidableEq

def flatToMacroCell (arena : FlatHashLifeArena) (st : FlatCellState) : MacroCell :=
  denoteCellNode st.level.toNat arena st.level st.nodeId

def flatToGrid (arena : FlatHashLifeArena) (st : FlatCellState) : List Coord :=
  macroCellToGrid st.offset.1 st.offset.2 (flatToMacroCell arena st)

/--
Executes `n` consecutive generations of `stepOneGeneration` in the flat arena.
Halts with `UNCOMPUTED` if any generation overflows or fails.
-/
def FlatHashLifeArena.stepOneGenerationN
    (n : ℕ) (arena : FlatHashLifeArena) (ox oy : Int32) (rootId : UInt32) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  match n with
  | 0 => ((ox, oy, rootId), arena)
  | n + 1 =>
    let ((ox1, oy1, id1), a1) := arena.stepOneGeneration ox oy rootId
    if a1.overflow != 0 || id1 == UNCOMPUTED then
      ((ox1, oy1, UNCOMPUTED), a1)
    else
      a1.stepOneGenerationN n ox1 oy1 id1

/--
Structural well-formedness of a Level 4 node in the flat arena:
The index is strictly in bounds, and if a step memo is cached (`l4HasRes = 1`),
it matches the true 16x16 next generation kernel.
-/
def l4NodeWellFormed (arena : FlatHashLifeArena) (id : UInt32) : Prop :=
  id.toUSize < arena.l4Count.toUSize ∧
  (arena.l4HasRes[id.toNat]! = 1 →
    arena.l4StepRes[id.toNat]! =
      computeLevel4NextGen16x16UInt
        arena.l4Nw[id.toNat]! arena.l4Ne[id.toNat]!
        arena.l4Sw[id.toNat]! arena.l4Se[id.toNat]!)

/--
Structural well-formedness of a Cell node in the flat arena:
Node index is strictly in bounds, levels are consistent, children are strictly
one level down and well-formed, and any cached memo denotes the true mathematical step.
-/
def cellNodeWellFormed (fuel : ℕ) (arena : FlatHashLifeArena) (lvl : UInt8) (id : UInt32) : Prop :=
  match fuel with
  | 0 => True
  | fuel + 1 =>
    id.toUSize < arena.cellCount.toUSize ∧
    arena.cellLevel[id.toNat]! = lvl ∧
    (if lvl == 5 then
      l4NodeWellFormed arena arena.cellNw[id.toNat]! ∧
      l4NodeWellFormed arena arena.cellNe[id.toNat]! ∧
      l4NodeWellFormed arena arena.cellSw[id.toNat]! ∧
      l4NodeWellFormed arena arena.cellSe[id.toNat]!
    else
      let childLvl := lvl - 1
      cellNodeWellFormed fuel arena childLvl arena.cellNw[id.toNat]! ∧
      cellNodeWellFormed fuel arena childLvl arena.cellNe[id.toNat]! ∧
      cellNodeWellFormed fuel arena childLvl arena.cellSw[id.toNat]! ∧
      cellNodeWellFormed fuel arena childLvl arena.cellSe[id.toNat]!) ∧
    (arena.cellStepRes[id.toNat]! ≠ UNCOMPUTED →
      denoteCellNode fuel arena (lvl - 1) arena.cellStepRes[id.toNat]! =
        hashLifeStep (denoteCellNode (fuel + 1) arena lvl id))

/--
Pure structural well-formedness of an arena root node:
- ID is in bounds and at level 5..60
- The quadtree is recursively well-formed down to leaves
- The denoted MacroCell satisfies functional well-formedness (`isWellFormed`)
Crucially, this invariant is purely structural and does NOT mention `stepOneGeneration`.
-/
def isWellFormedArena (arena : FlatHashLifeArena) (rootId : UInt32) : Prop :=
  rootId.toUSize < arena.cellCount.toUSize ∧
  let lvl := arena.cellLevel[rootId.toNat]!
  lvl ≥ 5 ∧ lvl ≤ 60 ∧
  cellNodeWellFormed lvl.toNat arena lvl rootId ∧
  isWellFormed (denoteCellNode lvl.toNat arena lvl rootId)

/--
$N$-step arena well-formedness across multi-step trajectories:
Initial state is well-formed, and all intermediate stepping results that do not overflow
preserve well-formedness.
-/
def isWellFormedArenaN (n : ℕ) (arena : FlatHashLifeArena) (rootId : UInt32) : Prop :=
  match n with
  | 0 => isWellFormedArena arena rootId
  | n + 1 =>
    isWellFormedArena arena rootId ∧
    ∀ (ox oy : Int32),
      let ((_, _, nextId), a') := arena.stepOneGeneration ox oy rootId
      a'.overflow = 0 → isWellFormedArenaN n a' nextId

/--
Specification of the Level 5 Base Step Simulation Property:
`arena.stepLevel5` on a well-formed level 5 node computes a result that denotes
the mathematical `hashLifeStep` when the arena does not overflow.
-/
def arenaLevel5StepSimulates (arena : FlatHashLifeArena) (nodeId : UInt32) : Prop :=
  let (resId, a') := arena.stepLevel5 nodeId
  a'.overflow = 0 →
    resId ≠ UNCOMPUTED ∧
    denoteLevel4 a' resId = hashLifeStep (denoteCellNode 5 arena 5 nodeId)

/--
Specification of the Master Single-Step Executable Refinement Property:
Executing `arena.stepOneGeneration` directly on a flat arena state produces a valid new node
whose denoted cell coordinates equal Conway's Game of Life rule (`stepGrid`) applied to the
input grid, provided the arena does not overflow.
-/
def arenaStepOneGenerationRefines (arena : FlatHashLifeArena) (st : FlatCellState) : Prop :=
  let ((nextOx, nextOy, nextId), a') :=
    arena.stepOneGeneration (Int32.ofInt st.offset.1) (Int32.ofInt st.offset.2) st.nodeId
  a'.overflow = 0 →
    nextId ≠ UNCOMPUTED ∧
    (nextOx.toInt, nextOy.toInt) = (hashLifeNextGeneration { offset := st.offset, macroCell := flatToMacroCell arena st }).offset ∧
    flatToMacroCell a' { offset := (nextOx.toInt, nextOy.toInt), level := getCellLevel a' nextId, nodeId := nextId } =
      (hashLifeNextGeneration { offset := st.offset, macroCell := flatToMacroCell arena st }).macroCell ∧
    cellsEqual
      (flatToGrid a' { offset := (nextOx.toInt, nextOy.toInt), level := getCellLevel a' nextId, nodeId := nextId })
      (stepGrid (flatToGrid arena st)) = true

/--
Specification of the Master Multi-Step Executable Refinement Property:
Executing `n` consecutive generations via `arena.stepOneGenerationN` on a flat arena state
produces a grid mathematically equal to `stepN n` (Conway's Law applied `n` times), provided all
intermediate steps do not overflow.
-/
def arenaStepOneGenerationNRefines (n : ℕ) (arena : FlatHashLifeArena) (st : FlatCellState) : Prop :=
  let ((nextOx, nextOy, nextId), a') :=
    arena.stepOneGenerationN n (Int32.ofInt st.offset.1) (Int32.ofInt st.offset.2) st.nodeId
  a'.overflow = 0 →
    nextId ≠ UNCOMPUTED ∧
    cellsEqual
      (flatToGrid a' { offset := (nextOx.toInt, nextOy.toInt), level := getCellLevel a' nextId, nodeId := nextId })
      (stepN n (flatToGrid arena st)) = true

end Algorithm


