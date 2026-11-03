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

def cellsEqual (a b : List Coord) : Bool :=
  let da := deduplicate a
  let db := deduplicate b
  da.all (db.contains ·) && db.all (da.contains ·)

def sameCells (a b : List Coord) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

-- =========================================================================
-- Hash Constants
-- =========================================================================

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
-- Semantic Cell Model of MacroCells
-- =========================================================================

/--
Morton (Z-order) bit index of the cell at relative coordinates (x, y) within an 8x8 leaf,
matching `cellToLeafBitUInt` and the inverse of `bitToCoord8x8`.
-/
def mortonIndex (x y : ℕ) : ℕ :=
  x % 2 + 2 * (y % 2) + 4 * (x / 2 % 2) + 8 * (y / 2 % 2) + 16 * (x / 4) + 32 * (y / 4)

/--
Whether the 8x8 leaf has an alive cell at relative coordinates (x, y).
Coordinates outside of [0, 8) x [0, 8) are dead.
-/
def leafAt (leaf : UInt64) (x y : ℤ) : Bool :=
  if 0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 then
    leaf.toBitVec.getLsbD (mortonIndex x.toNat y.toNat)
  else false

/--
Combines four quadrant cell functions of width `w` into a cell function of width `2 * w`.
Coordinates outside of [0, 2w) x [0, 2w) are dead.
-/
def quadSel (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ) : Bool :=
  if 0 ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < 2 * w then
    if x < w then
      if y < w then f1 x y else f3 x (y - w)
    else
      if y < w then f2 (x - w) y else f4 (x - w) (y - w)
  else false

/--
Whether the MacroCell has an alive cell at relative coordinates (x, y).
-/
def cellAt : MacroCell → ℤ → ℤ → Bool
  | .level4Node _ nw ne sw se, x, y =>
    quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 x y
  | .cellNode _ nw ne sw se, x, y =>
    quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) ((2 : ℤ) ^ nw.level.toNat) x y

/--
Number of alive Moore neighbors of (x, y) for an arbitrary cell function.
-/
def neighborCountAt (f : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (mooreOffsets.filter (fun d => f (x + d.1) (y + d.2))).length

/--
Conway's rule applied pointwise to an arbitrary cell function.
-/
def nextGenAt (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  lifeRule (f x y) (neighborCountAt f x y)

/--
Structural well-formedness at an explicit tree depth: every Level4Node is at depth 4,
and every CellNode at depth `d` has four children at depth `d - 1`.
-/
def WFd : MacroCell → ℕ → Prop
  | .level4Node .., d => d = 4
  | .cellNode _ nw ne sw se, d =>
    5 ≤ d ∧ WFd nw (d - 1) ∧ WFd ne (d - 1) ∧ WFd sw (d - 1) ∧ WFd se (d - 1)

-- =========================================================================
-- Bit-Level Kernels: Cell Functions of 4x4 Grids
-- =========================================================================

/--
Morton (Z-order) bit index of the cell at relative coordinates (x, y) within a 4x4 grid, matching
`bitToCoord4x4`: each 2x2 quadrant is a nibble.
-/
def mortonIndex4 (x y : ℕ) : ℕ :=
  x % 2 + 2 * (y % 2) + 4 * (x / 2) + 8 * (y / 2)

/--
The cells of a 4x4 grid encoded in the low 16 bits of `w` in Morton order. Coordinates outside of
[0, 4) x [0, 4) are dead.
-/
def grid4At (w : UInt32) (x y : ℤ) : Bool :=
  if 0 ≤ x ∧ x < 4 ∧ 0 ≤ y ∧ y < 4 then w.toBitVec.getLsbD (mortonIndex4 x.toNat y.toNat) else false

-- =========================================================================
-- MacroCell Engine: Hash Consistency and Kotlin Step State
-- =========================================================================

/--
Every node stores the hash that its smart constructor (`makeLevel4Node`, `makeCellNode`) computes from its
children. Kotlin builds every `MacroCell` through these constructors, so its canonical maps, which identify
nodes by their children, identify exactly the equal MacroCell values.
-/
def HashOK : MacroCell → Prop
  | .level4Node h nw ne sw se => h = level4Hash nw ne sw se
  | .cellNode h nw ne sw se =>
    h = cellNodeHash (nw.level + 1) nw.cellHashCode ne.cellHashCode sw.cellHashCode se.cellHashCode ∧
    HashOK nw ∧ HashOK ne ∧ HashOK sw ∧ HashOK se

/--
The HashLife state denoted by the `Int32`-offset step state that `LeanHashLifeAlgorithm` iterates.
-/
def HashLifeStepState.toCellState (st : HashLifeStepState) : HashLifeCellState :=
  { offset := (st.offsetX.toInt, st.offsetY.toInt), macroCell := st.macroCell }

/--
The center `offset + 2 ^ (level - 1)` of a HashLife state's window. Every HashLife generation keeps it fixed
(expanding moves the corner out by as much as the level grows), so a bound on it bounds every corner reached.
-/
def windowCenter (st : HashLifeCellState) : Coord :=
  (st.offset.1 + (2 : ℤ) ^ (st.macroCell.depth - 1), st.offset.2 + (2 : ℤ) ^ (st.macroCell.depth - 1))

-- =========================================================================
-- Flat HashLife Arena: Denotation, Invariant, and Stepping Specification
-- =========================================================================

/--
The MacroCell denoted by the Level 4 id `id` (out-of-range ids denote the empty Level 4 node).
-/
def denoteLevel4 (arena : FlatHashLifeArena) (id : UInt32) : MacroCell :=
  if id < arena.l4Count then
    makeLevel4Node arena.l4Nw[id.toNat]! arena.l4Ne[id.toNat]! arena.l4Sw[id.toNat]! arena.l4Se[id.toNat]!
  else
    emptyLevel4

/--
The MacroCell denoted by `id` read at height `h`, i.e. at level `h + 4`: height 0 reads the Level 4 table,
greater heights read the CellNode table (out-of-range ids denote the empty node of that level).
-/
def denoteAt : ℕ → FlatHashLifeArena → UInt32 → MacroCell
  | 0, arena, id => denoteLevel4 arena id
  | h + 1, arena, id =>
    if id < arena.cellCount then
      makeCellNode
        (denoteAt h arena arena.cellNw[id.toNat]!) (denoteAt h arena arena.cellNe[id.toNat]!)
        (denoteAt h arena arena.cellSw[id.toNat]!) (denoteAt h arena arena.cellSe[id.toNat]!)
    else
      emptyNode (h + 5)

/--
The stored level of CellNode `id`, as a natural number.
-/
def cellLevelOf (arena : FlatHashLifeArena) (id : UInt32) : ℕ :=
  (arena.cellLevel[id.toNat]!).toNat

/--
The MacroCell denoted by CellNode `id`, read at its stored level.
-/
def denoteCell (arena : FlatHashLifeArena) (id : UInt32) : MacroCell :=
  denoteAt (cellLevelOf arena id - 4) arena id

/--
`id` is a node of height `h` (level `h + 4`) in `arena` that denotes `m`: an in-range Level 4 id for `h = 0`,
and an in-range CellNode id stored at level `h + 4` for `h ≥ 1`.
-/
def NodeIs (arena : FlatHashLifeArena) : ℕ → UInt32 → MacroCell → Prop
  | 0, id, m => id < arena.l4Count ∧ denoteLevel4 arena id = m
  | h + 1, id, m => id < arena.cellCount ∧ cellLevelOf arena id = h + 5 ∧ denoteAt (h + 1) arena id = m

/--
The four children of CellNode `id` are nodes one level down: Level 4 ids for a level 5 node, and in-range
CellNodes stored at the level below otherwise.
-/
def CellChildrenWF (arena : FlatHashLifeArena) (id : UInt32) : Prop :=
  let L := cellLevelOf arena id
  let i := id.toNat
  5 ≤ L ∧
  (L = 5 →
    arena.cellNw[i]! < arena.l4Count ∧ arena.cellNe[i]! < arena.l4Count ∧
    arena.cellSw[i]! < arena.l4Count ∧ arena.cellSe[i]! < arena.l4Count) ∧
  (L ≠ 5 →
    (arena.cellNw[i]! < arena.cellCount ∧ cellLevelOf arena arena.cellNw[i]! = L - 1) ∧
    (arena.cellNe[i]! < arena.cellCount ∧ cellLevelOf arena arena.cellNe[i]! = L - 1) ∧
    (arena.cellSw[i]! < arena.cellCount ∧ cellLevelOf arena arena.cellSw[i]! = L - 1) ∧
    (arena.cellSe[i]! < arena.cellCount ∧ cellLevelOf arena arena.cellSe[i]! = L - 1))

/--
The memoized step result of CellNode `id`, if present, is a node one level down that denotes
HashLife's step of the node.
-/
def CellMemoWF (arena : FlatHashLifeArena) (id : UInt32) : Prop :=
  arena.cellStepRes[id.toNat]! ≠ UNCOMPUTED →
    NodeIs arena (cellLevelOf arena id - 5) arena.cellStepRes[id.toNat]! (hashLifeStep (denoteCell arena id))

/--
The global invariant of a flat HashLife arena. It is purely structural: every in-range slot (reachable from
a root or not) is well-formed, populations and memoized step results are correct for the MacroCell each slot
denotes, the pre-interned empty nodes are in place, and the tables have room for every index below their
capacity. It does not mention any stepping function.
-/
structure ArenaWF (arena : FlatHashLifeArena) : Prop where
  l4Size :
    arena.l4Mask.toNat + 1 ≤ arena.l4Nw.size ∧ arena.l4Mask.toNat + 1 ≤ arena.l4Ne.size ∧
    arena.l4Mask.toNat + 1 ≤ arena.l4Sw.size ∧ arena.l4Mask.toNat + 1 ≤ arena.l4Se.size ∧
    arena.l4Mask.toNat + 1 ≤ arena.l4StepRes.size ∧ arena.l4Mask.toNat + 1 ≤ arena.l4HasRes.size
  cellSize :
    arena.cellMask.toNat + 1 ≤ arena.cellNw.size ∧ arena.cellMask.toNat + 1 ≤ arena.cellNe.size ∧
    arena.cellMask.toNat + 1 ≤ arena.cellSw.size ∧ arena.cellMask.toNat + 1 ≤ arena.cellSe.size ∧
    arena.cellMask.toNat + 1 ≤ arena.cellLevel.size ∧ arena.cellMask.toNat + 1 ≤ arena.cellPop.size ∧
    arena.cellMask.toNat + 1 ≤ arena.cellStepRes.size
  l4CountLe : arena.l4Count.toNat ≤ arena.l4Mask.toNat + 1
  cellCountLe : arena.cellCount.toNat ≤ arena.cellMask.toNat + 1
  l4Empty :
    0 < arena.l4Count ∧ arena.l4Nw[0]! = 0 ∧ arena.l4Ne[0]! = 0 ∧ arena.l4Sw[0]! = 0 ∧ arena.l4Se[0]! = 0
  cellEmptyCount : 56 ≤ arena.cellCount.toNat
  cellEmpty : ∀ k : ℕ, k < 56 →
    cellLevelOf arena k.toUInt32 = k + 5 ∧
    arena.cellNw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    arena.cellNe[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    arena.cellSw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    arena.cellSe[k]! = emptyNodeForLevel (k + 4).toUInt32
  l4Memo : ∀ id : UInt32, id < arena.l4Count → arena.l4HasRes[id.toNat]! = 1 →
    arena.l4StepRes[id.toNat]! =
      computeLevel4NextGen16x16UInt arena.l4Nw[id.toNat]! arena.l4Ne[id.toNat]!
        arena.l4Sw[id.toNat]! arena.l4Se[id.toNat]!
  cellChildren : ∀ id : UInt32, id < arena.cellCount → CellChildrenWF arena id
  cellPop : ∀ id : UInt32, id < arena.cellCount → arena.cellPop[id.toNat]! = (denoteCell arena id).size
  cellMemo : ∀ id : UInt32, id < arena.cellCount → CellMemoWF arena id

/--
Every node of `a` is still a node of `b` with the same height and denotation.
-/
def NodesPreserved (a b : FlatHashLifeArena) : Prop :=
  ∀ (h : ℕ) (id : UInt32) (m : MacroCell), NodeIs a h id m → NodeIs b h id m

/--
A node table of the arena is at its capacity (the only failure the flat engine reports), by the test the interning functions use before raising the failure
flag (`count ≥ mask + 1`).
-/
def ArenaFull (a : FlatHashLifeArena) : Prop :=
  a.l4Count ≥ a.l4Mask + 1 ∨ a.cellCount ≥ a.cellMask + 1

/--
The HashLife state whose top-left corner is `(ox, oy)` and whose root is CellNode `rootId`.
-/
def flatState (arena : FlatHashLifeArena) (ox oy : Int32) (rootId : UInt32) : HashLifeCellState :=
  { offset := (ox.toInt, oy.toInt), macroCell := denoteCell arena rootId }

/--
The flat engine's preparation of a root before stepping: expand by two levels if the root is at level 5
(whose one-generation step would be a level 4 node, which cannot be a CellNode root) or if it has live
cells outside its centered sub-subnode.
-/
def flatPrepare (st : HashLifeCellState) : HashLifeCellState :=
  if st.macroCell.level ≤ 5 || needToExpand st.macroCell then
    { offset := (st.offset.1 + expandOffsetDelta st.macroCell.level.toNat,
                 st.offset.2 + expandOffsetDelta st.macroCell.level.toNat),
      macroCell := expandCentered st.macroCell }
  else
    st

/--
One generation of the flat engine at the MacroCell level: prepare, then take one HashLife step.
-/
def flatNextGeneration (st : HashLifeCellState) : HashLifeCellState :=
  hashLifeNextGenerationStep (flatPrepare st)

/--
`n` generations of the flat engine at the MacroCell level.
-/
def flatStepN : ℕ → HashLifeCellState → HashLifeCellState
  | 0, st => st
  | n + 1, st => flatStepN n (flatNextGeneration st)

/--
The flat engine can represent the next generation of `st`: the prepared root is at most level 30, and
the next top-left corner fits in `Int32`.
-/
def flatStepInRange (st : HashLifeCellState) : Prop :=
  (flatPrepare st).macroCell.level.toNat ≤ 30 ∧
  -2147483648 ≤ (flatNextGeneration st).offset.1 ∧ (flatNextGeneration st).offset.1 ≤ 2147483647 ∧
  -2147483648 ≤ (flatNextGeneration st).offset.2 ∧ (flatNextGeneration st).offset.2 ≤ 2147483647

/--
`n` consecutive calls of `stepOneGeneration`, as done by `FlatLeanHashLifeAlgorithm`, stopping at the first
failure.
-/
def FlatHashLifeArena.stepOneGenerationN
    (n : ℕ) (arena : FlatHashLifeArena) (ox oy : Int32) (rootId : UInt32) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  match n with
  | 0 => ((ox, oy, rootId), arena)
  | n + 1 =>
    let ((ox1, oy1, id1), a1) := arena.stepOneGeneration ox oy rootId
    if id1 == UNCOMPUTED then
      ((ox1, oy1, UNCOMPUTED), a1)
    else
      a1.stepOneGenerationN n ox1 oy1 id1

/--
The states reachable by the generation loop of `FlatLeanHashLifeAlgorithm`, starting from a root that denotes
`st0`, after `k` successful generations. Between generations the loop may:
- take a step (`stepOneGeneration`) that succeeds, advancing to the next generation;
- take a step that fails, keeping the root but continuing in the arena the failed step left behind;
- clear the failure flag (Kotlin writes `arena.overflow = 0u`, which is `clearOverflow`);
- compact the root into a well-formed fresh arena (`compactRootFrom`), continuing there if that succeeds.
-/
inductive FlatRun (st0 : HashLifeCellState) : ℕ → FlatHashLifeArena → Int32 → Int32 → UInt32 → Prop
  | start {a : FlatHashLifeArena} {ox oy : Int32} {root : UInt32} :
    ArenaWF a → root < a.cellCount → flatState a ox oy root = st0 → FlatRun st0 0 a ox oy root
  | step {k : ℕ} {a : FlatHashLifeArena} {ox oy : Int32} {root : UInt32} :
    FlatRun st0 k a ox oy root → (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED →
    FlatRun st0 (k + 1) (a.stepOneGeneration ox oy root).2 (a.stepOneGeneration ox oy root).1.1
      (a.stepOneGeneration ox oy root).1.2.1 (a.stepOneGeneration ox oy root).1.2.2
  | failedStep {k : ℕ} {a : FlatHashLifeArena} {ox oy : Int32} {root : UInt32} :
    FlatRun st0 k a ox oy root → (a.stepOneGeneration ox oy root).1.2.2 = UNCOMPUTED →
    FlatRun st0 k (a.stepOneGeneration ox oy root).2 ox oy root
  | clearOverflow {k : ℕ} {a : FlatHashLifeArena} {ox oy : Int32} {root : UInt32} :
    FlatRun st0 k a ox oy root → FlatRun st0 k a.clearOverflow ox oy root
  | compact {k : ℕ} {a dst : FlatHashLifeArena} {ox oy : Int32} {root : UInt32} :
    FlatRun st0 k a ox oy root → ArenaWF dst → (dst.compactRootFrom a root).1.1 ≠ UNCOMPUTED →
    FlatRun st0 k (dst.compactRootFrom a root).2 ox oy (dst.compactRootFrom a root).1.1

/--
The key of a cell with 32-bit coordinates, as `cellKeyOf` computes it: `x + 2 ^ 31` in the high 32 bits and
`y + 2 ^ 31` in the low 32 bits.
-/
def coordKey (c : Coord) : UInt64 := UInt64.ofNat ((c.1 + 2 ^ 31).toNat * 2 ^ 32 + (c.2 + 2 ^ 31).toNat)

/-- The cell of a key (the inverse of `coordKey`), as `FlatHashLifeCellState.kt` decodes it. -/
def keyCoord (k : UInt64) : Coord := ((k.toNat / 2 ^ 32 : ℕ) - 2 ^ 31, (k.toNat % 2 ^ 32 : ℕ) - 2 ^ 31)

/-- Whether a cell lies in the window `[l, r) × [t, b)`. -/
def InWindow (l t r b : ℤ) (c : Coord) : Prop := l ≤ c.1 ∧ c.1 < r ∧ t ≤ c.2 ∧ c.2 < b

/--
The recursion of `internMacroCellDag` in `FlatHashLifeCellState.kt`. `DagIntern memo a m id memo' a'` holds when
importing `m` into arena `a`, with memo table `memo` (a list of node ↦ id entries), can return `id`, leaving
arena `a'` and memo table `memo'`:
- a memo hit returns the id stored for an equal node;
- otherwise, when `importNeedsChildren m`, the four children are imported first (nw, ne, sw, se, each threading
  the arena and memo table on), then `importMacroCellNode` imports `m` from their ids, and the result is
  memoized.
-/
inductive DagIntern : List (MacroCell × UInt32) → FlatHashLifeArena → MacroCell → UInt32 →
    List (MacroCell × UInt32) → FlatHashLifeArena → Prop
  | hit {memo : List (MacroCell × UInt32)} {a : FlatHashLifeArena} {m : MacroCell} {id : UInt32} :
    (m, id) ∈ memo → DagIntern memo a m id memo a
  | leaf {memo : List (MacroCell × UInt32)} {a : FlatHashLifeArena} {m : MacroCell} :
    importNeedsChildren m = false →
    DagIntern memo a m (a.importMacroCellNode m UNCOMPUTED UNCOMPUTED UNCOMPUTED UNCOMPUTED).1
      ((m, (a.importMacroCellNode m UNCOMPUTED UNCOMPUTED UNCOMPUTED UNCOMPUTED).1) :: memo)
      (a.importMacroCellNode m UNCOMPUTED UNCOMPUTED UNCOMPUTED UNCOMPUTED).2
  | node {memo memo1 memo2 memo3 memo4 : List (MacroCell × UInt32)} {a a1 a2 a3 a4 : FlatHashLifeArena}
    {hh : UInt32} {nw ne sw se : MacroCell} {i1 i2 i3 i4 : UInt32} :
    importNeedsChildren (.cellNode hh nw ne sw se) = true →
    DagIntern memo a nw i1 memo1 a1 → DagIntern memo1 a1 ne i2 memo2 a2 →
    DagIntern memo2 a2 sw i3 memo3 a3 → DagIntern memo3 a3 se i4 memo4 a4 →
    DagIntern memo a (.cellNode hh nw ne sw se) (a4.importMacroCellNode (.cellNode hh nw ne sw se) i1 i2 i3 i4).1
      ((.cellNode hh nw ne sw se, (a4.importMacroCellNode (.cellNode hh nw ne sw se) i1 i2 i3 i4).1) :: memo4)
      (a4.importMacroCellNode (.cellNode hh nw ne sw se) i1 i2 i3 i4).2

/-!
## The cell cursor

The order in which `cellCursorStepWith` enumerates live cells, as folds over the keys of the cells with any
accumulator, and the keys a run of the cursor emits.
-/

/--
Folds `f` from `acc` over the keys (`cellKeyOf`) of the live cells `(x, y)`, among the cells `i ..< 64` (in row-major
order) of the 8x8 leaf `leaf` whose top-left corner is at `(x0, y0)`, that lie in the window `[l, r) × [t, b)`.
-/
def foldLeafCellsLoop {α : Type} (leaf : UInt64) (x0 y0 l t r b : Int64) (f : α → UInt64 → α) (i : UInt32)
    (acc : α) : α :=
  if h : i < 64 then
    have : 64 - (i + 1).toNat < 64 - i.toNat := by
      have h64 : (64 : UInt32).toNat = 64 := rfl
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      rw [h64] at h1
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        simp only [UInt32.toNat_one]
        omega
      omega
    let x := i &&& 7
    let y := i >>> 3
    let cx := x0 + x.toUInt64.toInt64
    let cy := y0 + y.toUInt64.toInt64
    let acc' := if leafContains leaf x y && l <= cx && cx < r && t <= cy && cy < b then f acc (cellKeyOf cx cy)
      else acc
    foldLeafCellsLoop leaf x0 y0 l t r b f (i + 1) acc'
  else acc
termination_by 64 - i.toNat

/--
Folds `f` from `acc` over the keys (`cellKeyOf`) of the live cells `(x, y)` of the Level 4 node `l4Id`, whose top-left
corner is at `(x0, y0)`, that lie in the window `[l, r) × [t, b)`.
-/
def FlatHashLifeArena.foldLevel4Cells {α : Type}
    (arena : FlatHashLifeArena) (l4Id : UInt32) (x0 y0 l t r b : Int64) (f : α → UInt64 → α) (acc : α) : α :=
  if l4Id == 0 || l4Id >= arena.l4Count || r <= x0 || b <= y0 || x0 + 16 <= l || y0 + 16 <= t then acc
  else
    let idx := l4Id.toNat
    let a1 := foldLeafCellsLoop arena.l4Nw[idx]! x0 y0 l t r b f 0 acc
    let a2 := foldLeafCellsLoop arena.l4Ne[idx]! (x0 + 8) y0 l t r b f 0 a1
    let a3 := foldLeafCellsLoop arena.l4Sw[idx]! x0 (y0 + 8) l t r b f 0 a2
    foldLeafCellsLoop arena.l4Se[idx]! (x0 + 8) (y0 + 8) l t r b f 0 a3

/--
Folds `f` from `acc` over the keys (`cellKeyOf`) of the live cells `(x, y)` of the CellNode `nodeId`, whose top-left
corner is at `(x0, y0)`, that lie in the window `[l, r) × [t, b)`, skipping subtrees that miss the window or (up to
level 31) have no live cells.
-/
def FlatHashLifeArena.foldCellsLoop {α : Type}
    (arena : FlatHashLifeArena) (nodeId : UInt32) (x0 y0 l t r b : Int64) (f : α → UInt64 → α) (acc : α)
    (fuel : UInt32) : α :=
  if h : fuel = 0 then acc
  else if nodeId >= arena.cellCount then acc
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!.toUInt32
    if lvl > 62 || (lvl <= 31 && arena.cellPop[idx]! == 0) then acc
    else
      let span := pow2Int64 lvl
      if r <= x0 || b <= y0 || x0 + span <= l || y0 + span <= t then acc
      else
        let half := pow2Int64 (lvl - 1)
        let nw := arena.cellNw[idx]!
        let ne := arena.cellNe[idx]!
        let sw := arena.cellSw[idx]!
        let se := arena.cellSe[idx]!
        if lvl <= 5 then
          let a1 := arena.foldLevel4Cells nw x0 y0 l t r b f acc
          let a2 := arena.foldLevel4Cells ne (x0 + half) y0 l t r b f a1
          let a3 := arena.foldLevel4Cells sw x0 (y0 + half) l t r b f a2
          arena.foldLevel4Cells se (x0 + half) (y0 + half) l t r b f a3
        else
          let a1 := arena.foldCellsLoop nw x0 y0 l t r b f acc (fuel - 1)
          let a2 := arena.foldCellsLoop ne (x0 + half) y0 l t r b f a1 (fuel - 1)
          let a3 := arena.foldCellsLoop sw x0 (y0 + half) l t r b f a2 (fuel - 1)
          arena.foldCellsLoop se (x0 + half) (y0 + half) l t r b f a3 (fuel - 1)
termination_by fuel.toNat

/-- Folds `f` over the cells that a frame of the cell cursor stands for. -/
def FlatHashLifeArena.foldFrame {α : Type} (a : FlatHashLifeArena) (l t r b : Int64) (f : α → UInt64 → α) (acc : α) :
    CellFrame → α
  | .node id x0 y0 fuel => a.foldCellsLoop id x0 y0 l t r b f acc fuel
  | .l4 id x0 y0 => a.foldLevel4Cells id x0 y0 l t r b f acc
  | .leaf bits x0 y0 => foldLeafCellsLoop bits x0 y0 l t r b f 0 acc

/-- Folds `f` over the cells that a stack of the cell cursor stands for, from its top frame down. -/
def FlatHashLifeArena.foldStack {α : Type} (a : FlatHashLifeArena) (l t r b : Int64) (f : α → UInt64 → α) (acc : α)
    (stack : List CellFrame) : α :=
  stack.foldl (a.foldFrame l t r b f) acc

/--
The keys of the cells of a `leafRowMask` chunk of the leaf at `(x0, y0)`, in increasing bit order: what
`FlatHashLifeCellState`'s iterator emits for one step of the cursor.
-/
def chunkKeys (mask : UInt64) (x0 y0 : Int64) : List UInt64 :=
  ((List.range 64).filter (fun k => mask.toBitVec.getLsbD k)).map (fun k => leafChunkKey x0 y0 k.toUInt32)

/--
The keys emitted, and the stack left, by up to `n` calls of the cursor step `step` (such as
`cellCursorStepInWindow`) from `stack`, stopping when the stack is empty, as `FlatHashLifeCellState`'s iterator
runs it.
-/
def cellCursorRun (step : List CellFrame → UInt64 × Int64 × Int64 × List CellFrame) :
    ℕ → List CellFrame → List UInt64 × List CellFrame
  | 0, stack => ([], stack)
  | _ + 1, [] => ([], [])
  | n + 1, frame :: stack =>
    let s := step (frame :: stack)
    let run := cellCursorRun step n s.2.2.2
    (chunkKeys s.1 s.2.1 s.2.2.1 ++ run.1, run.2)

end Algorithm
