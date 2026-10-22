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
import Lean.Compiler.Kotlin

open Lean.Compiler.Kotlin
open Algorithm

set_option compiler.kotlin.typedArrays true

namespace Algorithm

def EMPTY_BUCKET : UInt32 := 0xFFFFFFFF
def UNCOMPUTED : UInt32 := 0xFFFFFFFF

/--
A fully flat, zero-allocation memory arena for HashLife.
All quadtree nodes are dense 32-bit integer indices into flat primitive arrays.

The positional `kotlin_types` attribute matches the 24 structure fields in order:
0-4: l4Nw..l4StepRes (ULongArray), 5: l4HasRes (UByteArray), 6-7: l4Buckets..l4Next (UIntArray),
8-9: l4Count..l4Mask (scalars -> _), 10-13: cellNw..cellSe (UIntArray), 14: cellLevel (UByteArray),
15: cellPop (ULongArray), 16-18: cellStepRes..cellNext (UIntArray), 19-20: cellCount..cellMask (scalars -> _),
21-22: remapL4..remapCell (UIntArray), 23: overflow (scalar -> _).
-/
@[mutable_kotlin_class "FlatHashLifeArena",
  kotlin_types "ULongArray" "ULongArray" "ULongArray" "ULongArray" "ULongArray" "UByteArray" "UIntArray" "UIntArray" "_" "_" "UIntArray" "UIntArray" "UIntArray" "UIntArray" "UByteArray" "ULongArray" "UIntArray" "UIntArray" "UIntArray" "_" "_" "UIntArray" "UIntArray" "_"]
structure FlatHashLifeArena where
  -- Level 4 leaf table (16x16 nodes composed of four 8x8 UInt64 leaves)
  l4Nw : Array UInt64
  l4Ne : Array UInt64
  l4Sw : Array UInt64
  l4Se : Array UInt64
  l4StepRes : Array UInt64
  l4HasRes : Array UInt8
  l4Buckets : Array UInt32
  l4Next : Array UInt32
  l4Count : UInt32
  l4Mask : UInt32

  -- Level >= 5 CellNode table (composed of four 32-bit child NodeIds)
  cellNw : Array UInt32
  cellNe : Array UInt32
  cellSw : Array UInt32
  cellSe : Array UInt32
  cellLevel : Array UInt8
  cellPop : Array UInt64
  cellStepRes : Array UInt32
  cellBuckets : Array UInt32
  cellNext : Array UInt32
  cellCount : UInt32
  cellMask : UInt32

  -- Scratch tables: `remapL4` is the step work stack and the Level 4 copy remap table,
  -- `remapCell` is the CellNode copy remap table followed by the copy work stack.
  remapL4 : Array UInt32
  remapCell : Array UInt32

  -- Sticky failure flag (0 = ok, 1 = capacity, step budget, or scratch space exhausted).
  -- Once set, no further structural writes are made to the node tables.
  overflow : UInt8

/--
Returns the pre-interned empty node ID for a given level.
Level 4 empty node is at index 0 in the l4 table.
Level k >= 5 empty node is at index (k - 5) in the cell table.
-/
@[inline]
def emptyNodeForLevel (lvl : UInt32) : UInt32 :=
  if lvl <= 4 then 0 else lvl - 5

/--
`2 ^ k` as an `Int64`, for the small shift amounts used in offset arithmetic.
-/
@[inline]
def pow2Int64 (k : UInt32) : Int64 :=
  ((1 : UInt64) <<< k.toUInt64).toInt64

/--
Checks whether the arena is at or above 75% capacity in either table.
-/
@[kotlin_member "FlatHashLifeArena" "public" "isNearCapacity"]
def FlatHashLifeArena.isNearCapacity (arena : FlatHashLifeArena) : Bool :=
  let l4Cap := arena.l4Mask + 1
  let cellCap := arena.cellMask + 1
  (arena.l4Count * 4 >= l4Cap * 3) || (arena.cellCount * 4 >= cellCap * 3)

/--
Checks whether the arena is at or above 60% capacity in either table.
-/
@[kotlin_member "FlatHashLifeArena" "public" "isOver60Percent"]
def FlatHashLifeArena.isOver60Percent (arena : FlatHashLifeArena) : Bool :=
  let l4Cap := arena.l4Mask + 1
  let cellCap := arena.cellMask + 1
  (arena.l4Count * 5 >= l4Cap * 3) || (arena.cellCount * 5 >= cellCap * 3)

/--
Tail-recursive helper to initialize the pre-interned empty nodes for levels 6 through 60.
-/
def FlatHashLifeArena.initEmptyNodesLoop (arena : FlatHashLifeArena) (fuel : UInt32) (i : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if i >= 56 then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let prev := i - 1
    let idx := i.toNat
    let lvl := (i + 5).toUInt8
    let a' := { arena with
      cellNw := arena.cellNw.set! idx prev,
      cellNe := arena.cellNe.set! idx prev,
      cellSw := arena.cellSw.set! idx prev,
      cellSe := arena.cellSe.set! idx prev,
      cellLevel := arena.cellLevel.set! idx lvl,
      cellPop := arena.cellPop.set! idx 0,
      cellStepRes := arena.cellStepRes.set! idx prev
    }
    a'.initEmptyNodesLoop (fuel - 1) (i + 1)
termination_by fuel.toNat

/--
Initializes the pre-interned empty nodes for levels 4 through 60 in a freshly allocated arena.
-/
@[kotlin_member "FlatHashLifeArena" "public" "initEmptyNodes"]
def FlatHashLifeArena.initEmptyNodes (arena : FlatHashLifeArena) : FlatHashLifeArena :=
  let a2 := { arena with
    l4Nw := arena.l4Nw.set! 0 0,
    l4Ne := arena.l4Ne.set! 0 0,
    l4Sw := arena.l4Sw.set! 0 0,
    l4Se := arena.l4Se.set! 0 0,
    l4StepRes := arena.l4StepRes.set! 0 0,
    l4HasRes := arena.l4HasRes.set! 0 1,
    l4Count := 1,
    cellNw := arena.cellNw.set! 0 0,
    cellNe := arena.cellNe.set! 0 0,
    cellSw := arena.cellSw.set! 0 0,
    cellSe := arena.cellSe.set! 0 0,
    cellLevel := arena.cellLevel.set! 0 5,
    cellPop := arena.cellPop.set! 0 0,
    cellStepRes := arena.cellStepRes.set! 0 0,
    cellCount := 56,
    overflow := 0
  }
  a2.initEmptyNodesLoop 60 1

/--
Probes the Level 4 hash-consing chain for existing node with given 4 leaves, returning its id, or
`EMPTY_BUCKET` if there is none. A found id is below `l4Count`, so it is never `EMPTY_BUCKET`. The result is
an unboxed `UInt32` rather than an `Option`, which would be boxed on every hit in Kotlin.
-/
def probeLevel4 (arena : FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64) (fuel : UInt32) : UInt32 :=
  if h : fuel = 0 then EMPTY_BUCKET
  else if head == EMPTY_BUCKET then EMPTY_BUCKET
  else if head >= arena.l4Count then EMPTY_BUCKET
  else
    let idx := head.toNat
    if arena.l4Nw[idx]! == nw && arena.l4Ne[idx]! == ne &&
       arena.l4Sw[idx]! == sw && arena.l4Se[idx]! == se then
      head
    else
      let nextHead := arena.l4Next[idx]!
      have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
      probeLevel4 arena nextHead nw ne sw se (fuel - 1)
termination_by fuel.toNat

/--
Interns a Level 4 node (four 8x8 leaves) into the arena, returning its canonical 32-bit NodeId.
Returns the existing NodeId on hit (0 allocations), or allocates a new index on miss.
Returns `UNCOMPUTED` (with `overflow` set) if the table is full or the arena has already failed.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internLevel4"]
def FlatHashLifeArena.internLevel4 (arena : FlatHashLifeArena) (nw ne sw se : UInt64) : UInt32 × FlatHashLifeArena :=
  if arena.overflow != 0 then (UNCOMPUTED, arena)
  else if nw == 0 && ne == 0 && sw == 0 && se == 0 && arena.l4Count > 0 then
    (0, arena)
  else
    let h := level4Hash nw ne sw se
    let bucket := h &&& arena.l4Mask
    let head := arena.l4Buckets[bucket.toNat]!
    let found := probeLevel4 arena head nw ne sw se (arena.l4Count + 1)
    if found != EMPTY_BUCKET then (found, arena)
    else
      let id := arena.l4Count
      if id >= arena.l4Mask + 1 then
        (UNCOMPUTED, { arena with overflow := 1 })
      else
        let arena' := { arena with
          l4Nw := arena.l4Nw.set! id.toNat nw,
          l4Ne := arena.l4Ne.set! id.toNat ne,
          l4Sw := arena.l4Sw.set! id.toNat sw,
          l4Se := arena.l4Se.set! id.toNat se,
          l4StepRes := arena.l4StepRes.set! id.toNat 0,
          l4HasRes := arena.l4HasRes.set! id.toNat 0,
          l4Next := arena.l4Next.set! id.toNat head,
          l4Buckets := arena.l4Buckets.set! bucket.toNat id,
          l4Count := id + 1
        }
        (id, arena')

/--
Probes the CellNode hash-consing chain for existing node with given level and 4 child NodeIds, returning its
id, or `EMPTY_BUCKET` if there is none (as `probeLevel4`).
-/
def probeCellNode (arena : FlatHashLifeArena) (head : UInt32) (lvl : UInt8) (nw ne sw se : UInt32) (fuel : UInt32) :
    UInt32 :=
  if h : fuel = 0 then EMPTY_BUCKET
  else if head == EMPTY_BUCKET then EMPTY_BUCKET
  else if head >= arena.cellCount then EMPTY_BUCKET
  else
    let idx := head.toNat
    if arena.cellLevel[idx]! == lvl &&
       arena.cellNw[idx]! == nw && arena.cellNe[idx]! == ne &&
       arena.cellSw[idx]! == sw && arena.cellSe[idx]! == se then
      head
    else
      let nextHead := arena.cellNext[idx]!
      have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
      probeCellNode arena nextHead lvl nw ne sw se (fuel - 1)
termination_by fuel.toNat

/--
Returns the active cell population of a Level 4 node ID in the arena.
-/
@[inline]
def popLevel4Id (arena : FlatHashLifeArena) (id : UInt32) : UInt64 :=
  if id < arena.l4Count then
    let idx := id.toNat
    (popcount64 arena.l4Nw[idx]!).toUInt64 +
    (popcount64 arena.l4Ne[idx]!).toUInt64 +
    (popcount64 arena.l4Sw[idx]!).toUInt64 +
    (popcount64 arena.l4Se[idx]!).toUInt64
  else 0

/--
Returns the active cell population of a CellNode ID in the arena.
-/
@[inline]
def popCellId (arena : FlatHashLifeArena) (id : UInt32) : UInt64 :=
  if id < arena.cellCount then arena.cellPop[id.toNat]! else 0

/--
Calculates total active cell population for a CellNode from its 4 children.
-/
def computePopulation (arena : FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) : UInt64 :=
  if lvl == 5 then
    popLevel4Id arena nw + popLevel4Id arena ne + popLevel4Id arena sw + popLevel4Id arena se
  else
    popCellId arena nw + popCellId arena ne + popCellId arena sw + popCellId arena se

/--
Interns a CellNode (level >= 5) into the arena, returning its canonical 32-bit NodeId.
Returns the existing NodeId on hit (0 allocations), or allocates a new index on miss.
Returns `UNCOMPUTED` (with `overflow` set) if the table is full or the arena has already failed.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internCellNode"]
def FlatHashLifeArena.internCellNode (arena : FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) : UInt32 × FlatHashLifeArena :=
  if arena.overflow != 0 then (UNCOMPUTED, arena)
  else
  let emptyChild := emptyNodeForLevel (lvl.toUInt32 - 1)
  if lvl >= 5 && lvl <= 60 && arena.cellCount >= 56 &&
     nw == emptyChild && ne == emptyChild && sw == emptyChild && se == emptyChild then
    (emptyNodeForLevel lvl.toUInt32, arena)
  else
    let h := cellNodeHash lvl.toUInt32 nw ne sw se
    let bucket := h &&& arena.cellMask
    let head := arena.cellBuckets[bucket.toNat]!
    let found := probeCellNode arena head lvl nw ne sw se (arena.cellCount + 1)
    if found != EMPTY_BUCKET then (found, arena)
    else
      let id := arena.cellCount
      if id >= arena.cellMask + 1 then
        (UNCOMPUTED, { arena with overflow := 1 })
      else
        let pop := computePopulation arena lvl nw ne sw se
        let arena' := { arena with
          cellNw := arena.cellNw.set! id.toNat nw,
          cellNe := arena.cellNe.set! id.toNat ne,
          cellSw := arena.cellSw.set! id.toNat sw,
          cellSe := arena.cellSe.set! id.toNat se,
          cellLevel := arena.cellLevel.set! id.toNat lvl,
          cellPop := arena.cellPop.set! id.toNat pop,
          cellStepRes := arena.cellStepRes.set! id.toNat UNCOMPUTED,
          cellNext := arena.cellNext.set! id.toNat head,
          cellBuckets := arena.cellBuckets.set! bucket.toNat id,
          cellCount := id + 1
        }
        (id, arena')

/--
Sets an entry in `remapL4`.
-/
def FlatHashLifeArena.setRemapL4 (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with remapL4 := arena.remapL4.set! idx.toNat val }

/--
Sets an entry in `remapCell`.
-/
def FlatHashLifeArena.setRemapCell (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with remapCell := arena.remapCell.set! idx.toNat val }

/--
Sets an entry in `cellStepRes`.
-/
def FlatHashLifeArena.setCellStepRes (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with cellStepRes := arena.cellStepRes.set! idx.toNat val }

/--
Sets an entry in `l4StepRes` and marks `l4HasRes` as 1.
-/
def FlatHashLifeArena.setL4StepRes (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt64) : FlatHashLifeArena :=
  { arena with
    l4StepRes := arena.l4StepRes.set! idx.toNat val,
    l4HasRes := arena.l4HasRes.set! idx.toNat 1 }

/--
Sets the sticky `overflow` flag.
-/
def FlatHashLifeArena.setOverflow (arena : FlatHashLifeArena) : FlatHashLifeArena :=
  { arena with overflow := 1 }

/--
Clears the sticky `overflow` flag, keeping every node and memo written so far.
-/
def FlatHashLifeArena.clearOverflow (arena : FlatHashLifeArena) : FlatHashLifeArena :=
  { arena with overflow := 0 }

/--
Steps a Level 4 node (16x16) to its central 8x8 next generation leaf using memoization in l4StepRes.
-/
def FlatHashLifeArena.stepLevel4 (arena : FlatHashLifeArena) (l4Id : UInt32) : UInt64 × FlatHashLifeArena :=
  if l4Id >= arena.l4Count then (0, arena)
  else
    let idx := l4Id.toNat
    if arena.l4HasRes[idx]! == 1 then
      (arena.l4StepRes[idx]!, arena)
    else
      let nw := arena.l4Nw[idx]!
      let ne := arena.l4Ne[idx]!
      let sw := arena.l4Sw[idx]!
      let se := arena.l4Se[idx]!
      let res := computeLevel4NextGen16x16UInt nw ne sw se
      (res, arena.setL4StepRes l4Id res)

/--
Extracts the centered subnode of level k-1 from a node of level k.
-/
def FlatHashLifeArena.centeredSubnode (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let nw_se := arena.l4Se[nwId.toNat]!
      let ne_sw := arena.l4Sw[neId.toNat]!
      let sw_ne := arena.l4Ne[swId.toNat]!
      let se_nw := arena.l4Nw[seId.toNat]!
      arena.internLevel4 nw_se ne_sw sw_ne se_nw
    else
      let nw_se := arena.cellSe[nwId.toNat]!
      let ne_sw := arena.cellSw[neId.toNat]!
      let sw_ne := arena.cellNe[swId.toNat]!
      let se_nw := arena.cellNw[seId.toNat]!
      arena.internCellNode (lvl - 1) nw_se ne_sw sw_ne se_nw

/--
Extracts the horizontal centered subnode spanning west and east nodes.
-/
def FlatHashLifeArena.centeredHorizontal (arena : FlatHashLifeArena) (wId eId : UInt32) : UInt32 × FlatHashLifeArena :=
  if wId >= arena.cellCount || eId >= arena.cellCount then (0, arena)
  else
    let wIdx := wId.toNat
    let eIdx := eId.toNat
    let lvl := arena.cellLevel[wIdx]!
    let w_ne := arena.cellNe[wIdx]!
    let w_se := arena.cellSe[wIdx]!
    let e_nw := arena.cellNw[eIdx]!
    let e_sw := arena.cellSw[eIdx]!
    if lvl == 5 then
      let nw_val := arena.l4Se[w_ne.toNat]!
      let ne_val := arena.l4Sw[e_nw.toNat]!
      let sw_val := arena.l4Ne[w_se.toNat]!
      let se_val := arena.l4Nw[e_sw.toNat]!
      arena.internLevel4 nw_val ne_val sw_val se_val
    else
      let nw_val := arena.cellSe[w_ne.toNat]!
      let ne_val := arena.cellSw[e_nw.toNat]!
      let sw_val := arena.cellNe[w_se.toNat]!
      let se_val := arena.cellNw[e_sw.toNat]!
      arena.internCellNode (lvl - 1) nw_val ne_val sw_val se_val

/--
Extracts the vertical centered subnode spanning north and south nodes.
-/
def FlatHashLifeArena.centeredVertical (arena : FlatHashLifeArena) (nId sId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nId >= arena.cellCount || sId >= arena.cellCount then (0, arena)
  else
    let nIdx := nId.toNat
    let sIdx := sId.toNat
    let lvl := arena.cellLevel[nIdx]!
    let n_sw := arena.cellSw[nIdx]!
    let n_se := arena.cellSe[nIdx]!
    let s_nw := arena.cellNw[sIdx]!
    let s_ne := arena.cellNe[sIdx]!
    if lvl == 5 then
      let nw_val := arena.l4Se[n_sw.toNat]!
      let ne_val := arena.l4Sw[n_se.toNat]!
      let sw_val := arena.l4Ne[s_nw.toNat]!
      let se_val := arena.l4Nw[s_ne.toNat]!
      arena.internLevel4 nw_val ne_val sw_val se_val
    else
      let nw_val := arena.cellSe[n_sw.toNat]!
      let ne_val := arena.cellSw[n_se.toNat]!
      let sw_val := arena.cellNe[s_nw.toNat]!
      let se_val := arena.cellNw[s_ne.toNat]!
      arena.internCellNode (lvl - 1) nw_val ne_val sw_val se_val

/--
Extracts the centered sub-subnode of level k-2 from a node of level k >= 6.
-/
def FlatHashLifeArena.centeredSubSubnode (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    let nw_se := arena.cellSe[nwId.toNat]!
    let ne_sw := arena.cellSw[neId.toNat]!
    let sw_ne := arena.cellNe[swId.toNat]!
    let se_nw := arena.cellNw[seId.toNat]!
    if lvl == 6 then
      let nw_val := arena.l4Se[nw_se.toNat]!
      let ne_val := arena.l4Sw[ne_sw.toNat]!
      let sw_val := arena.l4Ne[sw_ne.toNat]!
      let se_val := arena.l4Nw[se_nw.toNat]!
      arena.internLevel4 nw_val ne_val sw_val se_val
    else
      let nw_val := arena.cellSe[nw_se.toNat]!
      let ne_val := arena.cellSw[ne_sw.toNat]!
      let sw_val := arena.cellNe[sw_ne.toNat]!
      let se_val := arena.cellNw[se_nw.toNat]!
      arena.internCellNode (lvl - 2) nw_val ne_val sw_val se_val

/--
Computes the population of the centered sub-subnode of a level >= 5 CellNode in O(1) without interning.
Matches `MacroCell.centeredSubSubnodeSizeFast`.
-/
def centeredSubSubnodeSizeCell (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt64 :=
  if nodeId >= arena.cellCount then 0
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let nw_se := arena.l4Se[nwId.toNat]!
      let ne_sw := arena.l4Sw[neId.toNat]!
      let sw_ne := arena.l4Ne[swId.toNat]!
      let se_nw := arena.l4Nw[seId.toNat]!
      (popcount64 (centeredSubnodeLevel4 nw_se ne_sw sw_ne se_nw)).toUInt64
    else if lvl == 6 then
      let nw_se_id := arena.cellSe[nwId.toNat]!
      let ne_sw_id := arena.cellSw[neId.toNat]!
      let sw_ne_id := arena.cellNe[swId.toNat]!
      let se_nw_id := arena.cellNw[seId.toNat]!
      let a := arena.l4Se[nw_se_id.toNat]!
      let b := arena.l4Sw[ne_sw_id.toNat]!
      let c := arena.l4Ne[sw_ne_id.toNat]!
      let d := arena.l4Nw[se_nw_id.toNat]!
      (popcount64 a).toUInt64 + (popcount64 b).toUInt64 + (popcount64 c).toUInt64 + (popcount64 d).toUInt64
    else
      let nw_se_id := arena.cellSe[nwId.toNat]!
      let ne_sw_id := arena.cellSw[neId.toNat]!
      let sw_ne_id := arena.cellNe[swId.toNat]!
      let se_nw_id := arena.cellNw[seId.toNat]!
      let a_id := arena.cellSe[nw_se_id.toNat]!
      let b_id := arena.cellSw[ne_sw_id.toNat]!
      let c_id := arena.cellNe[sw_ne_id.toNat]!
      let d_id := arena.cellNw[se_nw_id.toNat]!
      -- At level 7 the great-grandchildren are Level 4 nodes, whose populations are not in `cellPop`.
      if lvl == 7 then
        popLevel4Id arena a_id + popLevel4Id arena b_id + popLevel4Id arena c_id + popLevel4Id arena d_id
      else
        arena.cellPop[a_id.toNat]! + arena.cellPop[b_id.toNat]! +
        arena.cellPop[c_id.toNat]! + arena.cellPop[d_id.toNat]!

/--
Checks whether a level >= 5 CellNode requires spatial expansion before stepping.
Matches `MacroCell.needToExpand`.
-/
def FlatHashLifeArena.needToExpandCell (arena : FlatHashLifeArena) (nodeId : UInt32) : Bool :=
  if nodeId >= arena.cellCount then true
  else
    let subSubPop := centeredSubSubnodeSizeCell arena nodeId
    let totalPop := arena.cellPop[nodeId.toNat]!
    subSubPop != totalPop

/--
Expands a Level 4 node (16x16) by two levels into a centered Level 6 CellNode (64x64)
surrounded by empty borders. Matches `MacroCell.expandCentered` on `.level4Node`.
-/
def FlatHashLifeArena.expandLevel4Centered (arena : FlatHashLifeArena) (l4Id : UInt32) : UInt32 × FlatHashLifeArena :=
  if l4Id >= arena.l4Count then (UNCOMPUTED, arena)
  else
    let idx := l4Id.toNat
    let e4 : UInt32 := 0
    let nw := arena.l4Nw[idx]!
    let (nw_se, a1) := arena.internLevel4 0 0 0 nw
    let ne := a1.l4Ne[idx]!
    let (ne_sw, a2) := a1.internLevel4 0 0 ne 0
    let sw := a2.l4Sw[idx]!
    let (sw_ne, a3) := a2.internLevel4 0 sw 0 0
    let se := a3.l4Se[idx]!
    let (se_nw, a4) := a3.internLevel4 se 0 0 0
    let (q_nw, a5) := a4.internCellNode 5 e4 e4 e4 nw_se
    let (q_ne, a6) := a5.internCellNode 5 e4 e4 ne_sw e4
    let (q_sw, a7) := a6.internCellNode 5 e4 sw_ne e4 e4
    let (q_se, a8) := a7.internCellNode 5 se_nw e4 e4 e4
    a8.internCellNode 6 q_nw q_ne q_sw q_se

/--
Interns a Level 4 node with leaves `nw ne sw se` whose top-left corner is at `(ox, oy)`, expanded to a
centered Level 6 root so that it can be stepped. Returns `((ox', oy', rootId), arena)` where `(ox', oy')` is
the top-left corner of the expanded root. Returns `UNCOMPUTED` with `overflow` set on capacity failure, and
`UNCOMPUTED` with `overflow` unchanged if the expanded offset does not fit in `Int32`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "importLevel4Root"]
def FlatHashLifeArena.importLevel4Root
    (arena : FlatHashLifeArena) (ox oy : Int32) (nw ne sw se : UInt64) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  let nx := ox.toInt64 - 24
  let ny := oy.toInt64 - 24
  if nx < -2147483648 || ny < -2147483648 then ((ox, oy, UNCOMPUTED), arena)
  else
    let (l4Id, a1) := arena.internLevel4 nw ne sw se
    if a1.overflow != 0 then ((ox, oy, UNCOMPUTED), a1)
    else
      let (rootId, a2) := a1.expandLevel4Centered l4Id
      if a2.overflow != 0 then ((ox, oy, UNCOMPUTED), a2)
      else ((nx.toInt32, ny.toInt32, rootId), a2)

/--
Whether `importMacroCellNode` maps `m` directly to a pre-interned empty node: a CellNode of level at most 31
with no live cells (at those levels the cached population cannot wrap around).
-/
def importsAsEmpty (m : MacroCell) : Bool :=
  match m with
  | .level4Node .. => false
  | .cellNode .. => m.size == 0 && m.level <= 31

/--
Whether `importMacroCellNode` needs the ids the children of `m` were imported as: true for every CellNode of
level at most 60 that is not mapped directly to a pre-interned empty node. A node above level 60 is rejected
without importing its children.
-/
@[export import_needs_children]
def importNeedsChildren (m : MacroCell) : Bool :=
  match m with
  | .level4Node .. => false
  | .cellNode .. => !importsAsEmpty m && m.level <= 60

/--
Imports one node of a `MacroCell` DAG into the arena, given the ids its four children were imported as (unused
unless `importNeedsChildren m`). A Level 4 node is interned from its leaves, an empty CellNode maps to its
pre-interned empty node, and any other CellNode is interned from its children's ids. Returns `UNCOMPUTED` if a
child failed to import, if the node is above level 60, or (with `overflow` set) if the arena ran out of capacity.
-/
@[kotlin_member "FlatHashLifeArena" "public" "importMacroCellNode"]
def FlatHashLifeArena.importMacroCellNode
    (arena : FlatHashLifeArena) (m : MacroCell) (nwId neId swId seId : UInt32) : UInt32 × FlatHashLifeArena :=
  match m with
  | .level4Node _ nw ne sw se =>
    let (l4Id, a1) := arena.internLevel4 nw ne sw se
    if a1.overflow != 0 then (UNCOMPUTED, a1) else (l4Id, a1)
  | .cellNode .. =>
    let lvl := m.level
    if importsAsEmpty m then (lvl - 5, arena)
    else if lvl > 60 then (UNCOMPUTED, arena)
    else if nwId == UNCOMPUTED || neId == UNCOMPUTED || swId == UNCOMPUTED || seId == UNCOMPUTED then
      (UNCOMPUTED, arena)
    else
      let (cellId, a1) := arena.internCellNode lvl.toUInt8 nwId neId swId seId
      if a1.overflow != 0 then (UNCOMPUTED, a1) else (cellId, a1)

/--
Expands a level k >= 5 CellNode by two levels into a centered level (k + 2) CellNode
surrounded by empty borders. Matches `MacroCell.expandCentered` on `.cellNode`.
-/
def FlatHashLifeArena.expandCentered (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (UNCOMPUTED, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let ek := emptyNodeForLevel (lvl.toUInt32 - 1)
    let ek1 := emptyNodeForLevel lvl.toUInt32
    let nw := arena.cellNw[idx]!
    let (nw_se, a1) := arena.internCellNode lvl ek ek ek nw
    let ne := a1.cellNe[idx]!
    let (ne_sw, a2) := a1.internCellNode lvl ek ek ne ek
    let sw := a2.cellSw[idx]!
    let (sw_ne, a3) := a2.internCellNode lvl ek sw ek ek
    let se := a3.cellSe[idx]!
    let (se_nw, a4) := a3.internCellNode lvl se ek ek ek
    let (q_nw, a5) := a4.internCellNode (lvl + 1) ek1 ek1 ek1 nw_se
    let (q_ne, a6) := a5.internCellNode (lvl + 1) ek1 ek1 ne_sw ek1
    let (q_sw, a7) := a6.internCellNode (lvl + 1) ek1 sw_ne ek1 ek1
    let (q_se, a8) := a7.internCellNode (lvl + 1) se_nw ek1 ek1 ek1
    a8.internCellNode (lvl + 2) q_nw q_ne q_sw q_se

/--
Returns the NW quadrant of a level >= 5 node ready for recursive stepping.
-/
def FlatHashLifeArena.quadrantNW (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let nw1 := arena.l4Nw[nwId.toNat]!
      let ne1 := arena.l4Ne[nwId.toNat]!
      let sw1 := arena.l4Sw[nwId.toNat]!
      let se1 := arena.l4Se[nwId.toNat]!
      let nw2 := arena.l4Nw[neId.toNat]!
      let sw2 := arena.l4Sw[neId.toNat]!
      let nw3 := arena.l4Nw[swId.toNat]!
      let ne3 := arena.l4Ne[swId.toNat]!
      let nw4 := arena.l4Nw[seId.toNat]!
      let n00 := centeredSubnodeLevel4 nw1 ne1 sw1 se1
      let n01 := centeredSubnodeLevel4 ne1 nw2 se1 sw2
      let n10 := centeredSubnodeLevel4 sw1 se1 nw3 ne3
      let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
      arena.internLevel4 n00 n01 n10 n11
    else
      let (n00, a1) := arena.centeredSubnode nwId
      let (n01, a2) := a1.centeredHorizontal nwId neId
      let (n10, a3) := a2.centeredVertical nwId swId
      let (n11, a4) := a3.centeredSubSubnode nodeId
      a4.internCellNode (lvl - 1) n00 n01 n10 n11

/--
Returns the NE quadrant of a level >= 5 node ready for recursive stepping.
-/
def FlatHashLifeArena.quadrantNE (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let ne1 := arena.l4Ne[nwId.toNat]!
      let se1 := arena.l4Se[nwId.toNat]!
      let nw2 := arena.l4Nw[neId.toNat]!
      let ne2 := arena.l4Ne[neId.toNat]!
      let sw2 := arena.l4Sw[neId.toNat]!
      let se2 := arena.l4Se[neId.toNat]!
      let ne3 := arena.l4Ne[swId.toNat]!
      let nw4 := arena.l4Nw[seId.toNat]!
      let ne4 := arena.l4Ne[seId.toNat]!
      let n01 := centeredSubnodeLevel4 ne1 nw2 se1 sw2
      let n02 := centeredSubnodeLevel4 nw2 ne2 sw2 se2
      let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
      let n12 := centeredSubnodeLevel4 sw2 se2 nw4 ne4
      arena.internLevel4 n01 n02 n11 n12
    else
      let (n01, a1) := arena.centeredHorizontal nwId neId
      let (n02, a2) := a1.centeredSubnode neId
      let (n11, a3) := a2.centeredSubSubnode nodeId
      let (n12, a4) := a3.centeredVertical neId seId
      a4.internCellNode (lvl - 1) n01 n02 n11 n12

/--
Returns the SW quadrant of a level >= 5 node ready for recursive stepping.
-/
def FlatHashLifeArena.quadrantSW (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let sw1 := arena.l4Sw[nwId.toNat]!
      let se1 := arena.l4Se[nwId.toNat]!
      let sw2 := arena.l4Sw[neId.toNat]!
      let nw3 := arena.l4Nw[swId.toNat]!
      let ne3 := arena.l4Ne[swId.toNat]!
      let sw3 := arena.l4Sw[swId.toNat]!
      let se3 := arena.l4Se[swId.toNat]!
      let nw4 := arena.l4Nw[seId.toNat]!
      let sw4 := arena.l4Sw[seId.toNat]!
      let n10 := centeredSubnodeLevel4 sw1 se1 nw3 ne3
      let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
      let n20 := centeredSubnodeLevel4 nw3 ne3 sw3 se3
      let n21 := centeredSubnodeLevel4 ne3 nw4 se3 sw4
      arena.internLevel4 n10 n11 n20 n21
    else
      let (n10, a1) := arena.centeredVertical nwId swId
      let (n11, a2) := a1.centeredSubSubnode nodeId
      let (n20, a3) := a2.centeredSubnode swId
      let (n21, a4) := a3.centeredHorizontal swId seId
      a4.internCellNode (lvl - 1) n10 n11 n20 n21

/--
Returns the SE quadrant of a level >= 5 node ready for recursive stepping.
-/
def FlatHashLifeArena.quadrantSE (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (0, arena)
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!
    let nwId := arena.cellNw[idx]!
    let neId := arena.cellNe[idx]!
    let swId := arena.cellSw[idx]!
    let seId := arena.cellSe[idx]!
    if lvl == 5 then
      let se1 := arena.l4Se[nwId.toNat]!
      let sw2 := arena.l4Sw[neId.toNat]!
      let se2 := arena.l4Se[neId.toNat]!
      let ne3 := arena.l4Ne[swId.toNat]!
      let se3 := arena.l4Se[swId.toNat]!
      let nw4 := arena.l4Nw[seId.toNat]!
      let ne4 := arena.l4Ne[seId.toNat]!
      let sw4 := arena.l4Sw[seId.toNat]!
      let se4 := arena.l4Se[seId.toNat]!
      let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
      let n12 := centeredSubnodeLevel4 sw2 se2 nw4 ne4
      let n21 := centeredSubnodeLevel4 ne3 nw4 se3 sw4
      let n22 := centeredSubnodeLevel4 nw4 ne4 sw4 se4
      arena.internLevel4 n11 n12 n21 n22
    else
      let (n11, a1) := arena.centeredSubSubnode nodeId
      let (n12, a2) := a1.centeredVertical neId seId
      let (n21, a3) := a2.centeredHorizontal swId seId
      let (n22, a4) := a3.centeredSubnode seId
      a4.internCellNode (lvl - 1) n11 n12 n21 n22

/--
Steps a Level 5 CellNode (32x32) by 1 generation to produce its central 16x16 Level 4 NodeId,
memoizing the result in `cellStepRes[nodeId]`.
-/
def FlatHashLifeArena.stepLevel5 (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if nodeId >= arena.cellCount then (UNCOMPUTED, arena)
  else
    let cached := arena.cellStepRes[nodeId.toNat]!
    if cached != UNCOMPUTED then (cached, arena)
    else
      let (q_nw, a1) := arena.quadrantNW nodeId
      let (q_ne, a2) := a1.quadrantNE nodeId
      let (q_sw, a3) := a2.quadrantSW nodeId
      let (q_se, a4) := a3.quadrantSE nodeId
      if a4.overflow != 0 then (UNCOMPUTED, a4)
      else
        let (r_nw, a5) := a4.stepLevel4 q_nw
        let (r_ne, a6) := a5.stepLevel4 q_ne
        let (r_sw, a7) := a6.stepLevel4 q_sw
        let (r_se, a8) := a7.stepLevel4 q_se
        let (resId, a9) := a8.internLevel4 r_nw r_ne r_sw r_se
        if a9.overflow != 0 then (UNCOMPUTED, a9)
        else
          (resId, a9.setCellStepRes nodeId resId)

/--
Combines 4 stepped quadrant results for a level >= 6 node into a level-(k-1) result node in the arena,
and memoizes the result in `cellStepRes[nodeId]`.
-/
def FlatHashLifeArena.combineQuadrants
    (arena : FlatHashLifeArena) (nodeId : UInt32) (lvl : UInt8) (r_nw r_ne r_sw r_se : UInt32) :
    UInt32 × FlatHashLifeArena :=
  let subLvl := lvl - 1
  let (resId, a1) := arena.internCellNode subLvl r_nw r_ne r_sw r_se
  if a1.overflow == 0 && nodeId < a1.cellCount then
    (resId, a1.setCellStepRes nodeId resId)
  else
    (UNCOMPUTED, a1)

/--
Returns `arena.overflow`.
-/
def getOverflow (arena : @& FlatHashLifeArena) : UInt8 :=
  arena.overflow

/--
Returns `cellStepRes[nodeId]` or `UNCOMPUTED` if out of bounds.
-/
def getCellStepRes (arena : @& FlatHashLifeArena) (nodeId : UInt32) : UInt32 :=
  if nodeId < arena.cellCount then
    arena.cellStepRes[nodeId.toNat]!
  else
    UNCOMPUTED

/--
Returns `remapCell[nodeId]` or `UNCOMPUTED` if out of bounds.
-/
def getRemapCell (arena : @& FlatHashLifeArena) (nodeId : UInt32) : UInt32 :=
  if nodeId < arena.remapCell.size.toUInt32 then
    arena.remapCell[nodeId.toNat]!
  else
    UNCOMPUTED

/--
Tail-recursive work-stack loop for zero-allocation serial HashLife stepping of a level >= 5 CellNode.
The explicit stack lives in `remapL4[0 ..< sp]`, so that the function compiles to a flat while-loop
in Kotlin with zero heap or call-stack allocations. The loop stops early when the step budget (`fuel`)
or the stack space runs out; `stepCellSerial` reports that as a failure.
-/
def FlatHashLifeArena.stepCellSerialLoop
    (arena : FlatHashLifeArena) (sp : UInt32) (stackLimit : UInt32) (fuel : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if sp == 0 || arena.overflow != 0 then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let topIdx := (sp - 1).toNat
    let nodeId := arena.remapL4[topIdx]!
    if nodeId >= arena.cellCount then
      arena.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
    else
      let idx := nodeId.toNat
      if arena.cellStepRes[idx]! != UNCOMPUTED then
        arena.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
      else
        let lvl := arena.cellLevel[idx]!
        if lvl <= 5 then
          let (_, a1) := arena.stepLevel5 nodeId
          a1.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
        else
          let (q_nw, a1) := arena.quadrantNW nodeId
          let (q_ne, a2) := a1.quadrantNE nodeId
          let (q_sw, a3) := a2.quadrantSW nodeId
          let (q_se, a4) := a3.quadrantSE nodeId
          if a4.overflow != 0 then
            a4.stepCellSerialLoop 0 stackLimit (fuel - 1)
          else
            let r_nw := getCellStepRes a4 q_nw
            let r_ne := getCellStepRes a4 q_ne
            let r_sw := getCellStepRes a4 q_sw
            let r_se := getCellStepRes a4 q_se
            if r_nw == UNCOMPUTED || r_ne == UNCOMPUTED || r_sw == UNCOMPUTED || r_se == UNCOMPUTED then
              if sp >= stackLimit then
                a4.stepCellSerialLoop 0 stackLimit (fuel - 1)
              else
                let child :=
                  if r_nw == UNCOMPUTED then q_nw
                  else if r_ne == UNCOMPUTED then q_ne
                  else if r_sw == UNCOMPUTED then q_sw
                  else q_se
                let a5 := a4.setRemapL4 sp child
                a5.stepCellSerialLoop (sp + 1) stackLimit (fuel - 1)
            else
              let (_, a5) := a4.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se
              a5.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
termination_by fuel.toNat

/--
Zero-allocation recursive HashLife step for a level >= 5 CellNode in the arena, returning its stepped NodeId.
Returns `UNCOMPUTED` exactly when `overflow` is set: on capacity failure, or if the step budget or stack
space ran out before the result was memoized.
-/
def FlatHashLifeArena.stepCellSerial
    (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  if arena.remapL4.size.toUInt32 == 0 then
    (UNCOMPUTED, arena.setOverflow)
  else
    let maxSteps := (arena.cellMask + 1) * 8 + 1024
    let a0 := arena.setRemapL4 0 nodeId
    let a1 := a0.stepCellSerialLoop 1 arena.remapL4.size.toUInt32 maxSteps
    let res := getCellStepRes a1 nodeId
    if a1.overflow != 0 || res == UNCOMPUTED then (UNCOMPUTED, a1.setOverflow)
    else (res, a1)

/--
Advances a simulation root whose top-left corner is at `(ox, oy)` by exactly 1 generation.

The root is first expanded by two levels if it is at level 5 or has live cells outside its centered
sub-subnode. Returns `((nextOx, nextOy, nextRootId), arena)`. On failure `nextRootId` is `UNCOMPUTED`:
with `overflow` set if the arena ran out of capacity (or step budget or stack space), and with `overflow`
unchanged if `rootNodeId` is not a node, the prepared root would exceed level 30, or the next offset would
not fit in `Int32`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "stepOneGeneration"]
def FlatHashLifeArena.stepOneGeneration
    (arena : FlatHashLifeArena) (ox oy : Int32) (rootNodeId : UInt32) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  if rootNodeId >= arena.cellCount then ((ox, oy, UNCOMPUTED), arena)
  else
    let lvl := arena.cellLevel[rootNodeId.toNat]!.toUInt32
    let expand := lvl <= 5 || arena.needToExpandCell rootNodeId
    let k := if expand then lvl + 2 else lvl
    if k > 30 then ((ox, oy, UNCOMPUTED), arena)
    else
      let delta : Int64 :=
        (if expand then -(3 * pow2Int64 (lvl - 1)) else 0) + pow2Int64 (k - 2)
      let nx := ox.toInt64 + delta
      let ny := oy.toInt64 + delta
      if nx < -2147483648 || nx > 2147483647 || ny < -2147483648 || ny > 2147483647 then
        ((ox, oy, UNCOMPUTED), arena)
      else
        let (prepId, a1) := if expand then arena.expandCentered rootNodeId else (rootNodeId, arena)
        if a1.overflow != 0 then ((ox, oy, UNCOMPUTED), a1)
        else
          let (nextId, a2) := a1.stepCellSerial prepId
          if a2.overflow != 0 then ((ox, oy, UNCOMPUTED), a2)
          else ((nx.toInt32, ny.toInt32, nextId), a2)

/--
Initializes the Level 4 copy remapping table entries `i ..< limit`: the empty Level 4 node maps to
itself and every other entry is `UNCOMPUTED`.
-/
def FlatHashLifeArena.initRemapL4Loop
    (arena : FlatHashLifeArena) (i : UInt32) (limit : UInt32) : FlatHashLifeArena :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let val := if i == 0 then 0 else UNCOMPUTED
    let a' := arena.setRemapL4 i val
    a'.initRemapL4Loop (i + 1) limit
  else arena
termination_by limit.toNat - i.toNat

/--
Initializes the CellNode copy remapping table entries `i ..< limit`: the 56 pre-interned empty nodes
map to themselves and every other entry is `UNCOMPUTED`.
-/
def FlatHashLifeArena.initRemapCellLoop
    (arena : FlatHashLifeArena) (i : UInt32) (limit : UInt32) : FlatHashLifeArena :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let val := if i < 56 then i else UNCOMPUTED
    let a' := arena.setRemapCell i val
    a'.initRemapCellLoop (i + 1) limit
  else arena
termination_by limit.toNat - i.toNat

/--
Copies a Level 4 node (and optionally its memoized step result) from `src` into `dst`.
-/
def FlatHashLifeArena.copyL4From
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (l4Id : UInt32) (copyMemos : Bool) :
    UInt32 × FlatHashLifeArena :=
  if l4Id == 0 || l4Id >= src.l4Count then (0, dst)
  else
    let idx := l4Id.toNat
    let existing := dst.remapL4[idx]!
    if existing != UNCOMPUTED then (existing, dst)
    else
      let (newId, d1) := dst.internLevel4 src.l4Nw[idx]! src.l4Ne[idx]! src.l4Sw[idx]! src.l4Se[idx]!
      if d1.overflow != 0 then (UNCOMPUTED, d1)
      else
        let d2 :=
          if copyMemos && src.l4HasRes[idx]! == 1 then
            d1.setL4StepRes newId src.l4StepRes[idx]!
          else d1
        let d3 := d2.setRemapL4 l4Id newId
        (newId, d3)

/--
Single non-recursive step of copying `cellId` from `src` into `dst`, assuming its children (and optional
memoized step result) have already been remapped in `dst.remapCell` (or are Level 4 nodes).
Returns the first uncopied child `cellId` if one is needed before `cellId` can be interned, or `UNCOMPUTED`
once `cellId` has been remapped (or `overflow` is set).
-/
def copyCellTryStep
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (cellId : UInt32) (copyMemos : Bool) :
    UInt32 × FlatHashLifeArena :=
  let idx := cellId.toNat
  let lvl := src.cellLevel[idx]!
  let nwSrc := src.cellNw[idx]!
  let neSrc := src.cellNe[idx]!
  let swSrc := src.cellSw[idx]!
  let seSrc := src.cellSe[idx]!
  let stepRes := src.cellStepRes[idx]!
  if lvl == 5 then
    let (nw, d1) := dst.copyL4From src nwSrc copyMemos
    let (ne, d2) := d1.copyL4From src neSrc copyMemos
    let (sw, d3) := d2.copyL4From src swSrc copyMemos
    let (se, d4) := d3.copyL4From src seSrc copyMemos
    if d4.overflow != 0 then (UNCOMPUTED, d4)
    else
      let (newId, d5) := d4.internCellNode 5 nw ne sw se
      if d5.overflow != 0 then (UNCOMPUTED, d5)
      else
        let d6 :=
          if copyMemos && stepRes != UNCOMPUTED then
            let (remappedRes, d5m) := d5.copyL4From src stepRes copyMemos
            if d5m.overflow == 0 then
              d5m.setCellStepRes newId remappedRes
            else d5m
          else d5
        (UNCOMPUTED, d6.setRemapCell cellId newId)
  else
    let nw := getRemapCell dst nwSrc
    let ne := getRemapCell dst neSrc
    let sw := getRemapCell dst swSrc
    let se := getRemapCell dst seSrc
    let remappedRes := if copyMemos && stepRes != UNCOMPUTED then getRemapCell dst stepRes else 0
    if nw == UNCOMPUTED then (nwSrc, dst)
    else if ne == UNCOMPUTED then (neSrc, dst)
    else if sw == UNCOMPUTED then (swSrc, dst)
    else if se == UNCOMPUTED then (seSrc, dst)
    else if copyMemos && stepRes != UNCOMPUTED && remappedRes == UNCOMPUTED then (stepRes, dst)
    else
      let (newId, d1) := dst.internCellNode lvl nw ne sw se
      if d1.overflow != 0 then (UNCOMPUTED, d1)
      else
        let d2 :=
          if copyMemos && stepRes != UNCOMPUTED then
            d1.setCellStepRes newId remappedRes
          else d1
        (UNCOMPUTED, d2.setRemapCell cellId newId)

/--
Maximum depth of the explicit copy work stack stored after the remap entries in `remapCell`.
-/
def copyStackDepth : UInt32 := 256

/--
Tail-recursive subgraph copy loop using `dst.remapCell[stackBase ..< stackBase + sp]` as an explicit DFS
stack. Compiles to a flat while-loop in Kotlin with zero heap allocations. The loop stops early when the
step budget (`fuel`) or the stack space runs out; `copySubgraphFrom` reports that as a failure.
-/
def FlatHashLifeArena.copyCellFromLoop
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (copyMemos : Bool)
    (stackBase : UInt32) (sp : UInt32) (fuel : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then dst
  else if sp == 0 || dst.overflow != 0 then dst
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let topPos := stackBase + sp - 1
    let cellId := getRemapCell dst topPos
    if cellId >= src.cellCount then
      dst.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
    else if getRemapCell dst cellId != UNCOMPUTED then
      dst.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
    else
      let (missingChild, d1) := copyCellTryStep dst src cellId copyMemos
      if d1.overflow != 0 then
        d1.copyCellFromLoop src copyMemos stackBase 0 (fuel - 1)
      else if missingChild == UNCOMPUTED then
        d1.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
      else if sp >= copyStackDepth then
        d1.copyCellFromLoop src copyMemos stackBase 0 (fuel - 1)
      else
        let d2 := d1.setRemapCell (stackBase + sp) missingChild
        d2.copyCellFromLoop src copyMemos stackBase (sp + 1) (fuel - 1)
termination_by fuel.toNat

/--
Whether `dst` has enough scratch space to copy any subgraph of `src`: every Level 4 id of `src` fits in
`dst.remapL4`, and every CellNode id of `src` plus the copy work stack fits in `dst.remapCell`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "canCopySubgraphFrom"]
def FlatHashLifeArena.canCopySubgraphFrom (dst : @& FlatHashLifeArena) (src : @& FlatHashLifeArena) : Bool :=
  let remapCellSize := dst.remapCell.size.toUInt32
  src.l4Count <= dst.remapL4.size.toUInt32 &&
    remapCellSize >= copyStackDepth &&
    src.cellCount <= remapCellSize - copyStackDepth

/--
Copies the reachable subgraph rooted at `rootId` from `src` into `dst`, optionally preserving step memos,
and stores the remapped root ID at `dst.remapCell[rootId]`. Sets `overflow` if `dst` lacks the scratch
space to copy from `src`.
-/
def copySubgraphInto
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    FlatHashLifeArena :=
  if !dst.canCopySubgraphFrom src then dst.setOverflow
  else
    let srcCells := src.cellCount
    let d1 := dst.initRemapL4Loop 0 src.l4Count
    let d2 := d1.initRemapCellLoop 0 srcCells
    if rootId >= srcCells then d2
    else
      let stackBase := srcCells
      let d3 := d2.setRemapCell stackBase rootId
      let maxSteps := (srcCells + 1) * 6 + 256
      d3.copyCellFromLoop src copyMemos stackBase 1 maxSteps

/--
Copies the reachable subgraph rooted at `rootId` from `src` into `dst`, optionally preserving step memos.
Returns `UNCOMPUTED` exactly when `overflow` is set: on capacity failure, missing scratch space, or if the
step budget or stack space ran out before the root was copied.
-/
@[kotlin_member "FlatHashLifeArena" "public" "copySubgraphFrom"]
def FlatHashLifeArena.copySubgraphFrom
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    UInt32 × FlatHashLifeArena :=
  let d1 := copySubgraphInto dst src rootId copyMemos
  let res := if rootId >= src.cellCount then UNCOMPUTED else getRemapCell d1 rootId
  if getOverflow d1 != 0 || res == UNCOMPUTED then (UNCOMPUTED, d1.setOverflow)
  else (res, d1)

/--
Compacts `rootId` from `src` into `dst`. Attempts copying with memoized step results first.
If copying with memos overflows `dst`, clears overflow and falls back to clean copying without memos.
Returns `((newRootId, hasMemos), dst)`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "compactRootFrom"]
def FlatHashLifeArena.compactRootFrom
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (rootId : UInt32) :
    (UInt32 × UInt8) × FlatHashLifeArena :=
  if rootId >= src.cellCount || src.overflow != 0 then
    ((UNCOMPUTED, 0), dst)
  else
    let (id1, d1) := dst.copySubgraphFrom src rootId true
    if d1.overflow == 0 then
      ((id1, 1), d1)
    else
      let d2 := d1.clearOverflow
      let (id2, d3) := d2.copySubgraphFrom src rootId false
      ((id2, 0), d3)

/--
Whether relative coordinates `(rx, ry)`, within `[0, 16)`, are alive in the Level 4 node `l4Id`.
-/
@[inline]
def containsLevel4 (arena : @& FlatHashLifeArena) (l4Id : UInt32) (rx ry : Int64) : Bool :=
  if l4Id == 0 || l4Id >= arena.l4Count then false
  else
    let east := rx >= 8
    let south := ry >= 8
    let lx := (if east then rx - 8 else rx).toUInt64.toUInt32
    let ly := (if south then ry - 8 else ry).toUInt64.toUInt32
    let i := l4Id.toNat
    let leaf :=
      if south then (if east then arena.l4Se[i]! else arena.l4Sw[i]!)
      else (if east then arena.l4Ne[i]! else arena.l4Nw[i]!)
    leafContains leaf lx ly

/--
Tail-recursive zero-allocation traversal for `containsCell`: whether relative coordinates `(rx, ry)` are alive
in the CellNode `nodeId` (level >= 5). Nodes of level 63 or more are wider than any `Int64` coordinate, so for
them only the sign of the coordinates is checked and the west/north halves are always taken.
-/
def FlatHashLifeArena.containsCellLoop
    (arena : @& FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) (fuel : UInt32) : Bool :=
  if h : fuel = 0 then false
  else if nodeId >= arena.cellCount then false
  else
    let idx := nodeId.toNat
    let lvl := arena.cellLevel[idx]!.toUInt32
    if rx < 0 || ry < 0 || (lvl < 63 && (rx >= pow2Int64 lvl || ry >= pow2Int64 lvl)) then false
    else
      let half := pow2Int64 (lvl - 1)
      let east := lvl <= 63 && rx >= half
      let south := lvl <= 63 && ry >= half
      let rx' := if east then rx - half else rx
      let ry' := if south then ry - half else ry
      let childId :=
        if south then (if east then arena.cellSe[idx]! else arena.cellSw[idx]!)
        else (if east then arena.cellNe[idx]! else arena.cellNw[idx]!)
      if lvl <= 5 then containsLevel4 arena childId rx' ry'
      else
        have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
        arena.containsCellLoop childId rx' ry' (fuel - 1)
termination_by fuel.toNat

/--
Whether relative coordinates `(rx, ry)` (from the top-left corner) are alive in the CellNode `nodeId`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "containsCell"]
def FlatHashLifeArena.containsCell (arena : @& FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) : Bool :=
  arena.containsCellLoop nodeId rx ry 256

/--
The key of the cell `(x, y)` with 32-bit coordinates: `x + 2 ^ 31` in the high 32 bits and `y + 2 ^ 31` in the low
32 bits.
-/
@[inline]
def cellKeyOf (x y : Int64) : UInt64 :=
  ((x + 2147483648).toUInt64 <<< 32) + (y + 2147483648).toUInt64

/--
The cells `i ..< 64` (in row-major order) of the 8x8 leaf `leaf`, whose top-left corner is at `(x0, y0)`, that are
live and lie in the window `[l, r) × [t, b)`, as a mask with bit `y * 8 + x` set for the live cell `(x, y)`.
-/
def leafRowMask (leaf : UInt64) (x0 y0 l t r b : Int64) (i : UInt32) : UInt64 :=
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
    let rest := leafRowMask leaf x0 y0 l t r b (i + 1)
    if leafContains leaf x y && l <= cx && cx < r && t <= cy && cy < b then rest ||| (1 <<< i.toUInt64) else rest
  else 0
termination_by 64 - i.toNat

/--
The key (`cellKeyOf`) of cell `k` (in row-major order, `k < 64`) of the 8x8 leaf whose top-left corner is at
`(x0, y0)`: the cell `(x0 + k % 8, y0 + k / 8)`.
-/
@[export leaf_chunk_key]
def leafChunkKey (x0 y0 : Int64) (k : UInt32) : UInt64 :=
  cellKeyOf (x0 + (k &&& 7).toUInt64.toInt64) (y0 + (k >>> 3).toUInt64.toInt64)

/--
A pending piece of a cell enumeration: a CellNode (with the recursion depth left), a Level 4 node, or a leaf, each
with its top-left corner `(x0, y0)`.
-/
@[kotlin_class "sealed class CellFrame"]
inductive CellFrame where
  | node (id : UInt32) (x0 y0 : Int64) (fuel : UInt32)
  | l4 (id : UInt32) (x0 y0 : Int64)
  | leaf (bits : UInt64) (x0 y0 : Int64)

/-- Pushes the leaf frame of `bits` at `(x0, y0)` onto `rest`, unless the leaf has no live cells. -/
@[inline]
def pushLeafFrame (bits : UInt64) (x0 y0 : Int64) (rest : List CellFrame) : List CellFrame :=
  if bits == 0 then rest else .leaf bits x0 y0 :: rest

/--
One step of the enumeration of the live cells in the window `[l, r) × [t, b)`: pops the top frame of `stack` and
either pushes its pieces or emits the cells of one leaf. Returns the emitted cells as a `leafRowMask` (zero if none)
with the leaf's top-left corner, and the new stack. Subtrees that miss the window or (up to level 31) have no live
cells, and empty leaves, are skipped.
-/
def FlatHashLifeArena.cellCursorStepWith (arena : @& FlatHashLifeArena) (l t r b : Int64) (stack : @& List CellFrame) :
    UInt64 × Int64 × Int64 × List CellFrame :=
  match stack with
  | [] => (0, 0, 0, [])
  | .node id x0 y0 fuel :: rest =>
    if fuel == 0 || id >= arena.cellCount then (0, 0, 0, rest)
    else
      let idx := id.toNat
      let lvl := arena.cellLevel[idx]!.toUInt32
      if lvl > 62 || (lvl <= 31 && arena.cellPop[idx]! == 0) then (0, 0, 0, rest)
      else
        let span := pow2Int64 lvl
        if r <= x0 || b <= y0 || x0 + span <= l || y0 + span <= t then (0, 0, 0, rest)
        else
          let half := pow2Int64 (lvl - 1)
          let nw := arena.cellNw[idx]!
          let ne := arena.cellNe[idx]!
          let sw := arena.cellSw[idx]!
          let se := arena.cellSe[idx]!
          if lvl <= 5 then
            (0, 0, 0, .l4 nw x0 y0 :: .l4 ne (x0 + half) y0 :: .l4 sw x0 (y0 + half) ::
              .l4 se (x0 + half) (y0 + half) :: rest)
          else
            (0, 0, 0, .node nw x0 y0 (fuel - 1) :: .node ne (x0 + half) y0 (fuel - 1) ::
              .node sw x0 (y0 + half) (fuel - 1) :: .node se (x0 + half) (y0 + half) (fuel - 1) :: rest)
  | .l4 id x0 y0 :: rest =>
    if id == 0 || id >= arena.l4Count || r <= x0 || b <= y0 || x0 + 16 <= l || y0 + 16 <= t then (0, 0, 0, rest)
    else
      let idx := id.toNat
      (0, 0, 0, pushLeafFrame arena.l4Nw[idx]! x0 y0 (pushLeafFrame arena.l4Ne[idx]! (x0 + 8) y0
        (pushLeafFrame arena.l4Sw[idx]! x0 (y0 + 8) (pushLeafFrame arena.l4Se[idx]! (x0 + 8) (y0 + 8) rest))))
  | .leaf bits x0 y0 :: rest => (leafRowMask bits x0 y0 l t r b 0, x0, y0, rest)

/-- The stack that starts the enumeration of the live cells of the CellNode `rootId` with top-left corner `(ox, oy)`. -/
@[kotlin_member "FlatHashLifeArena" "public" "cellCursorStart"]
def FlatHashLifeArena.cellCursorStart (_arena : @& FlatHashLifeArena) (rootId : UInt32) (ox oy : Int32) :
    List CellFrame :=
  [.node rootId ox.toInt64 oy.toInt64 64]

/-- Whether an enumeration stack is exhausted. -/
@[export cell_cursor_done]
def cellCursorDone (stack : List CellFrame) : Bool := stack.isEmpty

/--
One step (`cellCursorStepWith`) of the enumeration of the live cells in the window `[l, r) × [t, b)`, the iterator
of `FlatHashLifeCellState.getAliveCellsInWindow`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "cellCursorStepInWindow"]
def FlatHashLifeArena.cellCursorStepInWindow (arena : @& FlatHashLifeArena) (l t r b : Int32)
    (stack : @& List CellFrame) : UInt64 × Int64 × Int64 × List CellFrame :=
  arena.cellCursorStepWith l.toInt64 t.toInt64 r.toInt64 b.toInt64 stack

/--
One step (`cellCursorStepWith`) of the enumeration of the live cells with 32-bit coordinates, the iterator of
`FlatHashLifeCellState.aliveCells`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "cellCursorStepAll"]
def FlatHashLifeArena.cellCursorStepAll (arena : @& FlatHashLifeArena) (stack : @& List CellFrame) :
    UInt64 × Int64 × Int64 × List CellFrame :=
  arena.cellCursorStepWith (-2147483648) (-2147483648) 2147483648 2147483648 stack

/--
One step (`cellCursorStepWith`) of the enumeration of the live cells with `x ≥ 2 ^ 31`, which have no 32-bit
coordinates; used by `FlatHashLifeCellState.fitsInIntRange`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "cellCursorStepPastX"]
def FlatHashLifeArena.cellCursorStepPastX (arena : @& FlatHashLifeArena) (stack : @& List CellFrame) :
    UInt64 × Int64 × Int64 × List CellFrame :=
  arena.cellCursorStepWith 2147483648 (-9223372036854775808) 9223372036854775807 9223372036854775807 stack

/--
One step (`cellCursorStepWith`) of the enumeration of the live cells with `y ≥ 2 ^ 31`, which have no 32-bit
coordinates; used by `FlatHashLifeCellState.fitsInIntRange`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "cellCursorStepPastY"]
def FlatHashLifeArena.cellCursorStepPastY (arena : @& FlatHashLifeArena) (stack : @& List CellFrame) :
    UInt64 × Int64 × Int64 × List CellFrame :=
  arena.cellCursorStepWith (-9223372036854775808) 2147483648 9223372036854775807 9223372036854775807 stack

/-- The high 32 bits of a key. -/
@[inline]
def keyHi (k : UInt64) : UInt64 := k >>> 32

/-- The low 32 bits of a key. -/
@[inline]
def keyLo (k : UInt64) : UInt64 := k &&& 0xFFFFFFFF

set_option compiler.kotlin.typedArrays false in
/--
The bounding box `(minX, minY, maxX, maxY)`, in key coordinates, of the cell keys `i ..< limit` of `cells`, started
from the box `minX ..= maxX`, `minY ..= maxY`.
-/
def cellBoundsLoop (cells : Array UInt64) (i limit : UInt32) (minX minY maxX maxY : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let k := cells[i.toNat]!
    cellBoundsLoop cells (i + 1) limit (min minX (keyHi k)) (min minY (keyLo k)) (max maxX (keyHi k))
      (max maxY (keyLo k))
  else (minX, minY, maxX, maxY)
termination_by limit.toNat - i.toNat

set_option compiler.kotlin.typedArrays false in
/--
Adds to `acc` the keys, relative to the corner `(minX, minY)` (in key coordinates), of the cell keys `i ..< limit` of
`cells`.
-/
def relativeKeysLoop (cells : Array UInt64) (i limit : UInt32) (minX minY : UInt64) (acc : List UInt64) :
    List UInt64 :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let k := cells[i.toNat]!
    relativeKeysLoop cells (i + 1) limit minX minY (((((keyHi k) - minX) <<< 32) + ((keyLo k) - minY)) :: acc)
  else acc
termination_by limit.toNat - i.toNat

/--
Splits `keys` into the keys of the four quadrants split at `(midX, midY)` in one pass, prepending them to
`nw`, `ne`, `sw` and `se`.
-/
def splitKeys (keys : List UInt64) (midX midY : UInt64) (nw ne sw se : List UInt64) :
    List UInt64 × List UInt64 × List UInt64 × List UInt64 :=
  match keys with
  | [] => (nw, ne, sw, se)
  | k :: rest =>
    if keyLo k ≥ midY then
      if keyHi k ≥ midX then splitKeys rest midX midY nw ne sw (k :: se)
      else splitKeys rest midX midY nw ne (k :: sw) se
    else if keyHi k ≥ midX then splitKeys rest midX midY nw (k :: ne) sw se
    else splitKeys rest midX midY (k :: nw) ne sw se

/--
Sets in `leaf` the cells of the keys of `keys` that lie in the 8x8 leaf whose top-left corner is at `(x0, y0)`.
-/
def leafFromKeys (keys : List UInt64) (x0 y0 : UInt64) (leaf : UInt64) : UInt64 :=
  match keys with
  | [] => leaf
  | k :: rest =>
    let kx := keyHi k
    let ky := keyLo k
    leafFromKeys rest x0 y0
      (if x0 <= kx && kx < x0 + 8 && y0 <= ky && ky < y0 + 8 then
        leafWithCell leaf (kx - x0).toUInt32 (ky - y0).toUInt32 true
      else leaf)

/--
The empty MacroCell of height `h` (level `h + 4`).
-/
def emptyAtHeight (h : UInt32) : MacroCell :=
  if hh : h = 0 then emptyLevel4
  else
    have : (h - 1).toNat < h.toNat := uint32_sub_one_lt h hh
    let e := emptyAtHeight (h - 1)
    makeCellNode e e e e
termination_by h.toNat

/-- The north-west child of a CellNode, which for an empty node is the empty node one level down. -/
def nwChild (m : MacroCell) : MacroCell :=
  match m with
  | .cellNode _ nw _ _ _ => nw
  | _ => m

/--
The MacroCell of height `h` (level `h + 4`) whose top-left corner is at key coordinates `(x0, y0)` and whose live
cells are exactly the cells of `keys` (all of which lie in it), given the empty node `empty` of height `h`, which
every empty quadrant shares.
-/
def keysToMacroCell (keys : List UInt64) (x0 y0 : UInt64) (h : UInt32) (empty : MacroCell) : MacroCell :=
  match keys with
  | [] => empty
  | _ :: _ =>
    if hh : h = 0 then
      makeLevel4Node (leafFromKeys keys x0 y0 0) (leafFromKeys keys (x0 + 8) y0 0)
        (leafFromKeys keys x0 (y0 + 8) 0) (leafFromKeys keys (x0 + 8) (y0 + 8) 0)
    else
      have : (h - 1).toNat < h.toNat := uint32_sub_one_lt h hh
      let half := (1 : UInt64) <<< (h + 3).toUInt64
      let midX := x0 + half
      let midY := y0 + half
      let parts := splitKeys keys midX midY [] [] [] []
      let e := nwChild empty
      makeCellNode
        (keysToMacroCell parts.1 x0 y0 (h - 1) e)
        (keysToMacroCell parts.2.1 midX y0 (h - 1) e)
        (keysToMacroCell parts.2.2.1 x0 midY (h - 1) e)
        (keysToMacroCell parts.2.2.2 midX midY (h - 1) e)
termination_by h.toNat

/--
The smallest level `L` with `lvl ≤ L ≤ 32` and `span ≤ 2 ^ L`.
-/
def levelForSpanLoop (span : UInt64) (lvl : UInt32) : UInt32 :=
  if h : lvl < 32 ∧ (1 : UInt64) <<< lvl.toUInt64 < span then
    have : 32 - (lvl + 1).toNat < 32 - lvl.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h.1
      have h32 : (32 : UInt32).toNat = 32 := rfl
      rw [h32] at h1
      have h2 : (lvl + 1).toNat = lvl.toNat + 1 := by
        rw [UInt32.toNat_add]
        simp only [UInt32.toNat_one]
        omega
      omega
    levelForSpanLoop span (lvl + 1)
  else lvl
termination_by 32 - lvl.toNat

set_option compiler.kotlin.typedArrays false in
/--
The quadtree of the cells whose keys (`cellKeyOf`) are `cells`, with its top-left corner at the corner of their
bounding box, at the smallest level (at least 5) that holds them: `(ox, oy, macroCell)`, with the corner in key
coordinates. No cells give the empty Level 5 node at the origin (key coordinates `(2 ^ 31, 2 ^ 31)`).
`buildQuadtreeBottomUp` in `FlatHashLifeCellState.kt` imports the result into an arena with `internMacroCellDag`.
-/
@[export flat_cells_to_macro_cell]
def cellsToMacroCell (cells : Array UInt64) : UInt64 × UInt64 × MacroCell :=
  let n := cells.size.toUInt32
  if n == 0 then (2147483648, 2147483648, emptyAtHeight 1)
  else
    let k := cells[0]!
    let (minX, minY, maxX, maxY) := cellBoundsLoop cells 1 n (keyHi k) (keyLo k) (keyHi k) (keyLo k)
    let span := max (maxX - minX) (maxY - minY) + 1
    let lvl := levelForSpanLoop span 5
    (minX, minY,
      keysToMacroCell (relativeKeysLoop cells 0 n minX minY []) 0 0 (lvl - 4) (emptyAtHeight (lvl - 4)))

@[kotlin_file]
def flatHashLifeFileSpec : FileSpec := {
  fileAnnotations := #[
    "@file:OptIn(ExperimentalUnsignedTypes::class)"
  ]
  imports := #[
    "import com.alexvanyo.composelife.model.MacroCell",
    "import com.alexvanyo.composelife.model.emptyLevel4",
    "import com.alexvanyo.composelife.model.macroCellHashCode",
    "import com.alexvanyo.composelife.model.macroCellLevel",
    "import com.alexvanyo.composelife.model.macroCellSize"
  ]
  items := #[
    .classes,
    .topLevel
  ]
}

end Algorithm
