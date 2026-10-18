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

  -- Scratch remapping tables for subgraph copying/compaction
  remapL4 : Array UInt32
  remapCell : Array UInt32

  -- Explicit capacity overflow flag (0 = ok, 1 = overflow occurred)
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
Tail-recursive helper to initialize empty nodes for levels 6 through 60 using fixed-width integers.
-/
@[kotlin_member "FlatHashLifeArena" "public" "initEmptyNodesLoop"]
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
Initializes pre-interned empty nodes for levels 4 through 60.
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

@[kotlin_member "FlatHashLifeArena" "public" "clearL4Loop"]
def FlatHashLifeArena.clearL4Loop (arena : FlatHashLifeArena) (fuel : UInt32) (i : UInt32) (cap : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if i >= cap then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let a' := { arena with
      l4Buckets := arena.l4Buckets.set! i.toNat EMPTY_BUCKET,
      l4Next := arena.l4Next.set! i.toNat EMPTY_BUCKET,
      l4HasRes := arena.l4HasRes.set! i.toNat 0
    }
    a'.clearL4Loop (fuel - 1) (i + 1) cap
termination_by fuel.toNat

@[kotlin_member "FlatHashLifeArena" "public" "clearCellLoop"]
def FlatHashLifeArena.clearCellLoop (arena : FlatHashLifeArena) (fuel : UInt32) (i : UInt32) (cap : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if i >= cap then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let a' := { arena with
      cellBuckets := arena.cellBuckets.set! i.toNat EMPTY_BUCKET,
      cellNext := arena.cellNext.set! i.toNat EMPTY_BUCKET,
      cellStepRes := arena.cellStepRes.set! i.toNat UNCOMPUTED
    }
    a'.clearCellLoop (fuel - 1) (i + 1) cap
termination_by fuel.toNat

/--
Resets arena node counts and re-initializes canonical empty nodes.
-/
@[kotlin_member "FlatHashLifeArena" "public" "clear"]
def FlatHashLifeArena.clear (arena : FlatHashLifeArena) : FlatHashLifeArena :=
  let l4Cap := arena.l4Mask + 1
  let cellCap := arena.cellMask + 1
  let a1 := arena.clearL4Loop l4Cap 0 l4Cap
  let a2 := a1.clearCellLoop cellCap 0 cellCap
  let a3 := { a2 with l4Count := 0, cellCount := 0, overflow := 0 }
  a3.initEmptyNodes

/--
Probes the Level 4 hash-consing chain for existing node with given 4 leaves.
-/
def probeLevel4 (arena : FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64) (fuel : UInt32) : Option UInt32 :=
  if h : fuel = 0 then none
  else if head == EMPTY_BUCKET then none
  else if head >= arena.l4Count then none
  else
    let idx := head.toNat
    if arena.l4Nw[idx]! == nw && arena.l4Ne[idx]! == ne &&
       arena.l4Sw[idx]! == sw && arena.l4Se[idx]! == se then
      some head
    else
      let nextHead := arena.l4Next[idx]!
      have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
      probeLevel4 arena nextHead nw ne sw se (fuel - 1)
termination_by fuel.toNat

/--
Interns a Level 4 node (four 8x8 leaves) into the arena, returning its canonical 32-bit NodeId.
Returns the existing NodeId on hit (0 allocations), or allocates a new index on miss.
Sets `overflow := 1` and returns `UNCOMPUTED` if the table is full.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internLevel4"]
def FlatHashLifeArena.internLevel4 (arena : FlatHashLifeArena) (nw ne sw se : UInt64) : UInt32 × FlatHashLifeArena :=
  if nw == 0 && ne == 0 && sw == 0 && se == 0 && arena.l4Count > 0 then
    (0, arena)
  else
    let h := level4Hash nw ne sw se
    let bucket := h &&& arena.l4Mask
    let head := arena.l4Buckets[bucket.toNat]!
    match probeLevel4 arena head nw ne sw se (arena.l4Count + 1) with
    | some id => (id, arena)
    | none =>
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
Probes the CellNode hash-consing chain for existing node with given level and 4 child NodeIds.
-/
def probeCellNode (arena : FlatHashLifeArena) (head : UInt32) (lvl : UInt8) (nw ne sw se : UInt32) (fuel : UInt32) : Option UInt32 :=
  if h : fuel = 0 then none
  else if head == EMPTY_BUCKET then none
  else if head >= arena.cellCount then none
  else
    let idx := head.toNat
    if arena.cellLevel[idx]! == lvl &&
       arena.cellNw[idx]! == nw && arena.cellNe[idx]! == ne &&
       arena.cellSw[idx]! == sw && arena.cellSe[idx]! == se then
      some head
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
Sets `overflow := 1` and returns `UNCOMPUTED` if the table is full.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internCellNode"]
def FlatHashLifeArena.internCellNode (arena : FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) : UInt32 × FlatHashLifeArena :=
  let emptyChild := emptyNodeForLevel (lvl.toUInt32 - 1)
  if lvl >= 5 && lvl <= 60 && arena.cellCount >= 56 &&
     nw == emptyChild && ne == emptyChild && sw == emptyChild && se == emptyChild then
    (emptyNodeForLevel lvl.toUInt32, arena)
  else
    let h := cellNodeHash lvl.toUInt32 nw ne sw se
    let bucket := h &&& arena.cellMask
    let head := arena.cellBuckets[bucket.toNat]!
    match probeCellNode arena head lvl nw ne sw se (arena.cellCount + 1) with
    | some id => (id, arena)
    | none =>
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
Steps a Level 4 node (16x16) to its central 8x8 next generation leaf using memoization in l4StepRes.
-/
@[kotlin_member "FlatHashLifeArena" "public" "stepLevel4"]
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
      let arena' := { arena with
        l4StepRes := arena.l4StepRes.set! idx res,
        l4HasRes := arena.l4HasRes.set! idx 1
      }
      (res, arena')

/--
Extracts the centered subnode of level k-1 from a node of level k.
-/
@[kotlin_member "FlatHashLifeArena" "public" "centeredSubnode"]
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
@[kotlin_member "FlatHashLifeArena" "public" "centeredHorizontal"]
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
@[kotlin_member "FlatHashLifeArena" "public" "centeredVertical"]
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
@[kotlin_member "FlatHashLifeArena" "public" "centeredSubSubnode"]
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
      (popcount64 a + popcount64 b + popcount64 c + popcount64 d).toUInt64
    else
      let nw_se_id := arena.cellSe[nwId.toNat]!
      let ne_sw_id := arena.cellSw[neId.toNat]!
      let sw_ne_id := arena.cellNe[swId.toNat]!
      let se_nw_id := arena.cellNw[seId.toNat]!
      let a_id := arena.cellSe[nw_se_id.toNat]!
      let b_id := arena.cellSw[ne_sw_id.toNat]!
      let c_id := arena.cellNe[sw_ne_id.toNat]!
      let d_id := arena.cellNw[se_nw_id.toNat]!
      arena.cellPop[a_id.toNat]! + arena.cellPop[b_id.toNat]! +
      arena.cellPop[c_id.toNat]! + arena.cellPop[d_id.toNat]!

/--
Checks whether a level >= 5 CellNode requires spatial expansion before stepping.
Matches `MacroCell.needToExpand`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "needToExpandCell"]
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
@[kotlin_member "FlatHashLifeArena" "public" "expandLevel4Centered"]
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
Expands a level k >= 5 CellNode by two levels into a centered level (k + 2) CellNode
surrounded by empty borders. Matches `MacroCell.expandCentered` on `.cellNode`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "expandCentered"]
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
@[kotlin_member "FlatHashLifeArena" "public" "quadrantNW"]
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
@[kotlin_member "FlatHashLifeArena" "public" "quadrantNE"]
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
@[kotlin_member "FlatHashLifeArena" "public" "quadrantSW"]
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
@[kotlin_member "FlatHashLifeArena" "public" "quadrantSE"]
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
@[kotlin_member "FlatHashLifeArena" "public" "stepLevel5"]
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
          let a10 := { a9 with cellStepRes := a9.cellStepRes.set! nodeId.toNat resId }
          (resId, a10)

/--
Combines 4 stepped quadrant results for a level >= 6 node into a level-(k-1) result node in the arena,
and memoizes the result in `cellStepRes[nodeId]`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "combineQuadrants"]
def FlatHashLifeArena.combineQuadrants
    (arena : FlatHashLifeArena) (nodeId : UInt32) (lvl : UInt8) (r_nw r_ne r_sw r_se : UInt32) :
    UInt32 × FlatHashLifeArena :=
  let subLvl := lvl - 1
  let (resId, a1) := arena.internCellNode subLvl r_nw r_ne r_sw r_se
  if a1.overflow == 0 && nodeId < a1.cellCount then
    let a2 := { a1 with cellStepRes := a1.cellStepRes.set! nodeId.toNat resId }
    (resId, a2)
  else
    (UNCOMPUTED, a1)

/--
Sets an entry in `remapL4`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "setRemapL4"]
def FlatHashLifeArena.setRemapL4 (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with remapL4 := arena.remapL4.set! idx.toNat val }

/--
Sets an entry in `remapCell`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "setRemapCell"]
def FlatHashLifeArena.setRemapCell (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with remapCell := arena.remapCell.set! idx.toNat val }

/--
Sets an entry in `cellStepRes`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "setCellStepRes"]
def FlatHashLifeArena.setCellStepRes (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt32) : FlatHashLifeArena :=
  { arena with cellStepRes := arena.cellStepRes.set! idx.toNat val }

/--
Sets an entry in `l4StepRes` and marks `l4HasRes` as 1.
-/
@[kotlin_member "FlatHashLifeArena" "public" "setL4StepRes"]
def FlatHashLifeArena.setL4StepRes (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt64) : FlatHashLifeArena :=
  { arena with
    l4StepRes := arena.l4StepRes.set! idx.toNat val,
    l4HasRes := arena.l4HasRes.set! idx.toNat 1 }

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
Uses an explicit stack in `remapL4` (depth `sp < 128`) so that the function compiles to a flat while-loop
in Kotlin with zero heap or call-stack allocations.
-/
@[kotlin_member "FlatHashLifeArena" "public" "stepCellSerialLoop"]
def FlatHashLifeArena.stepCellSerialLoop
    (arena : FlatHashLifeArena) (sp : UInt32) (fuel : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if sp == 0 || arena.overflow != 0 then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let topIdx := (sp - 1).toNat
    let nodeId := arena.remapL4[topIdx]!
    if nodeId >= arena.cellCount then
      arena.stepCellSerialLoop (sp - 1) (fuel - 1)
    else
      let idx := nodeId.toNat
      if arena.cellStepRes[idx]! != UNCOMPUTED then
        arena.stepCellSerialLoop (sp - 1) (fuel - 1)
      else
        let lvl := arena.cellLevel[idx]!
        if lvl <= 5 then
          let (_, a1) := arena.stepLevel5 nodeId
          a1.stepCellSerialLoop (sp - 1) (fuel - 1)
        else
          let (q_nw, a1) := arena.quadrantNW nodeId
          let (q_ne, a2) := a1.quadrantNE nodeId
          let (q_sw, a3) := a2.quadrantSW nodeId
          let (q_se, a4) := a3.quadrantSE nodeId
          if a4.overflow != 0 then
            a4.stepCellSerialLoop 0 (fuel - 1)
          else
            let r_nw := getCellStepRes a4 q_nw
            let r_ne := getCellStepRes a4 q_ne
            let r_sw := getCellStepRes a4 q_sw
            let r_se := getCellStepRes a4 q_se
            if r_nw == UNCOMPUTED then
              let a5 := a4.setRemapL4 sp q_nw
              a5.stepCellSerialLoop (sp + 1) (fuel - 1)
            else if r_ne == UNCOMPUTED then
              let a5 := a4.setRemapL4 sp q_ne
              a5.stepCellSerialLoop (sp + 1) (fuel - 1)
            else if r_sw == UNCOMPUTED then
              let a5 := a4.setRemapL4 sp q_sw
              a5.stepCellSerialLoop (sp + 1) (fuel - 1)
            else if r_se == UNCOMPUTED then
              let a5 := a4.setRemapL4 sp q_se
              a5.stepCellSerialLoop (sp + 1) (fuel - 1)
            else
              let (_, a5) := a4.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se
              a5.stepCellSerialLoop (sp - 1) (fuel - 1)
termination_by fuel.toNat

/--
Returns `cellLevel[nodeId]` or `0` if out of bounds.
-/
def getCellLevel (arena : @& FlatHashLifeArena) (nodeId : UInt32) : UInt8 :=
  if nodeId < arena.cellCount then
    arena.cellLevel[nodeId.toNat]!
  else
    0

/--
Returns `arena.overflow`.
-/
def getOverflow (arena : @& FlatHashLifeArena) : UInt8 :=
  arena.overflow

/--
Returns `arena.cellCount`.
-/
def getCellCount (arena : @& FlatHashLifeArena) : UInt32 :=
  arena.cellCount

/--
Returns `arena.l4Count`.
-/
def getL4Count (arena : @& FlatHashLifeArena) : UInt32 :=
  arena.l4Count

/--
Zero-allocation recursive HashLife step for a level >= 5 CellNode in the arena, returning its stepped NodeId.
-/
@[kotlin_member "FlatHashLifeArena" "public" "stepCellSerial"]
def FlatHashLifeArena.stepCellSerial
    (arena : FlatHashLifeArena) (nodeId : UInt32) : UInt32 × FlatHashLifeArena :=
  let maxSteps := (arena.cellMask + 1) * 8 + 1024
  let a0 := arena.setRemapL4 0 nodeId
  let a1 := a0.stepCellSerialLoop 1 maxSteps
  let res := if getOverflow a1 != 0 then UNCOMPUTED else getCellStepRes a1 nodeId
  (res, a1)

/--
Prepares a root CellNode (level >= 5) for stepping by expanding by 2 levels if `lvl <= 5`
or if active cells border the outer boundary (`needToExpandCell`).
-/
@[kotlin_member "FlatHashLifeArena" "public" "prepareRootForStep"]
def FlatHashLifeArena.prepareRootForStep
    (arena : FlatHashLifeArena) (rootId : UInt32) : UInt32 × FlatHashLifeArena :=
  if rootId >= arena.cellCount then
    (UNCOMPUTED, arena)
  else
    let lvl := getCellLevel arena rootId
    if lvl <= 5 || arena.needToExpandCell rootId then
      arena.expandCentered rootId
    else
      (rootId, arena)

/--
Advances a simulation root centered at `(ox, oy)` with ID `rootNodeId` by exactly 1 generation
in the arena, handling boundary expansion, offset tracking via `expandOffsetDeltaUInt` and
`stepOffsetDeltaUInt`, and returns `((nextOx, nextOy, nextRootId), arena)`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "stepOneGeneration"]
def FlatHashLifeArena.stepOneGeneration
    (arena : FlatHashLifeArena) (ox oy : Int32) (rootNodeId : UInt32) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  let (prepId, a1) := arena.prepareRootForStep rootNodeId
  if a1.overflow != 0 || prepId == UNCOMPUTED then
    ((ox, oy, UNCOMPUTED), a1)
  else
    let origLvl := a1.cellLevel[rootNodeId.toNat]!
    let (ox1, oy1) :=
      if prepId != rootNodeId then
        let expDelta := expandOffsetDeltaUInt origLvl.toUInt32
        (ox + expDelta, oy + expDelta)
      else
        (ox, oy)
    let currLvl := if prepId != rootNodeId then origLvl + 2 else origLvl
    let stepDelta := stepOffsetDeltaUInt currLvl.toUInt32
    let (nextId, a2) := a1.stepCellSerial prepId
    if a2.overflow != 0 || nextId == UNCOMPUTED then
      ((ox1, oy1, UNCOMPUTED), a2)
    else
      ((ox1 + stepDelta, oy1 + stepDelta, nextId), a2)

/--
Initializes the Level 4 remapping table up to `limit` before a subgraph copy.
-/
@[kotlin_member "FlatHashLifeArena" "public" "initRemapL4Loop"]
def FlatHashLifeArena.initRemapL4Loop
    (arena : FlatHashLifeArena) (fuel : UInt32) (i : UInt32) (limit : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if i >= limit then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let val := if i == 0 then 0 else UNCOMPUTED
    let a' := arena.setRemapL4 i val
    a'.initRemapL4Loop (fuel - 1) (i + 1) limit
termination_by fuel.toNat

/--
Initializes the CellNode remapping table up to `limit` before a subgraph copy.
-/
@[kotlin_member "FlatHashLifeArena" "public" "initRemapCellLoop"]
def FlatHashLifeArena.initRemapCellLoop
    (arena : FlatHashLifeArena) (fuel : UInt32) (i : UInt32) (limit : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if i >= limit then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    let val := if i < 56 then i else UNCOMPUTED
    let a' := arena.setRemapCell i val
    a'.initRemapCellLoop (fuel - 1) (i + 1) limit
termination_by fuel.toNat

/--
Copies a Level 4 node (and optionally its memoized step result) from `src` into `dst`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "copyL4From"]
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
once `cellId` has been remapped.
-/
def copyCellTryStep
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (cellId : UInt32) (copyMemos : Bool) :
    UInt32 × FlatHashLifeArena :=
  let idx := cellId.toNat
  let lvl := src.cellLevel[idx]!
  if src.cellPop[idx]! == 0 && lvl >= 5 && lvl <= 60 then
    let emptyId := lvl.toUInt32 - 5
    (UNCOMPUTED, dst.setRemapCell cellId emptyId)
  else
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
      if getOverflow d4 != 0 then (UNCOMPUTED, d4)
      else
        let (newId, d5) := d4.internCellNode 5 nw ne sw se
        if getOverflow d5 != 0 then (UNCOMPUTED, d5)
        else
          let d6 :=
            if copyMemos && stepRes != UNCOMPUTED then
              let (remappedRes, d5m) := d5.copyL4From src stepRes copyMemos
              if getOverflow d5m == 0 && remappedRes != UNCOMPUTED then
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
        if getOverflow d1 != 0 then (UNCOMPUTED, d1)
        else
          let d2 :=
            if copyMemos && stepRes != UNCOMPUTED && remappedRes != UNCOMPUTED then
              d1.setCellStepRes newId remappedRes
            else d1
          (UNCOMPUTED, d2.setRemapCell cellId newId)

/--
Tail-recursive subgraph copy loop using the upper end of `dst.remapCell` (starting at `stackBase`)
as an explicit DFS stack. Compiles to a flat while-loop in Kotlin with zero heap allocations.
-/
@[kotlin_member "FlatHashLifeArena" "public" "copyCellFromLoop"]
def FlatHashLifeArena.copyCellFromLoop
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (copyMemos : Bool)
    (stackBase : UInt32) (sp : UInt32) (fuel : UInt32) : FlatHashLifeArena :=
  if h : fuel = 0 then dst
  else if sp == 0 || getOverflow dst != 0 then dst
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
      if getOverflow d1 != 0 then
        d1.copyCellFromLoop src copyMemos stackBase 0 (fuel - 1)
      else if missingChild == UNCOMPUTED then
        d1.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
      else
        let d2 := d1.setRemapCell (stackBase + sp) missingChild
        d2.copyCellFromLoop src copyMemos stackBase (sp + 1) (fuel - 1)
termination_by fuel.toNat

/--
Copies the reachable subgraph rooted at `rootId` from `src` into `dst`, optionally preserving step memos,
and stores the remapped root ID at `dst.remapCell[rootId]`.
-/
def copySubgraphInto
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    FlatHashLifeArena :=
  let srcL4 := getL4Count src
  let srcCells := getCellCount src
  let d1 := dst.initRemapL4Loop (srcL4 + 1) 0 srcL4
  let d2 := d1.initRemapCellLoop (srcCells + 1) 0 srcCells
  if rootId >= srcCells then d2
  else
    let stackBase := srcCells
    let d3 := d2.setRemapCell stackBase rootId
    let maxSteps := (srcCells + 1) * 6 + 256
    d3.copyCellFromLoop src copyMemos stackBase 1 maxSteps

/--
Copies the reachable subgraph rooted at `rootId` from `src` into `dst`, optionally preserving step memos.
-/
@[kotlin_member "FlatHashLifeArena" "public" "copySubgraphFrom"]
def FlatHashLifeArena.copySubgraphFrom
    (dst : FlatHashLifeArena) (src : @& FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    UInt32 × FlatHashLifeArena :=
  let d1 := copySubgraphInto dst src rootId copyMemos
  let res :=
    if rootId >= src.cellCount then 0
    else if getOverflow d1 != 0 then UNCOMPUTED
    else getRemapCell d1 rootId
  (res, d1)

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
    ((0, 0), dst)
  else
    let (id1, d1) := dst.copySubgraphFrom src rootId true
    if d1.overflow == 0 && id1 != UNCOMPUTED then
      ((id1, 1), d1)
    else
      let d2 := { d1 with overflow := 0 }
      let (id2, d3) := d2.copySubgraphFrom src rootId false
      ((id2, 0), d3)

/--
Tail-recursive work-stack loop that interns a `MacroCell` tree into the flat arena,
storing the resulting root NodeId at `remapCell[0]`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internMacroCellLoop"]
def FlatHashLifeArena.internMacroCellLoop
    (arena : FlatHashLifeArena) (todo : List (Sum MacroCell UInt8)) (sp : UInt32) (fuel : UInt32) :
    FlatHashLifeArena :=
  if h : fuel = 0 then arena
  else if arena.overflow != 0 then arena
  else
    have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
    match todo with
    | [] => arena
    | item :: rest =>
      match item with
      | .inl (.level4Node _ nw ne sw se) =>
        let (id, a1) := arena.internLevel4 nw ne sw se
        let a2 := a1.setRemapCell sp id
        a2.internMacroCellLoop rest (sp + 1) (fuel - 1)
      | .inl cell@(.cellNode _ nw ne sw se) =>
        let lvl := cell.level
        if cell.size == 0 && lvl >= 5 && lvl <= 60 then
          let a1 := arena.setRemapCell sp (emptyNodeForLevel lvl)
          a1.internMacroCellLoop rest (sp + 1) (fuel - 1)
        else
          let todo' := (.inl nw) :: (.inl ne) :: (.inl sw) :: (.inl se) :: (.inr lvl.toUInt8) :: rest
          arena.internMacroCellLoop todo' sp (fuel - 1)
      | .inr lvl =>
        let nw := getRemapCell arena (sp - 4)
        let ne := getRemapCell arena (sp - 3)
        let sw := getRemapCell arena (sp - 2)
        let se := getRemapCell arena (sp - 1)
        let (id, a1) := arena.internCellNode lvl nw ne sw se
        let a2 := a1.setRemapCell (sp - 4) id
        a2.internMacroCellLoop rest (sp - 3) (fuel - 1)
termination_by fuel.toNat

/--
Interns a `MacroCell` into the flat arena and ensures the returned root is a CellNode at level >= 5.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internMacroCellAsRoot"]
def FlatHashLifeArena.internMacroCellAsRoot
    (arena : FlatHashLifeArena) (m : MacroCell) : UInt32 × FlatHashLifeArena :=
  let maxSteps := (arena.cellMask + 1) * 8 + 4096
  let a1 := arena.internMacroCellLoop [.inl m] 0 maxSteps
  let rawId := getRemapCell a1 0
  if getOverflow a1 != 0 || rawId == UNCOMPUTED then
    (UNCOMPUTED, a1)
  else if m.level == 4 then
    a1.expandLevel4Centered rawId
  else
    (rawId, a1)

/--
Interns a `MacroCell` into the flat arena and returns `(FlatStepResult, arena)`.
If the `MacroCell` is a Level 4 node, it expands it to a centered Level 6 node and shifts
the offset by `expandOffsetDeltaUInt 4`.
-/
@[kotlin_member "FlatHashLifeArena" "public" "internMacroCellWithOffset"]
def FlatHashLifeArena.internMacroCellWithOffset
    (arena : FlatHashLifeArena) (ox oy : Int32) (m : MacroCell) :
    (Int32 × Int32 × UInt32) × FlatHashLifeArena :=
  let (rootId, a1) := arena.internMacroCellAsRoot m
  if a1.overflow != 0 || rootId == UNCOMPUTED then
    ((ox, oy, UNCOMPUTED), a1)
  else if m.level == 4 then
    let expDelta := expandOffsetDeltaUInt 4
    ((ox + expDelta, oy + expDelta, rootId), a1)
  else
    ((ox, oy, rootId), a1)

/--
Tests whether relative coordinates `(rx, ry)` are alive in the CellNode `nodeId` (level >= 5)
using tail-recursive zero-allocation array traversal.
-/
@[kotlin_member "FlatHashLifeArena" "public" "containsCell"]
def FlatHashLifeArena.containsCell
    (arena : @& FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int32) (fuel : UInt32) : Bool :=
  if h : fuel = 0 then false
  else if nodeId >= arena.cellCount then false
  else
    let idx := nodeId.toNat
    if arena.cellPop[idx]! == 0 then false
    else
      let lvl := arena.cellLevel[idx]!.toUInt32.toInt32
      let span : Int32 := (1 : Int32) <<< lvl
      if rx < 0 || ry < 0 || rx >= span || ry >= span then false
      else
        let half : Int32 := (1 : Int32) <<< (lvl - 1)
        let east := rx >= half
        let south := ry >= half
        let rx' := if east then rx - half else rx
        let ry' := if south then ry - half else ry
        let childId :=
          if !east && !south then arena.cellNw[idx]!
          else if east && !south then arena.cellNe[idx]!
          else if !east && south then arena.cellSw[idx]!
          else arena.cellSe[idx]!
        if lvl <= 5 then
          if childId == 0 || childId >= arena.l4Count then false
          else
            let east8 := rx' >= 8
            let south8 := ry' >= 8
            let lx := (if east8 then rx' - 8 else rx').toUInt32
            let ly := (if south8 then ry' - 8 else ry').toUInt32
            let leaf :=
              if !east8 && !south8 then arena.l4Nw[childId.toNat]!
              else if east8 && !south8 then arena.l4Ne[childId.toNat]!
              else if !east8 && south8 then arena.l4Sw[childId.toNat]!
              else arena.l4Se[childId.toNat]!
            leafContains leaf lx ly
        else
          have : (fuel - 1).toNat < fuel.toNat := uint32_sub_one_lt fuel h
          arena.containsCell childId rx' ry' (fuel - 1)
termination_by fuel.toNat

@[kotlin_file]
def flatHashLifeFileSpec : FileSpec := {
  fileAnnotations := #[
    "@file:OptIn(ExperimentalUnsignedTypes::class)"
  ]
  imports := #[
    "import com.alexvanyo.composelife.model.MacroCell",
    "import com.alexvanyo.composelife.model.macroCellLevel",
    "import com.alexvanyo.composelife.model.macroCellSize"
  ]
  items := #[
    .classes,
    .topLevel
  ]
}

end Algorithm
