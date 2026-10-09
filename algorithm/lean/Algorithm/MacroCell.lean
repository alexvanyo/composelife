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
import Algorithm.MacroCellHash
import Algorithm.Cache
import Lean.Compiler.Kotlin

open Lean.Compiler.Kotlin

local notation "ℕ" => Nat

namespace Algorithm

/--
A leaf MacroCell containing 64 cells encoded in a 64-bit word in Morton (Z-order) layout.
Matches MacroCell.LeafNode = Long in Kotlin.
-/
abbrev LeafNode := UInt64

/--
SWAR population count for 64-bit Morton leaf words.
Computes the exact number of active cells in O(1) bitwise operations.
-/
def popcount64 (x : UInt64) : UInt32 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h01 : UInt64 := 0x0101010101010101
  let x1 := x - ((x >>> 1) &&& m1)
  let x2 := (x1 &&& m2) + ((x1 >>> 2) &&& m2)
  let x3 := (x2 + (x2 >>> 4)) &&& m4
  let x4 := (x3 * h01) >>> 56
  x4.toUInt32

/--
A quadtree representation of the state of cells, matching Kotlin's `MacroCell`.
A `MacroCell` is either:
- A `Level4Node` with 4 64-bit `LeafNode` quadrants (16x16 cells).
- A `CellNode` with 4 subnodes of equal level >= 4 (representing 2^(k+1) x 2^(k+1) cells).
-/
@[kotlin_class "data sealed interface MacroCell"]
inductive MacroCell where
  | level4Node (nw ne sw se : UInt64) : MacroCell
  | cellNode (nw ne sw se : MacroCell) : MacroCell
deriving DecidableEq

/--
The tree level of this cell. A cell at level `k` represents 2^k x 2^k cells.
Minimum level is 4.
-/
@[export macrocell_level]
def MacroCell.level : MacroCell → UInt32
  | .level4Node _ _ _ _ => 4
  | .cellNode nw _ _ _ => nw.level + 1

/--
The number of alive cells represented by this MacroCell.
-/
@[export macrocell_size]
def MacroCell.size : MacroCell → UInt32
  | .level4Node nw ne sw se => popcount64 nw + popcount64 ne + popcount64 sw + popcount64 se
  | .cellNode nw ne sw se => nw.size + ne.size + sw.size + se.size

/--
The memoized hashcode for MacroCell matching MacroCellHash.lean.
Level4Node uses Stafford's Mix13 hash on the 4 leaves.
CellNode uses MurmurHash3 fmix32 on level and the 4 child hashes.
-/
@[export macrocell_hash_code]
def MacroCell.cellHashCode : MacroCell → UInt32
  | .level4Node nw ne sw se => level4Hash nw ne sw se
  | .cellNode nw ne sw se => cellNodeHash (nw.level + 1) nw.cellHashCode ne.cellHashCode sw.cellHashCode se.cellHashCode

/--
An empty (all dead) level 4 MacroCell.
-/
def emptyLevel4 : MacroCell :=
  .level4Node 0 0 0 0

/--
Creates an empty MacroCell at level k (k >= 4).
For levels <= 4, returns an empty level 4 node.
-/
def emptyNode : ℕ → MacroCell
  | 0 => emptyLevel4
  | 1 => emptyLevel4
  | 2 => emptyLevel4
  | 3 => emptyLevel4
  | 4 => emptyLevel4
  | k + 5 =>
    let sub := emptyNode (k + 4)
    .cellNode sub sub sub sub

/--
Extracts the center 8x8 leaf from a 16x16 Level 4 node.
In quadtree coordinates: nw = nw.se, ne = ne.sw, sw = sw.ne, se = se.nw.
-/
def centeredSubnodeLevel4 (nw ne sw se : UInt64) : UInt64 :=
  let nw_se := (nw >>> 48).toUInt32 &&& 0xFFFF
  let ne_sw := (ne >>> 32).toUInt32 &&& 0xFFFF
  let sw_ne := (sw >>> 16).toUInt32 &&& 0xFFFF
  let se_nw := se.toUInt32 &&& 0xFFFF
  (nw_se.toUInt64) |||
  (ne_sw.toUInt64 <<< 16) |||
  (sw_ne.toUInt64 <<< 32) |||
  (se_nw.toUInt64 <<< 48)

/--
Extracts the center subnode of level k-1 from a level k CellNode.
In quadtree coordinates, the center consists of:
  nw = nw.se, ne = ne.sw, sw = sw.ne, se = se.nw
-/
def centeredSubnode : MacroCell → MacroCell
  | .cellNode (.cellNode _ _ _ nw_se) (.cellNode _ _ ne_sw _)
              (.cellNode _ sw_ne _ _) (.cellNode se_nw _ _ _) =>
    .cellNode nw_se ne_sw sw_ne se_nw
  | .cellNode (.level4Node nw1 ne1 sw1 se1) (.level4Node nw2 ne2 sw2 se2)
              (.level4Node nw3 ne3 sw3 se3) (.level4Node nw4 ne4 sw4 se4) =>
    .level4Node
      (centeredSubnodeLevel4 nw1 ne1 sw1 se1)
      (centeredSubnodeLevel4 nw2 ne2 sw2 se2)
      (centeredSubnodeLevel4 nw3 ne3 sw3 se3)
      (centeredSubnodeLevel4 nw4 ne4 sw4 se4)
  | m => m

/--
Extracts the horizontal center subnode spanning between west and east nodes.
-/
def centeredHorizontalSubnode : MacroCell → MacroCell → MacroCell
  | .cellNode _ w_ne _ w_se, .cellNode e_nw _ e_sw _ =>
    match w_ne, w_se, e_nw, e_sw with
    | .cellNode _ _ _ w_ne_se, .cellNode _ _ w_se_ne _,
      .cellNode _ _ _ e_nw_sw, .cellNode _ e_sw_nw _ _ =>
      .cellNode w_ne_se e_nw_sw w_se_ne e_sw_nw
    | .level4Node _ _ _ w_ne_se, .level4Node _ _ w_se_ne _,
      .level4Node _ _ _ e_nw_sw, .level4Node _ e_sw_nw _ _ =>
      .level4Node w_ne_se e_nw_sw w_se_ne e_sw_nw
    | _, _, _, _ => emptyLevel4
  | w, _ => w

/--
Extracts the vertical center subnode spanning between north and south nodes.
-/
def centeredVerticalSubnode : MacroCell → MacroCell → MacroCell
  | .cellNode _ _ n_sw n_se, .cellNode s_nw s_ne _ _ =>
    match n_sw, n_se, s_nw, s_ne with
    | .cellNode _ _ _ n_sw_se, .cellNode _ _ _ n_se_sw,
      .cellNode _ _ s_nw_ne _, .cellNode _ s_ne_nw _ _ =>
      .cellNode n_sw_se n_se_sw s_nw_ne s_ne_nw
    | .level4Node _ _ _ n_sw_se, .level4Node _ _ _ n_se_sw,
      .level4Node _ _ s_nw_ne _, .level4Node _ s_ne_nw _ _ =>
      .level4Node n_sw_se n_se_sw s_nw_ne s_ne_nw
    | _, _, _, _ => emptyLevel4
  | n, _ => n

/--
Extracts the center sub-subnode from a node of level k >= 5.
-/
def centeredSubSubnode (m : MacroCell) : MacroCell :=
  centeredSubnode (centeredSubnode m)

/--
Computes the population of the center sub-subnode.
-/
def centeredSubSubnodeSize (m : MacroCell) : UInt32 :=
  (centeredSubSubnode m).size

def emptySubnode : MacroCell → MacroCell
  | .level4Node _ _ _ _ => emptyLevel4
  | .cellNode nw _ _ _ =>
    let sub := emptySubnode nw
    .cellNode sub sub sub sub

/--
Surrounds a MacroCell with empty nodes of matching size, creating a centered
macrocell of level k + 2.
-/
def expandCentered : MacroCell → MacroCell
  | .level4Node nw ne sw se =>
    let e4 := emptyLevel4
    let nw_se := MacroCell.level4Node 0 0 0 nw
    let ne_sw := MacroCell.level4Node 0 0 ne 0
    let sw_ne := MacroCell.level4Node 0 sw 0 0
    let se_nw := MacroCell.level4Node se 0 0 0
    let q_nw := MacroCell.cellNode e4 e4 e4 nw_se
    let q_ne := MacroCell.cellNode e4 e4 ne_sw e4
    let q_sw := MacroCell.cellNode e4 sw_ne e4 e4
    let q_se := MacroCell.cellNode se_nw e4 e4 e4
    .cellNode q_nw q_ne q_sw q_se
  | .cellNode nw ne sw se =>
    let ek := emptySubnode nw
    let nw_se := MacroCell.cellNode ek ek ek nw
    let ne_sw := MacroCell.cellNode ek ek ne ek
    let sw_ne := MacroCell.cellNode ek sw ek ek
    let se_nw := MacroCell.cellNode se ek ek ek
    let ek1 := MacroCell.cellNode ek ek ek ek
    let q_nw := MacroCell.cellNode ek1 ek1 ek1 nw_se
    let q_ne := MacroCell.cellNode ek1 ek1 ne_sw ek1
    let q_sw := MacroCell.cellNode ek1 sw_ne ek1 ek1
    let q_se := MacroCell.cellNode se_nw ek1 ek1 ek1
    .cellNode q_nw q_ne q_sw q_se

/--
Recursive Gosper step on MacroCell.
Stepping a level 4 node returns the central 8x8 leaf wrapped in an empty level 4 node.
Stepping a level 5 node returns a level 4 node.
Stepping a level k+1 node returns a level k node.
-/
def hashLifeStep : MacroCell → MacroCell
  | .level4Node nw ne sw se =>
    let outLeaf := centeredSubnodeLevel4 nw ne sw se
    .level4Node 0 0 0 outLeaf
  | .cellNode (.level4Node nw1 ne1 sw1 se1) (.level4Node nw2 ne2 sw2 se2)
              (.level4Node nw3 ne3 sw3 se3) (.level4Node nw4 ne4 sw4 se4) =>
    let n00 := centeredSubnodeLevel4 nw1 ne1 sw1 se1
    let n01 := centeredSubnodeLevel4 ne1 nw2 se1 sw2
    let n02 := centeredSubnodeLevel4 nw2 ne2 sw2 se2
    let n10 := centeredSubnodeLevel4 sw1 se1 nw3 ne3
    let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
    let n12 := centeredSubnodeLevel4 sw2 se2 nw4 ne4
    let n20 := centeredSubnodeLevel4 nw3 ne3 sw3 se3
    let n21 := centeredSubnodeLevel4 ne3 nw4 se3 sw4
    let n22 := centeredSubnodeLevel4 nw4 ne4 sw4 se4
    let q_nw := centeredSubnodeLevel4 n00 n01 n10 n11
    let q_ne := centeredSubnodeLevel4 n01 n02 n11 n12
    let q_sw := centeredSubnodeLevel4 n10 n11 n20 n21
    let q_se := centeredSubnodeLevel4 n11 n12 n21 n22
    .level4Node q_nw q_ne q_sw q_se
  | .cellNode nw _ _ _ =>
    let sub := centeredSubnode nw
    .cellNode sub sub sub sub

/--
Suite of 5 caches mirroring HashLifeAlgorithm.kt:
- canonicalLevel4Map
- canonicalCellNodeMap
- cellNodeMap
- level4NodeMap
- leafNodeMap
-/
structure HashLifeCaches where
  canonicalLevel4Map : Cache MacroCell MacroCell
  canonicalCellNodeMap : Cache MacroCell MacroCell
  cellNodeMap : Cache MacroCell MacroCell
  level4NodeMap : ObjectLongCache MacroCell
  leafNodeMap : LongIntCache
  computedGenerations : UInt64
deriving DecidableEq

/--
Initializes an empty HashLife cache suite.
-/
def initHashLifeCaches : HashLifeCaches :=
  { canonicalLevel4Map := Cache.empty
  , canonicalCellNodeMap := Cache.empty
  , cellNodeMap := Cache.empty
  , level4NodeMap := Cache.empty
  , leafNodeMap := Cache.empty
  , computedGenerations := 0 }

/--
Prunes all caches to the specified generational thresholds.
-/
def pruneHashLifeCaches (caches : HashLifeCaches) (macroKeep leafKeep : UInt64) : HashLifeCaches :=
  let oldestMacro := if caches.computedGenerations >= macroKeep then caches.computedGenerations - macroKeep else 0
  let oldestLeaf := if caches.computedGenerations >= leafKeep then caches.computedGenerations - leafKeep else 0
  { canonicalLevel4Map := caches.canonicalLevel4Map.prune oldestMacro
  , canonicalCellNodeMap := caches.canonicalCellNodeMap.prune oldestMacro
  , cellNodeMap := caches.cellNodeMap.prune oldestMacro
  , level4NodeMap := caches.level4NodeMap.prune oldestMacro
  , leafNodeMap := caches.leafNodeMap.prune oldestLeaf
  , computedGenerations := caches.computedGenerations }

/--
Canonicalizes a MacroCell using the canonical caches (hash-consing).
-/
def makeCanonical (m : MacroCell) (caches : HashLifeCaches) : MacroCell × HashLifeCaches :=
  match m with
  | .level4Node nw ne sw se =>
    let (canon, newL4Map) := caches.canonicalLevel4Map.get id (.level4Node nw ne sw se) caches.computedGenerations
    (canon, { caches with canonicalLevel4Map := newL4Map })
  | .cellNode nw ne sw se =>
    let (cnw, c1) := makeCanonical nw caches
    let (cne, c2) := makeCanonical ne c1
    let (csw, c3) := makeCanonical sw c2
    let (cse, c4) := makeCanonical se c3
    let canonicalForm := MacroCell.cellNode cnw cne csw cse
    let (canon, newCellMap) := c4.canonicalCellNodeMap.get id canonicalForm c4.computedGenerations
    (canon, { c4 with canonicalCellNodeMap := newCellMap })

/--
Cached next generation computation using `cellNodeMap` and `level4NodeMap`.
-/
def cachedComputeNextGen (m : MacroCell) (caches : HashLifeCaches) : MacroCell × HashLifeCaches :=
  let (canon, c1) := makeCanonical m caches
  let (res, newStepMap) := c1.cellNodeMap.get hashLifeStep canon c1.computedGenerations
  (res, { c1 with cellNodeMap := newStepMap, computedGenerations := c1.computedGenerations + 1 })

@[kotlin_file]
def macroCellFileSpec : FileSpec := {
  imports := #[]
  items := #[
    .cls {
      name := "MacroCell"
      header := "sealed interface MacroCell"
      body := #[
        .verbatim "fun level(): UInt
fun size(): UInt
fun cellHashCode(): UInt = hashCode().toUInt()

data class Level4Node(
    val nw: ULong,
    val ne: ULong,
    val sw: ULong,
    val se: ULong,
) : MacroCell {
    override fun level(): UInt = 4u

    private val _size: UInt =
        nw.countOneBits().toUInt() +
            ne.countOneBits().toUInt() +
            sw.countOneBits().toUInt() +
            se.countOneBits().toUInt()

    override fun size(): UInt = _size

    private val _hashCode: Int = f_Algorithm_level4Hash(nw, ne, sw, se).toInt()

    override fun hashCode(): Int = _hashCode
}

data class CellNode(
    val nw: MacroCell,
    val ne: MacroCell,
    val sw: MacroCell,
    val se: MacroCell,
) : MacroCell {
    init {
        require(nw.level() == ne.level())
        require(ne.level() == sw.level())
        require(sw.level() == se.level())
    }

    private val _level: UInt = nw.level() + 1u

    override fun level(): UInt = _level

    private val _size: UInt = nw.size() + ne.size() + sw.size() + se.size()

    override fun size(): UInt = _size

    private val _hashCode: Int =
        f_Algorithm_cellNodeHash(
            _level,
            nw.hashCode().toUInt(),
            ne.hashCode().toUInt(),
            sw.hashCode().toUInt(),
            se.hashCode().toUInt(),
        ).toInt()

    override fun hashCode(): Int = _hashCode
}"
      ]
    },
    .topLevel
  ]
}

end Algorithm

