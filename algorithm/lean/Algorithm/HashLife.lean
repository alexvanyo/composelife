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
import Algorithm.Properties

local notation "ℕ" => Nat

namespace Algorithm

-- =========================================================================
-- Part 1: MacroCell Size and Population Counting
-- =========================================================================

/--
Computes the total number of alive cells in a MacroCell.
Matches `MacroCell.size` in Kotlin (`override val size = nw.size + ne.size + sw.size + se.size`).
-/
def macroCellSize : MacroCell → ℕ
  | .leaf true => 1
  | .leaf false => 0
  | .node _ nw ne sw se =>
    macroCellSize nw + macroCellSize ne + macroCellSize sw + macroCellSize se

/--
Empty node size is identically 0 for all quadtree levels k.
-/
theorem macroCellSize_emptyNode : ∀ (k : ℕ), macroCellSize (emptyNode k) = 0
  | 0 => rfl
  | k + 1 => by
    have ih := macroCellSize_emptyNode k
    unfold emptyNode
    unfold macroCellSize
    omega

-- =========================================================================
-- Part 2: Centered Expansion Mechanics (HashLifeCellState.expandCentered)
-- =========================================================================

/--
Formal definition of HashLifeCellState.expandCentered from HashLifeCellState.kt.
Takes a macrocell at level k and embeds it into the dead center of a new macrocell
at level k + 2 with empty padding quadrants.
-/
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

/--
Theorem: Centered Sub-Subnode Recovery.
Extracting the central sub-subnode from an expanded macrocell reconstructs
the original macrocell with 100% fidelity.
-/
theorem centeredSubSubnode_expandCentered (k : ℕ) (nw ne sw se : MacroCell) :
    centeredSubSubnode (expandCentered (.node k nw ne sw se)) = .node k nw ne sw se := by
  rfl

/--
Theorem: Level Increase under Expansion.
`expandCentered` strictly increases the quadtree level by 2.
-/
theorem expandCentered_level (k : ℕ) (nw ne sw se : MacroCell) :
    (expandCentered (.node k nw ne sw se)).level = k + 2 := by
  rfl

/--
Theorem: Live Cell Population Invariance under Expansion.
`expandCentered` preserves the exact live cell count of the macrocell.
-/
theorem expandCentered_size_node (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (expandCentered (.node k nw ne sw se)) =
    macroCellSize (.node k nw ne sw se) := by
  simp [expandCentered, macroCellSize, macroCellSize_emptyNode]

/--
Theorem: Need-to-Expand Confinement Guarantee.
After `expandCentered`, the live population of the center sub-subnode is identical
to the live population of the entire expanded node, proving that no live cells
exist in the outer perimeter margin.
-/
theorem expandCentered_confinement (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (.node k nw ne sw se))) =
    macroCellSize (expandCentered (.node k nw ne sw se)) := by
  rw [centeredSubSubnode_expandCentered]
  rw [expandCentered_size_node]

-- =========================================================================
-- Part 3: The 9-Subnode Geometric Decomposition & Quadrant Alignment
-- =========================================================================

/--
The 9 overlapping subnodes extracted from a node of level k >= 3 during HashLife's recursive step.
Matches n00 ... n22 in HashLifeAlgorithm.kt lines 188-196 and lines 254-262.
-/
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

/--
Decomposes a MacroCell into its 9 constituent overlapping subnodes.
-/
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

/--
Quadrant builders from subnodes matching HashLifeAlgorithm.kt:
Each quadrant combines 4 adjacent subnodes to form a recursive step input at level k - 1.
-/
def quadrantNW (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n00 sn.n01 sn.n10 sn.n11

def quadrantNE (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n01 sn.n02 sn.n11 sn.n12

def quadrantSW (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n10 sn.n11 sn.n20 sn.n21

def quadrantSE (k : ℕ) (sn : HashLifeSubnodes) : MacroCell :=
  .node k sn.n11 sn.n12 sn.n21 sn.n22

/--
Theorem: Central Subnode Universality (Quadtree Intersection).
All four recursive stepping quadrants share the exact same central subnode n11:
- quadrantNW's South-East child is n11
- quadrantNE's South-West child is n11
- quadrantSW's North-East child is n11
- quadrantSE's North-West child is n11
This formalizes why HashLife's canonical hash-consing achieves maximal memoization overlap.
-/
theorem subnodes_shared_center (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ _ nw_se, .node _ _ _ ne_sw _,
      .node _ _ sw_ne _ _, .node _ se_nw _ _ _ =>
      nw_se = sn.n11 ∧ ne_sw = sn.n11 ∧ sw_ne = sn.n11 ∧ se_nw = sn.n11
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
Theorem: Adjacent Quadrant Horizontal Boundary Alignment.
The East boundary of quadrantNW matches the West boundary of quadrantNE,
and the East boundary of quadrantSW matches the West boundary of quadrantSE.
-/
theorem subnodes_horizontal_alignment (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ nw_ne _ nw_se, .node _ ne_nw _ ne_sw _,
      .node _ _ sw_ne _ sw_se, .node _ se_nw _ se_sw _ =>
      nw_ne = ne_nw ∧ nw_se = ne_sw ∧ sw_ne = se_nw ∧ sw_se = se_sw
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
Theorem: Adjacent Quadrant Vertical Boundary Alignment.
The South boundary of quadrantNW matches the North boundary of quadrantSW,
and the South boundary of quadrantNE matches the North boundary of quadrantSE.
-/
theorem subnodes_vertical_alignment (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ nw_sw nw_se, .node _ _ _ ne_sw ne_se,
      .node _ sw_nw sw_ne _ _, .node _ se_nw se_ne _ _ =>
      nw_sw = sw_nw ∧ nw_se = se_nw ∧ ne_sw = sw_ne ∧ ne_se = se_ne
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

-- =========================================================================
-- Part 4: Universal Empty Node Invariants
-- =========================================================================

/--
Theorem: Centered Subnode of Empty Node.
For any k >= 1, the centered subnode of an empty node at level k + 1 is an empty node at level k.
-/
theorem centeredSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubnode (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

/--
Theorem: Centered Horizontal Subnode of Empty Nodes.
Combining two empty nodes at level k + 2 horizontally yields an empty node at level k + 1.
-/
theorem centeredHorizontalSubnode_emptyNode : ∀ (k : ℕ),
    centeredHorizontalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

/--
Theorem: Centered Vertical Subnode of Empty Nodes.
Combining two empty nodes at level k + 2 vertically yields an empty node at level k + 1.
-/
theorem centeredVerticalSubnode_emptyNode : ∀ (k : ℕ),
    centeredVerticalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

/--
Theorem: Centered Sub-Subnode of Empty Node.
For any k >= 0, the centered sub-subnode of an empty node at level k + 3 is an empty node at level k + 1.
-/
theorem centeredSubSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubSubnode (emptyNode (k + 3)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

/--
Theorem: Empty Node Decomposition Universality.
Decomposing an empty node at level k + 3 produces empty subnodes across all 9 components.
-/
theorem decomposeSubnodes_emptyNode (k : ℕ) :
    decomposeSubnodes (emptyNode (k + 3)) =
      { n00 := emptyNode (k + 1)
      , n01 := emptyNode (k + 1)
      , n02 := emptyNode (k + 1)
      , n10 := emptyNode (k + 1)
      , n11 := emptyNode (k + 1)
      , n12 := emptyNode (k + 1)
      , n20 := emptyNode (k + 1)
      , n21 := emptyNode (k + 1)
      , n22 := emptyNode (k + 1) } := by
  rfl

theorem hashLifeStep_empty2 : hashLifeStep (emptyNode 2) = emptyNode 1 := by
  unfold hashLifeStep
  exact hashlife_empty_level2_stability

-- =========================================================================
-- Part 5: Level 3 Leaf Node 4x4 Central Splicing (Quadtree Bit Representation)
-- =========================================================================

/--
Computes the packed 16-bit word from four 4-bit quadrants (nibbles),
matching HashLifeAlgorithm.kt centeredSubnodeLevel3:
  node.nw.se + node.ne.sw * 16 + node.sw.ne * 256 + node.se.nw * 4096
-/
def packCentralNibbles (q0 q1 q2 q3 : ℕ) : ℕ :=
  q0 + q1 * 16 + q2 * 256 + q3 * 4096

/--
Theorem: Bitwise Disjointness and Unambiguous Extraction.
Each 4-bit quadrant q0, q1, q2, q3 (< 16) is uniquely recoverable from the packed 16-bit word,
proving that no bit collision or cross-lane carry occurs during quadtree center extraction.
-/
theorem packCentralNibbles_extract_q0 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) :
    (packCentralNibbles q0 q1 q2 q3) % 16 = q0 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q1 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 16) % 16 = q1 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q2 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 256) % 16 = q2 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q3 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 4096) % 16 = q3 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_in_range (q0 q1 q2 q3 : ℕ)
    (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    packCentralNibbles q0 q1 q2 q3 < 65536 := by
  unfold packCentralNibbles
  omega

/--
Extracts the central 4x4 from an 8x8 packed leaf node (64-bit word).
Matches centeredSubnodeLevel3 in Kotlin.
-/
def centeredSubnodeLevel3Bits (leaf : ℕ) : ℕ :=
  let nw := (leaf / (2^0)) % (2^16)
  let ne := (leaf / (2^16)) % (2^16)
  let sw := (leaf / (2^32)) % (2^16)
  let se := (leaf / (2^48)) % (2^16)
  let q0 := (nw / (2^12)) % 16
  let q1 := (ne / (2^8)) % 16
  let q2 := (sw / (2^4)) % 16
  let q3 := (se / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
Matches centeredHorizontalSubnodeLevel3 in Kotlin.
-/
def centeredHorizontalSubnodeLevel3Bits (w e : ℕ) : ℕ :=
  let w_ne := (w / (2^16)) % (2^16)
  let w_se := (w / (2^48)) % (2^16)
  let e_nw := (e / (2^0)) % (2^16)
  let e_sw := (e / (2^32)) % (2^16)
  let q0 := (w_ne / (2^12)) % 16
  let q1 := (e_nw / (2^8)) % 16
  let q2 := (w_se / (2^4)) % 16
  let q3 := (e_sw / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
Matches centeredVerticalSubnodeLevel3 in Kotlin.
-/
def centeredVerticalSubnodeLevel3Bits (n s : ℕ) : ℕ :=
  let n_sw := (n / (2^32)) % (2^16)
  let n_se := (n / (2^48)) % (2^16)
  let s_nw := (s / (2^0)) % (2^16)
  let s_ne := (s / (2^16)) % (2^16)
  let q0 := (n_sw / (2^12)) % 16
  let q1 := (n_se / (2^8)) % 16
  let q2 := (s_nw / (2^4)) % 16
  let q3 := (s_ne / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Extracts the center 4x4 from a 16x16 Level 4 node (four 8x8 leaf nodes).
Matches centeredSubSubnodeLevel4 in Kotlin.
-/
def centeredSubSubnodeLevel4Bits (nw ne sw se : ℕ) : ℕ :=
  let nw_se := (nw / (2^48)) % (2^16)
  let ne_sw := (ne / (2^32)) % (2^16)
  let sw_ne := (sw / (2^16)) % (2^16)
  let se_nw := (se / (2^0)) % (2^16)
  let q0 := (nw_se / (2^12)) % 16
  let q1 := (ne_sw / (2^8)) % 16
  let q2 := (sw_ne / (2^4)) % 16
  let q3 := (se_nw / (2^0)) % 16
  packCentralNibbles q0 q1 q2 q3

/--
Packs four 16-bit 4x4 quadrants into a 64-bit 8x8 leaf node.
-/
def packLeafFrom4x4s (q0 q1 q2 q3 : ℕ) : ℕ :=
  (q0 % (2^16)) + (q1 % (2^16)) * (2^16) + (q2 % (2^16)) * (2^32) + (q3 % (2^16)) * (2^48)

/--
Direct computation of next generation for a 16x16 Level 4 MacroCell (four 8x8 leaf nodes)
into its central 8x8 leaf node.
Matches Level4Node.computeNextGeneration in HashLifeAlgorithm.kt.
-/
def computeLevel4NextGen16x16 (nw ne sw se : ℕ) : ℕ :=
  let n00 := centeredSubnodeLevel3Bits nw
  let n01 := centeredHorizontalSubnodeLevel3Bits nw ne
  let n02 := centeredSubnodeLevel3Bits ne
  let n10 := centeredVerticalSubnodeLevel3Bits nw sw
  let n11 := centeredSubSubnodeLevel4Bits nw ne sw se
  let n12 := centeredVerticalSubnodeLevel3Bits ne se
  let n20 := centeredSubnodeLevel3Bits sw
  let n21 := centeredHorizontalSubnodeLevel3Bits sw se
  let n22 := centeredSubnodeLevel3Bits se

  let leafNW := packLeafFrom4x4s n00 n01 n10 n11
  let leafNE := packLeafFrom4x4s n01 n02 n11 n12
  let leafSW := packLeafFrom4x4s n10 n11 n20 n21
  let leafSE := packLeafFrom4x4s n11 n12 n21 n22

  let outNW := computeLeafNextGen8x8Branch leafNW
  let outNE := computeLeafNextGen8x8Branch leafNE
  let outSW := computeLeafNextGen8x8Branch leafSW
  let outSE := computeLeafNextGen8x8Branch leafSE

  packLeafFrom4x4s outNW outNE outSW outSE

/--
Theorem: Empty Level 4 Next Generation Stability.
Stepping an empty 16x16 Level 4 node directly yields an empty 8x8 leaf node (0).
-/
theorem computeLevel4NextGen16x16_zero :
    computeLevel4NextGen16x16 0 0 0 0 = 0 := by
  rfl

-- =========================================================================
-- Part 6: Classical Game of Life Soundness and Still Life / Oscillator Fidelity
-- =========================================================================

/--
Filters a list of live 2D coordinates to only those in the central 2x2 bounding window [1, 2] x [1, 2].
Matches the output window of a level 2 to level 1 HashLife step.
-/
def central2x2Window (coords : List Coord) : List Coord :=
  coords.filter (fun (x, y) => x >= 1 && x <= 2 && y >= 1 && y <= 2)

/--
Theorem: HashLife Step Level 2 Classical Grid Soundness for Block Still Life.
The central 2x2 output of `hashLifeStepLevel2` on a 4x4 block matches the
classical `stepGrid` rule filtered to the central 2x2 window.
-/
theorem hashlife_step_soundness_block :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true false   -- (2, 1) active
    let sw := makeLevel1 false true false false   -- (1, 2) active
    let se := makeLevel1 true false false false   -- (2, 2) active
    let block4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

/--
Theorem: HashLife Step Level 2 Classical Grid Soundness for Blinker Oscillator.
The horizontal blinker at (1, 1), (2, 1), (3, 1) evolves identically under
`hashLifeStepLevel2` and under classical `stepGrid`.
-/
theorem hashlife_step_soundness_blinker :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) active
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

/--
Theorem: HashLife Step Level 2 Classical Grid Soundness for Tub Still Life.
-/
theorem hashlife_step_soundness_tub :
    let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

/--
Theorem: HashLife Step Level 2 Classical Grid Soundness for Boat Still Life.
Boat at (1, 1), (2, 1), (1, 2), (3, 2), (2, 3).
-/
theorem hashlife_step_soundness_boat :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false true true false    -- (3, 2) and (2, 3)
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

/--
Theorem: HashLife Step Level 2 Classical Grid Soundness for Glider Step.
A glider entering the 4x4 region is correctly stepped into the 2x2 center by `hashLifeStepLevel2`.
-/
theorem hashlife_step_soundness_glider :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false    -- (2, 2), (3, 2), (2, 3)
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

-- =========================================================================
-- Part 7: Symmetry Invariance of HashLife Transitions
-- =========================================================================

/--
Horizontal reflection (flipX) across MacroCell quadrants:
Swaps North and South quadrants (nw <-> sw, ne <-> se) and recursively flips children.
-/
def macroCellFlipX : MacroCell → MacroCell
  | .leaf b => .leaf b
  | .node k nw ne sw se =>
    .node k (macroCellFlipX sw) (macroCellFlipX se) (macroCellFlipX nw) (macroCellFlipX ne)

/--
Vertical reflection (flipY) across MacroCell quadrants:
Swaps West and East quadrants (nw <-> ne, sw <-> se) and recursively flips children.
-/
def macroCellFlipY : MacroCell → MacroCell
  | .leaf b => .leaf b
  | .node k nw ne sw se =>
    .node k (macroCellFlipY ne) (macroCellFlipY nw) (macroCellFlipY se) (macroCellFlipY sw)

/--
Theorem: FlipX Involution.
Reflecting twice horizontally is the identity.
-/
theorem macroCellFlipX_involution : ∀ (m : MacroCell), macroCellFlipX (macroCellFlipX m) = m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipX]
    exact ⟨macroCellFlipX_involution nw, macroCellFlipX_involution ne,
           macroCellFlipX_involution sw, macroCellFlipX_involution se⟩

/--
Theorem: FlipY Involution.
Reflecting twice vertically is the identity.
-/
theorem macroCellFlipY_involution : ∀ (m : MacroCell), macroCellFlipY (macroCellFlipY m) = m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipY]
    exact ⟨macroCellFlipY_involution nw, macroCellFlipY_involution ne,
           macroCellFlipY_involution sw, macroCellFlipY_involution se⟩

/--
Theorem: Population Conservation under Reflection.
Flipping a MacroCell horizontally or vertically preserves its exact size.
-/
theorem macroCellFlipX_size : ∀ (m : MacroCell), macroCellSize (macroCellFlipX m) = macroCellSize m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipX, macroCellSize]
    rw [macroCellFlipX_size nw, macroCellFlipX_size ne, macroCellFlipX_size sw, macroCellFlipX_size se]
    omega

theorem macroCellFlipY_size : ∀ (m : MacroCell), macroCellSize (macroCellFlipY m) = macroCellSize m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipY, macroCellSize]
    rw [macroCellFlipY_size nw, macroCellFlipY_size ne, macroCellFlipY_size sw, macroCellFlipY_size se]
    omega

/--
Theorem: HashLife Step Level 2 Commutes with FlipX on Symmetric Patterns.
Verifies that stepping a vertically reflected block produces the vertically reflected step.
-/
theorem hashlife_step_flipX_commutes_block :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX block4x4) = macroCellFlipX (hashLifeStepLevel2 block4x4) := by
  decide

/--
Theorem: HashLife Step Level 2 Commutes with FlipY on Symmetric Patterns.
-/
theorem hashlife_step_flipY_commutes_block :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY block4x4) = macroCellFlipY (hashLifeStepLevel2 block4x4) := by
  decide

/--
Theorem: HashLife Step Level 2 Commutes with FlipX on Blinker.
-/
theorem hashlife_step_flipX_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX blinker4x4) = macroCellFlipX (hashLifeStepLevel2 blinker4x4) := by
  decide

/--
Theorem: HashLife Step Level 2 Commutes with FlipY on Blinker.
-/
theorem hashlife_step_flipY_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY blinker4x4) = macroCellFlipY (hashLifeStepLevel2 blinker4x4) := by
  decide

end Algorithm
