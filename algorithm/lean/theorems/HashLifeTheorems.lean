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
import Algorithm.HashLife
import AlgorithmDefs
import proofs.HashLifeProofs

local notation "ℕ" => Nat

namespace Algorithm

theorem macroCellSize_emptyNode : ∀ (k : ℕ), macroCellSize (emptyNode k) = 0 :=
  macroCellSize_emptyNode_Impl

theorem centeredSubSubnode_expandCentered (k : ℕ) (nw ne sw se : MacroCell) :
    centeredSubSubnode (expandCentered (.node k nw ne sw se)) = .node k nw ne sw se :=
  centeredSubSubnode_expandCentered_Impl k nw ne sw se

theorem expandCentered_level (k : ℕ) (nw ne sw se : MacroCell) :
    (expandCentered (.node k nw ne sw se)).level = k + 2 :=
  expandCentered_level_Impl k nw ne sw se

theorem expandCentered_size_node (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (expandCentered (.node k nw ne sw se)) =
    macroCellSize (.node k nw ne sw se) :=
  expandCentered_size_node_Impl k nw ne sw se

theorem expandCentered_confinement (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (.node k nw ne sw se))) =
    macroCellSize (expandCentered (.node k nw ne sw se)) :=
  expandCentered_confinement_Impl k nw ne sw se

theorem subnodes_shared_center (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ _ nw_se, .node _ _ _ ne_sw _,
      .node _ _ sw_ne _ _, .node _ se_nw _ _ _ =>
      nw_se = sn.n11 ∧ ne_sw = sn.n11 ∧ sw_ne = sn.n11 ∧ se_nw = sn.n11
    | _, _, _, _ => False :=
  subnodes_shared_center_Impl k sn

theorem subnodes_horizontal_alignment (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ nw_ne _ nw_se, .node _ ne_nw _ ne_sw _,
      .node _ _ sw_ne _ sw_se, .node _ se_nw _ se_sw _ =>
      nw_ne = ne_nw ∧ nw_se = ne_sw ∧ sw_ne = se_nw ∧ sw_se = se_sw
    | _, _, _, _ => False :=
  subnodes_horizontal_alignment_Impl k sn

theorem subnodes_vertical_alignment (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ nw_sw nw_se, .node _ _ _ ne_sw ne_se,
      .node _ sw_nw sw_ne _ _, .node _ se_nw se_ne _ _ =>
      nw_sw = sw_nw ∧ nw_se = se_nw ∧ ne_sw = sw_ne ∧ ne_se = se_ne
    | _, _, _, _ => False :=
  subnodes_vertical_alignment_Impl k sn

theorem centeredSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubnode (emptyNode (k + 2)) = emptyNode (k + 1) :=
  centeredSubnode_emptyNode_Impl

theorem centeredHorizontalSubnode_emptyNode : ∀ (k : ℕ),
    centeredHorizontalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1) :=
  centeredHorizontalSubnode_emptyNode_Impl

theorem centeredVerticalSubnode_emptyNode : ∀ (k : ℕ),
    centeredVerticalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1) :=
  centeredVerticalSubnode_emptyNode_Impl

theorem centeredSubSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubSubnode (emptyNode (k + 3)) = emptyNode (k + 1) :=
  centeredSubSubnode_emptyNode_Impl

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
      , n22 := emptyNode (k + 1) } :=
  decomposeSubnodes_emptyNode_Impl k

theorem hashLifeStep_empty2 : hashLifeStep (emptyNode 2) = emptyNode 1 :=
  hashLifeStep_empty2_Impl

theorem packCentralNibbles_extract_q0 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) :
    (packCentralNibbles q0 q1 q2 q3) % 16 = q0 :=
  packCentralNibbles_extract_q0_Impl q0 q1 q2 q3 h0

theorem packCentralNibbles_extract_q1 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 16) % 16 = q1 :=
  packCentralNibbles_extract_q1_Impl q0 q1 q2 q3 h0 h1

theorem packCentralNibbles_extract_q2 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 256) % 16 = q2 :=
  packCentralNibbles_extract_q2_Impl q0 q1 q2 q3 h0 h1 h2

theorem packCentralNibbles_extract_q3 (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 4096) % 16 = q3 :=
  packCentralNibbles_extract_q3_Impl q0 q1 q2 q3 h0 h1 h2 h3

theorem packCentralNibbles_in_range (q0 q1 q2 q3 : ℕ)
    (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    packCentralNibbles q0 q1 q2 q3 < 65536 :=
  packCentralNibbles_in_range_Impl q0 q1 q2 q3 h0 h1 h2 h3

theorem computeLevel4NextGen16x16_zero :
    computeLevel4NextGen16x16 0 0 0 0 = 0 :=
  computeLevel4NextGen16x16_zero_Impl

theorem hashlife_step_soundness_block :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true false   -- (2, 1) active
    let sw := makeLevel1 false true false false   -- (1, 2) active
    let se := makeLevel1 true false false false   -- (2, 2) active
    let block4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_block_Impl

theorem hashlife_step_soundness_blinker :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) active
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_blinker_Impl

theorem hashlife_step_soundness_tub :
    let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_tub_Impl

theorem hashlife_step_soundness_boat :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false true true false    -- (3, 2) and (2, 3)
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_boat_Impl

theorem hashlife_step_soundness_glider :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false    -- (2, 2), (3, 2), (2, 3)
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := macroCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := macroCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_glider_Impl

theorem macroCellFlipX_involution : ∀ (m : MacroCell), macroCellFlipX (macroCellFlipX m) = m :=
  macroCellFlipX_involution_Impl

theorem macroCellFlipY_involution : ∀ (m : MacroCell), macroCellFlipY (macroCellFlipY m) = m :=
  macroCellFlipY_involution_Impl

theorem macroCellFlipX_size : ∀ (m : MacroCell), macroCellSize (macroCellFlipX m) = macroCellSize m :=
  macroCellFlipX_size_Impl

theorem macroCellFlipY_size : ∀ (m : MacroCell), macroCellSize (macroCellFlipY m) = macroCellSize m :=
  macroCellFlipY_size_Impl

theorem hashlife_step_flipX_commutes_block :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX block4x4) = macroCellFlipX (hashLifeStepLevel2 block4x4) :=
  hashlife_step_flipX_commutes_block_Impl

theorem hashlife_step_flipY_commutes_block :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY block4x4) = macroCellFlipY (hashLifeStepLevel2 block4x4) :=
  hashlife_step_flipY_commutes_block_Impl

theorem hashlife_step_flipX_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX blinker4x4) = macroCellFlipX (hashLifeStepLevel2 blinker4x4) :=
  hashlife_step_flipX_commutes_blinker_Impl

theorem hashlife_step_flipY_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY blinker4x4) = macroCellFlipY (hashLifeStepLevel2 blinker4x4) :=
  hashlife_step_flipY_commutes_blinker_Impl

end Algorithm
