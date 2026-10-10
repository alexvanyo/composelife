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
import proofs.MacroCellProofs

local notation "ℕ" => Nat

namespace Algorithm

theorem macroCellSize_emptyNode_Impl : ∀ (k : ℕ), macroCellSize (emptyNode k) = 0
  | 0 => rfl
  | k + 1 => by
    have ih := macroCellSize_emptyNode_Impl k
    unfold emptyNode
    unfold macroCellSize
    omega

theorem centeredSubSubnode_expandCentered_Impl (k : ℕ) (nw ne sw se : MacroCell) :
    centeredSubSubnode (expandCentered (.node k nw ne sw se)) = .node k nw ne sw se := by
  rfl

theorem expandCentered_level_Impl (k : ℕ) (nw ne sw se : MacroCell) :
    (expandCentered (.node k nw ne sw se)).level = k + 2 := by
  rfl

theorem expandCentered_size_node_Impl (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (expandCentered (.node k nw ne sw se)) =
    macroCellSize (.node k nw ne sw se) := by
  simp [expandCentered, macroCellSize, macroCellSize_emptyNode_Impl]

theorem expandCentered_confinement_Impl (k : ℕ) (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (.node k nw ne sw se))) =
    macroCellSize (expandCentered (.node k nw ne sw se)) := by
  rw [centeredSubSubnode_expandCentered_Impl]
  rw [expandCentered_size_node_Impl]

theorem subnodes_shared_center_Impl (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ _ nw_se, .node _ _ _ ne_sw _,
      .node _ _ sw_ne _ _, .node _ se_nw _ _ _ =>
      nw_se = sn.n11 ∧ ne_sw = sn.n11 ∧ sw_ne = sn.n11 ∧ se_nw = sn.n11
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem subnodes_horizontal_alignment_Impl (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ nw_ne _ nw_se, .node _ ne_nw _ ne_sw _,
      .node _ _ sw_ne _ sw_se, .node _ se_nw _ se_sw _ =>
      nw_ne = ne_nw ∧ nw_se = ne_sw ∧ sw_ne = se_nw ∧ sw_se = se_sw
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem subnodes_vertical_alignment_Impl (k : ℕ) (sn : HashLifeSubnodes) :
    match quadrantNW k sn, quadrantNE k sn, quadrantSW k sn, quadrantSE k sn with
    | .node _ _ _ nw_sw nw_se, .node _ _ _ ne_sw ne_se,
      .node _ sw_nw sw_ne _ _, .node _ se_nw se_ne _ _ =>
      nw_sw = sw_nw ∧ nw_se = se_nw ∧ ne_sw = sw_ne ∧ ne_se = se_ne
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem centeredSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredSubnode (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredHorizontalSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredHorizontalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredVerticalSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredVerticalSubnode (emptyNode (k + 2)) (emptyNode (k + 2)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredSubSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredSubSubnode (emptyNode (k + 3)) = emptyNode (k + 1)
  | 0 => rfl
  | _ + 1 => rfl

theorem decomposeSubnodes_emptyNode_Impl (k : ℕ) :
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

theorem hashLifeStep_empty2_Impl : hashLifeStep (emptyNode 2) = emptyNode 1 := by
  unfold hashLifeStep
  exact hashlife_empty_level2_stability_Impl

theorem packCentralNibbles_extract_q0_Impl (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) :
    (packCentralNibbles q0 q1 q2 q3) % 16 = q0 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q1_Impl (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 16) % 16 = q1 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q2_Impl (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 256) % 16 = q2 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_extract_q3_Impl (q0 q1 q2 q3 : ℕ) (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    ((packCentralNibbles q0 q1 q2 q3) / 4096) % 16 = q3 := by
  unfold packCentralNibbles
  omega

theorem packCentralNibbles_in_range_Impl (q0 q1 q2 q3 : ℕ)
    (h0 : q0 < 16) (h1 : q1 < 16) (h2 : q2 < 16) (h3 : q3 < 16) :
    packCentralNibbles q0 q1 q2 q3 < 65536 := by
  unfold packCentralNibbles
  omega

theorem computeLevel4NextGen16x16_zero_Impl :
    computeLevel4NextGen16x16 0 0 0 0 = 0 := by
  rfl

theorem hashlife_step_soundness_block_Impl :
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

theorem hashlife_step_soundness_blinker_Impl :
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

theorem hashlife_step_soundness_tub_Impl :
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

theorem hashlife_step_soundness_boat_Impl :
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

theorem hashlife_step_soundness_glider_Impl :
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

theorem macroCellFlipX_involution_Impl : ∀ (m : MacroCell), macroCellFlipX (macroCellFlipX m) = m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipX]
    exact ⟨macroCellFlipX_involution_Impl nw, macroCellFlipX_involution_Impl ne,
           macroCellFlipX_involution_Impl sw, macroCellFlipX_involution_Impl se⟩

theorem macroCellFlipY_involution_Impl : ∀ (m : MacroCell), macroCellFlipY (macroCellFlipY m) = m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipY]
    exact ⟨macroCellFlipY_involution_Impl nw, macroCellFlipY_involution_Impl ne,
           macroCellFlipY_involution_Impl sw, macroCellFlipY_involution_Impl se⟩

theorem macroCellFlipX_size_Impl : ∀ (m : MacroCell), macroCellSize (macroCellFlipX m) = macroCellSize m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipX, macroCellSize]
    rw [macroCellFlipX_size_Impl nw, macroCellFlipX_size_Impl ne,
        macroCellFlipX_size_Impl sw, macroCellFlipX_size_Impl se]
    omega

theorem macroCellFlipY_size_Impl : ∀ (m : MacroCell), macroCellSize (macroCellFlipY m) = macroCellSize m
  | .leaf _ => rfl
  | .node _ nw ne sw se => by
    simp [macroCellFlipY, macroCellSize]
    rw [macroCellFlipY_size_Impl nw, macroCellFlipY_size_Impl ne,
        macroCellFlipY_size_Impl sw, macroCellFlipY_size_Impl se]
    omega

theorem hashlife_step_flipX_commutes_block_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX block4x4) = macroCellFlipX (hashLifeStepLevel2 block4x4) := by
  decide

theorem hashlife_step_flipY_commutes_block_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY block4x4) = macroCellFlipY (hashLifeStepLevel2 block4x4) := by
  decide

theorem hashlife_step_flipX_commutes_blinker_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipX blinker4x4) = macroCellFlipX (hashLifeStepLevel2 blinker4x4) := by
  decide

theorem hashlife_step_flipY_commutes_blinker_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (macroCellFlipY blinker4x4) = macroCellFlipY (hashLifeStepLevel2 blinker4x4) := by
  decide

end Algorithm
