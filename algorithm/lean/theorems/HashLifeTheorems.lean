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
local notation "ℤ" => Int

namespace Algorithm

theorem macroCellSize_emptyNode : ∀ (k : ℕ), macroCellSize (emptyNode k) = 0 :=
  macroCellSize_emptyNode_Impl

theorem centeredSubSubnode_expandCentered (nw ne sw se : MacroCell) :
    centeredSubSubnode (expandCentered (makeCellNode nw ne sw se)) = makeCellNode nw ne sw se :=
  centeredSubSubnode_expandCentered_Impl nw ne sw se

theorem expandCentered_level (nw ne sw se : MacroCell) :
    (expandCentered (makeCellNode nw ne sw se)).level = nw.level + 1 + 1 + 1 :=
  expandCentered_level_Impl nw ne sw se

theorem expandCentered_size_node (nw ne sw se : MacroCell) :
    macroCellSize (expandCentered (makeCellNode nw ne sw se)) =
    macroCellSize (makeCellNode nw ne sw se) :=
  expandCentered_size_node_Impl nw ne sw se

theorem expandCentered_confinement (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (makeCellNode nw ne sw se))) =
    macroCellSize (expandCentered (makeCellNode nw ne sw se)) :=
  expandCentered_confinement_Impl nw ne sw se

theorem subnodes_shared_center (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ _ _ nw_se, .cellNode _ _ _ ne_sw _,
      .cellNode _ _ sw_ne _ _, .cellNode _ se_nw _ _ _ =>
      nw_se = sn.n11 ∧ ne_sw = sn.n11 ∧ sw_ne = sn.n11 ∧ se_nw = sn.n11
    | _, _, _, _ => False :=
  subnodes_shared_center_Impl sn

theorem subnodes_horizontal_alignment (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ nw_ne _ nw_se, .cellNode _ ne_nw _ ne_sw _,
      .cellNode _ _ sw_ne _ sw_se, .cellNode _ se_nw _ se_sw _ =>
      nw_ne = ne_nw ∧ nw_se = ne_sw ∧ sw_ne = se_nw ∧ sw_se = se_sw
    | _, _, _, _ => False :=
  subnodes_horizontal_alignment_Impl sn

theorem subnodes_vertical_alignment (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ _ nw_sw nw_se, .cellNode _ _ _ ne_sw ne_se,
      .cellNode _ sw_nw sw_ne _ _, .cellNode _ se_nw se_ne _ _ =>
      nw_sw = sw_nw ∧ nw_se = se_nw ∧ ne_sw = sw_ne ∧ ne_se = se_ne
    | _, _, _, _ => False :=
  subnodes_vertical_alignment_Impl sn

theorem centeredSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubnode (emptyNode (k + 5)) = emptyNode (k + 4) :=
  centeredSubnode_emptyNode_Impl

theorem centeredHorizontalSubnode_emptyNode : ∀ (k : ℕ),
    centeredHorizontalSubnode (emptyNode (k + 5)) (emptyNode (k + 5)) = emptyNode (k + 4) :=
  centeredHorizontalSubnode_emptyNode_Impl

theorem centeredVerticalSubnode_emptyNode : ∀ (k : ℕ),
    centeredVerticalSubnode (emptyNode (k + 5)) (emptyNode (k + 5)) = emptyNode (k + 4) :=
  centeredVerticalSubnode_emptyNode_Impl

theorem centeredSubSubnode_emptyNode : ∀ (k : ℕ),
    centeredSubSubnode (emptyNode (k + 6)) = emptyNode (k + 4) :=
  centeredSubSubnode_emptyNode_Impl

theorem decomposeSubnodes_emptyNode : ∀ (k : ℕ),
    decomposeSubnodes (emptyNode (k + 6)) =
      { n00 := emptyNode (k + 4)
      , n01 := emptyNode (k + 4)
      , n02 := emptyNode (k + 4)
      , n10 := emptyNode (k + 4)
      , n11 := emptyNode (k + 4)
      , n12 := emptyNode (k + 4)
      , n20 := emptyNode (k + 4)
      , n21 := emptyNode (k + 4)
      , n22 := emptyNode (k + 4) } :=
  decomposeSubnodes_emptyNode_Impl

theorem hashLifeStep_empty2 : hashLifeStep (emptyNode 5) = emptyNode 4 :=
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
    let grid := microCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_block_Impl

theorem hashlife_step_soundness_blinker :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) active
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_blinker_Impl

theorem hashlife_step_soundness_tub :
    let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_tub_Impl

theorem hashlife_step_soundness_boat :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false true true false    -- (3, 2) and (2, 3)
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_boat_Impl

theorem hashlife_step_soundness_glider :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false    -- (2, 2), (3, 2), (2, 3)
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
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
    hashLifeStepLevel2 (microCellFlipX block4x4) = microCellFlipX (hashLifeStepLevel2 block4x4) :=
  hashlife_step_flipX_commutes_block_Impl

theorem hashlife_step_flipY_commutes_block :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipY block4x4) = microCellFlipY (hashLifeStepLevel2 block4x4) :=
  hashlife_step_flipY_commutes_block_Impl

theorem hashlife_step_flipX_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipX blinker4x4) = microCellFlipX (hashLifeStepLevel2 blinker4x4) :=
  hashlife_step_flipX_commutes_blinker_Impl

theorem hashlife_step_flipY_commutes_blinker :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipY blinker4x4) = microCellFlipY (hashLifeStepLevel2 blinker4x4) :=
  hashlife_step_flipY_commutes_blinker_Impl

theorem centeredSubnodeLevel3BitsUInt_zero :
    centeredSubnodeLevel3BitsUInt 0 = 0 :=
  centeredSubnodeLevel3BitsUInt_zero_Impl

theorem centeredHorizontalSubnodeLevel3BitsUInt_zero :
    centeredHorizontalSubnodeLevel3BitsUInt 0 0 = 0 :=
  centeredHorizontalSubnodeLevel3BitsUInt_zero_Impl

theorem centeredVerticalSubnodeLevel3BitsUInt_zero :
    centeredVerticalSubnodeLevel3BitsUInt 0 0 = 0 :=
  centeredVerticalSubnodeLevel3BitsUInt_zero_Impl

theorem centeredSubSubnodeLevel4BitsUInt_zero :
    centeredSubSubnodeLevel4BitsUInt 0 0 0 0 = 0 :=
  centeredSubSubnodeLevel4BitsUInt_zero_Impl

theorem packLeafFrom4x4sUInt_zero :
    packLeafFrom4x4sUInt 0 0 0 0 = 0 :=
  packLeafFrom4x4sUInt_zero_Impl

theorem computeLevel4NextGen16x16UInt_zero :
    computeLevel4NextGen16x16UInt 0 0 0 0 = 0 :=
  computeLevel4NextGen16x16UInt_zero_Impl

theorem computeLevel4NextGen16x16WithUInt_zero (f : UInt64 → UInt32) (hf : f 0 = 0) :
    computeLevel4NextGen16x16WithUInt 0 0 0 0 f = 0 :=
  computeLevel4NextGen16x16WithUInt_zero_Impl f hf

theorem expandOffsetDelta_succ (k : ℕ) :
    expandOffsetDelta (k + 1) = -3 * (2 : ℤ) ^ k :=
  expandOffsetDelta_succ_Impl k

theorem stepOffsetDelta_succ (k : ℕ) :
    stepOffsetDelta (k + 2) = (2 : ℤ) ^ k :=
  stepOffsetDelta_succ_Impl k

theorem expandCentered_guarantees_confinement (nw ne sw se : MacroCell) :
    isConfinedToSubSubnode (expandCentered (makeCellNode nw ne sw se)) :=
  expandCentered_guarantees_confinement_Impl nw ne sw se

theorem quadrants_cover_center (sn : HashLifeSubnodes) :
    (quadrantNW sn).level = sn.n00.level + 1 ∧
    (quadrantNE sn).level = sn.n01.level + 1 ∧
    (quadrantSW sn).level = sn.n10.level + 1 ∧
    (quadrantSE sn).level = sn.n11.level + 1 :=
  quadrants_cover_center_Impl sn

theorem macroCellToGrid_emptyNode (k : ℕ) (ox oy : ℤ) :
    macroCellToGrid ox oy (emptyNode k) = [] :=
  macroCellToGrid_emptyNode_Impl k ox oy

theorem hashLifeToGrid_emptyNode (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode k } = [] :=
  hashLifeToGrid_emptyNode_Impl k ox oy

theorem hashLifeStepN_zero (st : HashLifeCellState) :
    hashLifeStepN 0 st = st :=
  hashLifeStepN_zero_Impl st

theorem hashLifeStepN_succ (n : ℕ) (st : HashLifeCellState) :
    hashLifeStepN (n + 1) st = hashLifeStepN n (hashLifeNextGeneration st) :=
  hashLifeStepN_succ_Impl n st

theorem hashlife_stepN_induction_step (n : ℕ) (st : HashLifeCellState)
    (h : hashLifeToGrid (hashLifeStepN n (hashLifeNextGeneration st)) =
         stepN n (hashLifeToGrid (hashLifeNextGeneration st))) :
    hashLifeToGrid (hashLifeStepN (n + 1) st) =
    stepN n (hashLifeToGrid (hashLifeNextGeneration st)) :=
  hashlife_stepN_induction_step_Impl n st h

theorem hashLifeStep_emptyNode (k : ℕ) :
    hashLifeStep (emptyNode (k + 5)) = emptyNode (k + 4) :=
  hashLifeStep_emptyNode_Impl k

theorem hashLifeNextGenerationStep_emptyNode (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }) = [] :=
  hashLifeNextGenerationStep_emptyNode_Impl k ox oy

theorem hashlife_step_equivalence_empty (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }) =
    stepGrid (hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode (k + 5) }) :=
  hashlife_step_equivalence_empty_Impl k ox oy

theorem stepLevel4NodeWith_zero (f : UInt64 → UInt32) (hf : f 0 = 0) :
    stepLevel4NodeWith emptyLevel4 f = 0 :=
  stepLevel4NodeWith_zero_Impl f hf

end Algorithm
