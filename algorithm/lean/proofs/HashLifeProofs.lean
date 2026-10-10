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
local notation "ℤ" => Int

namespace Algorithm

theorem makeCellNode_level (a b c d : MacroCell) :
    (makeCellNode a b c d).level = a.level + 1 := rfl

theorem makeCellNode_size (a b c d : MacroCell) :
    macroCellSize (makeCellNode a b c d) =
    macroCellSize a + macroCellSize b + macroCellSize c + macroCellSize d := rfl

theorem macroCellSize_emptyNode_Impl : ∀ (k : ℕ), macroCellSize (emptyNode k) = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | k + 5 => by
    have ih := macroCellSize_emptyNode_Impl (k + 4)
    change macroCellSize (makeCellNode (emptyNode (k + 4)) (emptyNode (k + 4)) (emptyNode (k + 4)) (emptyNode (k + 4))) = 0
    rw [makeCellNode_size, ih]

theorem centeredSubSubnode_expandCentered_Impl (nw ne sw se : MacroCell) :
    centeredSubSubnode (expandCentered (makeCellNode nw ne sw se)) = makeCellNode nw ne sw se := by
  rfl

theorem emptyLevel4_level : emptyLevel4.level = 4 := rfl

theorem emptySubnode_level : ∀ (m : MacroCell), (emptySubnode m).level = m.level
  | .level4Node _ _ _ _ _ => by
    change emptyLevel4.level = 4
    rw [emptyLevel4_level]
  | .cellNode _ nw _ _ _ => by
    change (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)).level = nw.level + 1
    rw [makeCellNode_level, emptySubnode_level nw]

theorem emptySubnode_size : ∀ (m : MacroCell), macroCellSize (emptySubnode m) = 0
  | .level4Node _ _ _ _ _ => rfl
  | .cellNode _ nw _ _ _ => by
    change macroCellSize (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)) = 0
    rw [makeCellNode_size, emptySubnode_size nw]

theorem expandCentered_level_Impl (nw ne sw se : MacroCell) :
    (expandCentered (makeCellNode nw ne sw se)).level = nw.level + 1 + 1 + 1 := by
  dsimp [expandCentered, makeCellNode, MacroCell.level]
  rw [emptySubnode_level]

theorem expandCentered_size_node_Impl (nw ne sw se : MacroCell) :
    macroCellSize (expandCentered (makeCellNode nw ne sw se)) =
    macroCellSize (makeCellNode nw ne sw se) := by
  dsimp [expandCentered, makeCellNode, macroCellSize]
  repeat rw [emptySubnode_size]
  omega

theorem expandCentered_confinement_Impl (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (makeCellNode nw ne sw se))) =
    macroCellSize (expandCentered (makeCellNode nw ne sw se)) := by
  rw [centeredSubSubnode_expandCentered_Impl]
  rw [expandCentered_size_node_Impl]

theorem subnodes_shared_center_Impl (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ _ _ nw_se, .cellNode _ _ _ ne_sw _,
      .cellNode _ _ sw_ne _ _, .cellNode _ se_nw _ _ _ =>
      nw_se = sn.n11 ∧ ne_sw = sn.n11 ∧ sw_ne = sn.n11 ∧ se_nw = sn.n11
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE, makeCellNode]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem subnodes_horizontal_alignment_Impl (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ nw_ne _ nw_se, .cellNode _ ne_nw _ ne_sw _,
      .cellNode _ _ sw_ne _ sw_se, .cellNode _ se_nw _ se_sw _ =>
      nw_ne = ne_nw ∧ nw_se = ne_sw ∧ sw_ne = se_nw ∧ sw_se = se_sw
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE, makeCellNode]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem subnodes_vertical_alignment_Impl (sn : HashLifeSubnodes) :
    match quadrantNW sn, quadrantNE sn, quadrantSW sn, quadrantSE sn with
    | .cellNode _ _ _ nw_sw nw_se, .cellNode _ _ _ ne_sw ne_se,
      .cellNode _ sw_nw sw_ne _ _, .cellNode _ se_nw se_ne _ _ =>
      nw_sw = sw_nw ∧ nw_se = se_nw ∧ ne_sw = sw_ne ∧ ne_se = se_ne
    | _, _, _, _ => False := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE, makeCellNode]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem centeredSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredSubnode (emptyNode (k + 5)) = emptyNode (k + 4)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredHorizontalSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredHorizontalSubnode (emptyNode (k + 5)) (emptyNode (k + 5)) = emptyNode (k + 4)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredVerticalSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredVerticalSubnode (emptyNode (k + 5)) (emptyNode (k + 5)) = emptyNode (k + 4)
  | 0 => rfl
  | _ + 1 => rfl

theorem centeredSubSubnode_emptyNode_Impl : ∀ (k : ℕ),
    centeredSubSubnode (emptyNode (k + 6)) = emptyNode (k + 4)
  | 0 => rfl
  | _ + 1 => rfl

theorem decomposeSubnodes_emptyNode_Impl : ∀ (k : ℕ),
    decomposeSubnodes (emptyNode (k + 6)) =
      { n00 := emptyNode (k + 4)
      , n01 := emptyNode (k + 4)
      , n02 := emptyNode (k + 4)
      , n10 := emptyNode (k + 4)
      , n11 := emptyNode (k + 4)
      , n12 := emptyNode (k + 4)
      , n20 := emptyNode (k + 4)
      , n21 := emptyNode (k + 4)
      , n22 := emptyNode (k + 4) }
  | 0 => rfl
  | _ + 1 => rfl

theorem hashLifeStep_empty2_Impl : hashLifeStep (emptyNode 5) = emptyNode 4 := by
  rfl

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
    let grid := microCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

theorem hashlife_step_soundness_blinker_Impl :
    let nw := makeLevel1 false false false true   -- (1, 1) active
    let ne := makeLevel1 false false true true    -- (2, 1) and (3, 1) active
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

theorem hashlife_step_soundness_tub_Impl :
    let nw := makeLevel1 false true true false    -- (1, 0) and (0, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

theorem hashlife_step_soundness_boat_Impl :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false true false false   -- (1, 2)
    let se := makeLevel1 false true true false    -- (3, 2) and (2, 3)
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

theorem hashlife_step_soundness_glider_Impl :
    let nw := makeLevel1 false false false true   -- (1, 1)
    let ne := makeLevel1 false false true false   -- (2, 1)
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false    -- (2, 2), (3, 2), (2, 3)
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
    cellsEqual classicalStep hashLifeResult = true := by
  decide

theorem macroCellFlipX_involution_Impl : ∀ (m : MacroCell), macroCellFlipX (macroCellFlipX m) = m
  | .level4Node _ _ _ _ _ => rfl
  | .cellNode _ nw ne sw se => by
    simp [macroCellFlipX]
    exact ⟨macroCellFlipX_involution_Impl nw, macroCellFlipX_involution_Impl ne,
           macroCellFlipX_involution_Impl sw, macroCellFlipX_involution_Impl se⟩

theorem macroCellFlipY_involution_Impl : ∀ (m : MacroCell), macroCellFlipY (macroCellFlipY m) = m
  | .level4Node _ _ _ _ _ => rfl
  | .cellNode _ nw ne sw se => by
    simp [macroCellFlipY]
    exact ⟨macroCellFlipY_involution_Impl nw, macroCellFlipY_involution_Impl ne,
           macroCellFlipY_involution_Impl sw, macroCellFlipY_involution_Impl se⟩

theorem macroCellFlipX_size_Impl : ∀ (m : MacroCell), macroCellSize (macroCellFlipX m) = macroCellSize m
  | .level4Node _ nw ne sw se => by
    dsimp [macroCellFlipX, macroCellSize]
    have h : popcount64 sw + popcount64 se + popcount64 nw + popcount64 ne =
             popcount64 nw + popcount64 ne + popcount64 sw + popcount64 se := by ac_rfl
    rw [h]
  | .cellNode _ nw ne sw se => by
    dsimp [macroCellFlipX, macroCellSize]
    rw [macroCellFlipX_size_Impl sw, macroCellFlipX_size_Impl se,
        macroCellFlipX_size_Impl nw, macroCellFlipX_size_Impl ne]
    omega

theorem macroCellFlipY_size_Impl : ∀ (m : MacroCell), macroCellSize (macroCellFlipY m) = macroCellSize m
  | .level4Node _ nw ne sw se => by
    dsimp [macroCellFlipY, macroCellSize]
    have h : popcount64 ne + popcount64 nw + popcount64 se + popcount64 sw =
             popcount64 nw + popcount64 ne + popcount64 sw + popcount64 se := by ac_rfl
    rw [h]
  | .cellNode _ nw ne sw se => by
    dsimp [macroCellFlipY, macroCellSize]
    rw [macroCellFlipY_size_Impl ne, macroCellFlipY_size_Impl nw,
        macroCellFlipY_size_Impl se, macroCellFlipY_size_Impl sw]
    omega

theorem hashlife_step_flipX_commutes_block_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipX block4x4) = microCellFlipX (hashLifeStepLevel2 block4x4) := by
  decide

theorem hashlife_step_flipY_commutes_block_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipY block4x4) = microCellFlipY (hashLifeStepLevel2 block4x4) := by
  decide

theorem hashlife_step_flipX_commutes_blinker_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipX blinker4x4) = microCellFlipX (hashLifeStepLevel2 blinker4x4) := by
  decide

theorem hashlife_step_flipY_commutes_blinker_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    hashLifeStepLevel2 (microCellFlipY blinker4x4) = microCellFlipY (hashLifeStepLevel2 blinker4x4) := by
  decide

theorem centeredSubnodeLevel3BitsUInt_zero_Impl :
    centeredSubnodeLevel3BitsUInt 0 = 0 := by
  rfl

theorem centeredHorizontalSubnodeLevel3BitsUInt_zero_Impl :
    centeredHorizontalSubnodeLevel3BitsUInt 0 0 = 0 := by
  rfl

theorem centeredVerticalSubnodeLevel3BitsUInt_zero_Impl :
    centeredVerticalSubnodeLevel3BitsUInt 0 0 = 0 := by
  rfl

theorem centeredSubSubnodeLevel4BitsUInt_zero_Impl :
    centeredSubSubnodeLevel4BitsUInt 0 0 0 0 = 0 := by
  rfl

theorem packLeafFrom4x4sUInt_zero_Impl :
    packLeafFrom4x4sUInt 0 0 0 0 = 0 := by
  rfl

theorem computeLevel4NextGen16x16UInt_zero_Impl :
    computeLevel4NextGen16x16UInt 0 0 0 0 = 0 := by
  rfl

theorem computeLevel4NextGen16x16WithUInt_zero_Impl (f : UInt64 → UInt32) (hf : f 0 = 0) :
    computeLevel4NextGen16x16WithUInt 0 0 0 0 f = 0 := by
  change packLeafFrom4x4sUInt (f 0) (f 0) (f 0) (f 0) = 0
  rw [hf]
  rfl

theorem expandOffsetDelta_succ_Impl (k : ℕ) :
    expandOffsetDelta (k + 1) = -3 * (2 : ℤ) ^ k := by
  rfl

theorem stepOffsetDelta_succ_Impl (k : ℕ) :
    stepOffsetDelta (k + 2) = (2 : ℤ) ^ k := by
  rfl

theorem expandCentered_guarantees_confinement_Impl (nw ne sw se : MacroCell) :
    isConfinedToSubSubnode (expandCentered (makeCellNode nw ne sw se)) := by
  unfold isConfinedToSubSubnode
  exact expandCentered_confinement_Impl nw ne sw se

theorem quadrants_cover_center_Impl (sn : HashLifeSubnodes) :
    (quadrantNW sn).level = sn.n00.level + 1 ∧
    (quadrantNE sn).level = sn.n01.level + 1 ∧
    (quadrantSW sn).level = sn.n10.level + 1 ∧
    (quadrantSE sn).level = sn.n11.level + 1 := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE, makeCellNode, MacroCell.level]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem makeCellNode_macroCellToGrid (ox oy : ℤ) (a b c d : MacroCell) :
    macroCellToGrid ox oy (makeCellNode a b c d) =
    macroCellToGrid ox oy a ++
    macroCellToGrid (ox + ((2 : ℤ) ^ (a.level.toNat))) oy b ++
    macroCellToGrid ox (oy + ((2 : ℤ) ^ (a.level.toNat))) c ++
    macroCellToGrid (ox + ((2 : ℤ) ^ (a.level.toNat))) (oy + ((2 : ℤ) ^ (a.level.toNat))) d := rfl

theorem macroCellToGrid_emptyNode_Impl : ∀ (k : ℕ) (ox oy : ℤ),
    macroCellToGrid ox oy (emptyNode k) = []
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | k + 5, ox, oy => by
    have ih := macroCellToGrid_emptyNode_Impl (k + 4)
    change macroCellToGrid ox oy (makeCellNode (emptyNode (k + 4)) (emptyNode (k + 4)) (emptyNode (k + 4)) (emptyNode (k + 4))) = []
    rw [makeCellNode_macroCellToGrid]
    repeat rw [ih]
    rfl

theorem hashLifeToGrid_emptyNode_Impl (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode k } = [] := by
  dsimp [hashLifeToGrid]
  exact macroCellToGrid_emptyNode_Impl k ox oy

theorem hashLifeStepN_zero_Impl (st : HashLifeCellState) :
    hashLifeStepN 0 st = st := by
  rfl

theorem hashLifeStepN_succ_Impl (n : ℕ) (st : HashLifeCellState) :
    hashLifeStepN (n + 1) st = hashLifeStepN n (hashLifeNextGeneration st) := by
  rfl

theorem hashlife_stepN_induction_step_Impl (n : ℕ) (st : HashLifeCellState)
    (h : hashLifeToGrid (hashLifeStepN n (hashLifeNextGeneration st)) =
         stepN n (hashLifeToGrid (hashLifeNextGeneration st))) :
    hashLifeToGrid (hashLifeStepN (n + 1) st) =
    stepN n (hashLifeToGrid (hashLifeNextGeneration st)) := by
  rw [hashLifeStepN_succ_Impl]
  exact h

theorem hashLifeStep_emptyNode_Impl : ∀ (k : ℕ),
    hashLifeStep (emptyNode (k + 5)) = emptyNode (k + 4)
  | 0 => hashLifeStep_empty2_Impl
  | k + 1 => by
    have h := centeredSubnode_emptyNode_Impl k
    change makeCellNode (centeredSubnode (emptyNode (k + 5))) (centeredSubnode (emptyNode (k + 5))) (centeredSubnode (emptyNode (k + 5))) (centeredSubnode (emptyNode (k + 5))) = emptyNode (k + 5)
    rw [h]
    rfl

theorem hashLifeNextGenerationStep_emptyNode_Impl (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }) = [] := by
  dsimp [hashLifeNextGenerationStep, hashLifeToGrid]
  rw [hashLifeStep_emptyNode_Impl k]
  exact macroCellToGrid_emptyNode_Impl (k + 4) _ _

theorem hashlife_step_equivalence_empty_Impl (k : ℕ) (ox oy : ℤ) :
    hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }) =
    stepGrid (hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode (k + 5) }) := by
  rw [hashLifeNextGenerationStep_emptyNode_Impl k ox oy]
  rw [hashLifeToGrid_emptyNode_Impl (k + 5) ox oy]
  rw [stepGrid_empty]

theorem stepLevel4NodeWith_zero_Impl (f : UInt64 → UInt32) (hf : f 0 = 0) :
    stepLevel4NodeWith emptyLevel4 f = 0 := by
  dsimp [stepLevel4NodeWith, emptyLevel4, makeLevel4Node]
  exact computeLevel4NextGen16x16WithUInt_zero_Impl f hf

end Algorithm
