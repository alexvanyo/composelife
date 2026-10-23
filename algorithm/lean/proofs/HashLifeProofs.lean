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

theorem emptyNode_depth_Impl : ∀ (k : ℕ),
    (emptyNode (k + 4)).depth = k + 4
  | 0 => rfl
  | k + 1 => by
    dsimp [emptyNode, makeCellNode, MacroCell.depth]
    rw [emptyNode_depth_Impl k]

theorem stepQuadrants_emptyNode_Impl : ∀ (k : ℕ),
    stepQuadrants (emptyNode (k + 6)) =
      { nw := emptyNode (k + 5)
      , ne := emptyNode (k + 5)
      , sw := emptyNode (k + 5)
      , se := emptyNode (k + 5) }
  | 0 => rfl
  | _ + 1 => rfl

theorem hashLifeStepRecursiveAux_emptyNode_Impl : ∀ (fuel k : ℕ) (_h_fuel : fuel ≥ k + 1),
    hashLifeStepRecursiveAux fuel (emptyNode (k + 5)) = emptyNode (k + 4)
  | 0, _, h => by omega
  | fuel + 1, 0, _ => rfl
  | fuel + 1, k + 1, h => by
    have h_fuel' : fuel ≥ k + 1 := by omega
    show makeCellNode (hashLifeStepRecursiveAux fuel (stepQuadrants (emptyNode (k + 6))).nw)
                      (hashLifeStepRecursiveAux fuel (stepQuadrants (emptyNode (k + 6))).ne)
                      (hashLifeStepRecursiveAux fuel (stepQuadrants (emptyNode (k + 6))).sw)
                      (hashLifeStepRecursiveAux fuel (stepQuadrants (emptyNode (k + 6))).se) =
         emptyNode (k + 5)
    rw [stepQuadrants_emptyNode_Impl k]
    dsimp
    rw [hashLifeStepRecursiveAux_emptyNode_Impl fuel k h_fuel']
    rfl

theorem hashLifeStep_emptyNode_Impl (k : ℕ) :
    hashLifeStep (emptyNode (k + 5)) = emptyNode (k + 4) := by
  dsimp [hashLifeStep, hashLifeStepRecursive]
  have h_depth : (emptyNode (k + 5)).depth = k + 5 := by
    have := emptyNode_depth_Impl (k + 1)
    exact this
  rw [h_depth]
  exact hashLifeStepRecursiveAux_emptyNode_Impl (k + 5) k (by omega)

theorem stepLevel4Node_eq_stepLevel4NodeWith_Impl (m : MacroCell) :
    stepLevel4Node m = stepLevel4NodeWith m computeLeafNextGen8x8BranchUInt := by
  cases m with
  | level4Node h nw ne sw se => rfl
  | cellNode h nw ne sw se => rfl

theorem computePruneThresholds_macro_Impl
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : gen ≥ macroKeep.toUInt64) :
    (computePruneThresholds gen macroKeep leafKeep).oldestMacroToKeep = gen - macroKeep.toUInt64 := by
  dsimp [computePruneThresholds]
  split
  · rfl
  · next h_not =>
    exfalso
    exact h_not h

theorem computePruneThresholds_leaf_Impl
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : gen ≥ leafKeep.toUInt64) :
    (computePruneThresholds gen macroKeep leafKeep).oldestLeafToKeep = gen - leafKeep.toUInt64 := by
  dsimp [computePruneThresholds]
  split
  · rfl
  · next h_not =>
    exfalso
    exact h_not h

theorem computePruneThresholds_macro_zero_Impl
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : ¬(gen ≥ macroKeep.toUInt64)) :
    (computePruneThresholds gen macroKeep leafKeep).oldestMacroToKeep = 0 := by
  dsimp [computePruneThresholds]
  split
  · next h_is =>
    exfalso
    exact h h_is
  · rfl

theorem computeGenerationStep_thresholds_Impl
    (step : UInt32)
    (st : HashLifeStepState)
    (computedGenerations : UInt64)
    (macroKeep leafKeep : UInt32)
    (stepOneGen : HashLifeStepState → HashLifeStepState) :
    (computeGenerationStep step st computedGenerations macroKeep leafKeep stepOneGen).thresholds =
      computePruneThresholds (computedGenerations + step.toUInt64) macroKeep leafKeep := by
  rfl

end Algorithm

