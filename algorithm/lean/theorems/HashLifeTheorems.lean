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

theorem hashLifeStep_emptyNode (k : ℕ) :
    hashLifeStep (emptyNode (k + 5)) = emptyNode (k + 4) :=
  hashLifeStep_emptyNode_Impl k

theorem stepLevel4Node_eq_stepLevel4NodeWith (m : MacroCell) :
    stepLevel4Node m = stepLevel4NodeWith m computeLeafNextGen8x8BranchUInt :=
  stepLevel4Node_eq_stepLevel4NodeWith_Impl m

theorem computePruneThresholds_macro
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : gen ≥ macroKeep.toUInt64) :
    (computePruneThresholds gen macroKeep leafKeep).oldestMacroToKeep = gen - macroKeep.toUInt64 :=
  computePruneThresholds_macro_Impl gen macroKeep leafKeep h

theorem computePruneThresholds_leaf
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : gen ≥ leafKeep.toUInt64) :
    (computePruneThresholds gen macroKeep leafKeep).oldestLeafToKeep = gen - leafKeep.toUInt64 :=
  computePruneThresholds_leaf_Impl gen macroKeep leafKeep h

theorem computePruneThresholds_macro_zero
    (gen : UInt64) (macroKeep leafKeep : UInt32)
    (h : ¬(gen ≥ macroKeep.toUInt64)) :
    (computePruneThresholds gen macroKeep leafKeep).oldestMacroToKeep = 0 :=
  computePruneThresholds_macro_zero_Impl gen macroKeep leafKeep h

theorem computeGenerationStep_thresholds
    (step : UInt32)
    (st : HashLifeStepState)
    (computedGenerations : UInt64)
    (macroKeep leafKeep : UInt32)
    (stepOneGen : HashLifeStepState → HashLifeStepState) :
    (computeGenerationStep step st computedGenerations macroKeep leafKeep stepOneGen).thresholds =
      computePruneThresholds (computedGenerations + step.toUInt64) macroKeep leafKeep :=
  computeGenerationStep_thresholds_Impl step st computedGenerations macroKeep leafKeep stepOneGen

end Algorithm
