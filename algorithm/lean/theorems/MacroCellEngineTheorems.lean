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

import Algorithm.MacroCell
import AlgorithmDefs
import proofs.MacroCellEngineProofs
import proofs.MacroCellQueryProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# The MacroCell engine of `LeanHashLifeAlgorithm`

Master theorems for the compiled MacroCell functions that `LeanHashLifeAlgorithm.kt` and `MacroCell.kt` call,
and for the functions the generated Kotlin substitutes for them (`kotlin_expr`). Callbacks are characterized by
what the Kotlin memo tables and canonical maps return, never by what the compiled functions compute.
-/

-- =========================================================================
-- Generated-code substitutions
-- =========================================================================

/-- `popcount64` (the SWAR count inlined into the generated Kotlin) counts the set bits, like `countOneBits()`. -/
theorem popcount64_eq_cpop (x : UInt64) : (popcount64 x).toNat = x.toBitVec.cpop.toNat :=
  popcount64_toNat_eq_cpop x

/-- The generated code computes `centeredSubSubnode` with `centeredSubSubnodeFast`; they agree on every node. -/
theorem centeredSubSubnodeFast_eq_centeredSubSubnode {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) :
    centeredSubSubnodeFast m = centeredSubSubnode m :=
  centeredSubSubnodeFast_eq hm h5

/-- The generated code computes `centeredSubSubnodeSize` with `centeredSubSubnodeSizeFast`; they agree. -/
theorem centeredSubSubnodeSizeFast_eq_centeredSubSubnodeSize {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) :
    centeredSubSubnodeSizeFast m = centeredSubSubnodeSize m :=
  centeredSubSubnodeSizeFast_eq hm h5

/-- The generated code computes `emptySubnode m` as the pre-built empty node of `m`'s level. -/
theorem emptySubnode_eq_emptyNode_of_WFd {m : MacroCell} {d : ℕ} (hm : WFd m d) : emptySubnode m = emptyNode d :=
  emptySubnode_eq_emptyNode hm

-- =========================================================================
-- Stepping
-- =========================================================================

/-- HashLife's step keeps every node hash-consistent. -/
theorem hashLifeStep_hashOK (m : MacroCell) : HashOK (hashLifeStep m) :=
  HashOK_hashLifeStep m

/-- With the exact callbacks, `stepCellNodeWith` is HashLife's step. -/
theorem stepCellNodeWith_eq_hashLifeStep {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) (hd : d < 2 ^ 32) :
    stepCellNodeWith m stepLevel4Node hashLifeStep = hashLifeStep m :=
  stepCellNodeWith_exact hm h5 hd

/--
The canonicalization of `LeanHashLifeAlgorithm` returns its argument: `canonicalizeMacroCellWith` is the identity
on hash-consistent well-formed nodes of depth at most 30, for callbacks that return values equal to their
argument and a subnode canonicalization that is the same recursion.
-/
theorem canonicalizeMacroCellWith_eq_self (internLevel4 : MacroCell → MacroCell)
    (findExistingCell : MacroCell → Option MacroCell) (canonicalizeSubnode internCell : MacroCell → MacroCell)
    (hI4 : ∀ q, internLevel4 q = q)
    (hFe : ∀ q e, HashOK q → findExistingCell q = some e → e = q)
    (hIc : ∀ q, HashOK q → internCell q = q)
    (hS : ∀ q, canonicalizeSubnode q =
      canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell)
    {q : MacroCell} {d : ℕ} (hq : WFd q d) (hd : d ≤ 30) (H : HashOK q) :
    canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell = q :=
  canonicalize_fixpoint internLevel4 findExistingCell canonicalizeSubnode internCell hI4 hFe hIc
    (fun q _ _ _ _ => hS q) d q hq hd H

/--
The prepared-node step of `LeanHashLifeAlgorithm` (`stepCellNodeWith` with its memoized callbacks, followed by
canonicalization) is HashLife's step on every hash-consistent well-formed node of depth 5 to 30.
-/
theorem leanHashLife_preparedStep_eq (L : UInt64 → UInt32) (G : MacroCell → UInt64) (F : MacroCell → MacroCell)
    (internLevel4 : MacroCell → MacroCell) (findExistingCell : MacroCell → Option MacroCell)
    (canonicalizeSubnode internCell : MacroCell → MacroCell)
    (hL : ∀ w, L w = computeLeafNextGen8x8BranchUInt w)
    (hG : ∀ q, G q = stepLevel4NodeWith
      (canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) L)
    (hF : ∀ q, F q = stepCellNodeWith
      (canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) G F)
    (hI4 : ∀ q, internLevel4 q = q)
    (hFe : ∀ q e, HashOK q → findExistingCell q = some e → e = q)
    (hIc : ∀ q, HashOK q → internCell q = q)
    (hS : ∀ q, canonicalizeSubnode q =
      canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell)
    {q : MacroCell} {d : ℕ} (hq : WFd q d) (h5 : 5 ≤ d) (hd : d ≤ 30) (H : HashOK q) :
    canonicalizeMacroCellWith (stepCellNodeWith q G F) internLevel4 findExistingCell canonicalizeSubnode internCell =
      hashLifeStep q :=
  leanHashLife_preparedStep L G F internLevel4 findExistingCell canonicalizeSubnode internCell hL hG hF hI4 hFe hIc hS
    q d hq h5 hd H

/-- Every HashLife generation keeps the center of the window fixed. -/
theorem windowCenter_nextGeneration (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 30) :
    windowCenter (hashLifeNextGeneration st) = windowCenter st :=
  windowCenter_hashLifeNextGeneration st hwf hd

/--
One generation of `LeanHashLifeAlgorithm`: `stepHashLifeStateWith` with a prepared-node step that is HashLife's
step (such as `leanHashLife_preparedStep_eq`'s) computes exactly one HashLife generation, `Int32` offsets
included, for any hash-consistent well-formed state of depth at most 28 whose window center lies within
`2 ^ 30` of the origin.
-/
theorem stepHashLifeStateWith_eq_nextGeneration (st : HashLifeStepState) (P : MacroCell → MacroCell)
    (hP : ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → P q = hashLifeStep q)
    (hwf : isWellFormed st.macroCell) (hok : HashOK st.macroCell) (hd : st.macroCell.depth ≤ 28)
    (hcx : -2 ^ 30 ≤ (windowCenter st.toCellState).1 ∧ (windowCenter st.toCellState).1 ≤ 2 ^ 30)
    (hcy : -2 ^ 30 ≤ (windowCenter st.toCellState).2 ∧ (windowCenter st.toCellState).2 ≤ 2 ^ 30) :
    (stepHashLifeStateWith st P).toCellState = hashLifeNextGeneration st.toCellState :=
  stepHashLifeStateWith_correct st P hP hwf hok hd hcx hcy

/--
Master theorem for `LeanHashLifeAlgorithm.computeGenerationWithStep`: `n` generations by `computeGenerationStep`
over `stepHashLifeStateWith` compute `n` HashLife generations (`Int32` offsets included), and the resulting cells
are exactly `n` Conway generations of the input cells. It holds for any hash-consistent well-formed state of depth
`d` with `d + n ≤ 29` whose window center lies within `2 ^ 30` of the origin; both conditions are on the input
only.
-/
theorem computeGenerationStep_correct (P : MacroCell → MacroCell)
    (hP : ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → P q = hashLifeStep q)
    (n : UInt32) (st : HashLifeStepState) (computedGenerations : UInt64) (macroKeep leafKeep : UInt32)
    (hwf : isWellFormed st.macroCell) (hok : HashOK st.macroCell) (hd : st.macroCell.depth + n.toNat ≤ 29)
    (hcx : -2 ^ 30 ≤ (windowCenter st.toCellState).1 ∧ (windowCenter st.toCellState).1 ≤ 2 ^ 30)
    (hcy : -2 ^ 30 ≤ (windowCenter st.toCellState).2 ∧ (windowCenter st.toCellState).2 ≤ 2 ^ 30) :
    (computeGenerationStep n st computedGenerations macroKeep leafKeep
        (fun s => stepHashLifeStateWith s P)).finalState.toCellState = hashLifeStepN n.toNat st.toCellState ∧
    cellsEqual
      (hashLifeToGrid (computeGenerationStep n st computedGenerations macroKeep leafKeep
        (fun s => stepHashLifeStateWith s P)).finalState.toCellState)
      (stepN n.toNat (hashLifeToGrid st.toCellState)) = true := by
  have h := stepNGenerationsWith_stepHashLifeStateWith P hP n.toNat n st rfl hwf hok hd hcx hcy
  exact ⟨h, h ▸ hashlife_n_step_equivalence_Impl n.toNat st.toCellState hwf (by
    simp [HashLifeStepState.toCellState]; omega)⟩

-- =========================================================================
-- Cell queries
-- =========================================================================

/-- `cellToLeafBitUInt` is the Morton index of a leaf coordinate. -/
theorem cellToLeafBitUInt_eq_mortonIndex (x y : ℕ) (hx : x < 8) (hy : y < 8) :
    (cellToLeafBitUInt x.toUInt32 y.toUInt32).toNat = mortonIndex x y :=
  cellToLeafBit_morton x hx y hy

/-- `leafContains` reads the leaf's cell function. -/
theorem leafContains_eq_leafAt (leaf : UInt64) (x y : UInt32) (hx : x.toNat < 8) (hy : y.toNat < 8) :
    leafContains leaf x y = leafAt leaf x.toNat y.toNat :=
  leafContains_toNat leaf x y hx hy

/-- `leafWithCell` sets exactly one cell of a leaf. -/
theorem leafAt_leafWithCell_eq (leaf : UInt64) (x y : UInt32) (hx : x.toNat < 8) (hy : y.toNat < 8) (b : Bool)
    (x' y' : ℤ) :
    leafAt (leafWithCell leaf x y b) x' y' = if x' = x.toNat ∧ y' = y.toNat then b else leafAt leaf x' y' :=
  leafAt_leafWithCell leaf x y hx hy b x' y'

/-- `macroCellContains` (Kotlin's `MacroCell.contains`) is the cell function, at every `Int32` coordinate. -/
theorem macroCellContains_eq_cellAt {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d ≤ 30) (x y : Int32) :
    macroCellContains m x y = cellAt m x.toInt y.toInt :=
  macroCellContains_correct m hm hd x y

/--
`macroCellWithCell` (Kotlin's `MacroCell.withCell`) keeps the node well-formed and hash-consistent and sets
exactly the cell `(x, y)` if it lies inside the node, leaving the node unchanged otherwise.
-/
theorem macroCellWithCell_spec {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d ≤ 30) (H : HashOK m)
    (x y : Int32) (b : Bool) :
    WFd (macroCellWithCell m x y b) d ∧ HashOK (macroCellWithCell m x y b) ∧
    ∀ x' y', cellAt (macroCellWithCell m x y b) x' y' =
      if 0 ≤ x.toInt ∧ x.toInt < 2 ^ d ∧ 0 ≤ y.toInt ∧ y.toInt < 2 ^ d then
        (if x' = x.toInt ∧ y' = y.toInt then b else cellAt m x' y')
      else cellAt m x' y' :=
  macroCellWithCell_correct m hm hd H x y b

/-- `minimumMacroCellLevel span` is the smallest level of at least 4 whose width covers `span` cells. -/
theorem minimumMacroCellLevel_correct (span : UInt32) :
    4 ≤ (minimumMacroCellLevel span).toNat ∧ span.toNat ≤ 2 ^ (minimumMacroCellLevel span).toNat ∧
      ((minimumMacroCellLevel span).toNat = 4 ∨ 2 ^ ((minimumMacroCellLevel span).toNat - 1) < span.toNat) :=
  minimumMacroCellLevel_spec span

end Algorithm
