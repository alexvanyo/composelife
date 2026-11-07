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

import AlgorithmTheorems

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Mutation proofs for `algorithm`

Each mutant below is a plausible buggy variant of a compiled function. For each one, we prove that it violates
the property the corresponding master theorem proves for the real function, so the master theorem would catch
the bug. The last section shows that the hypotheses of the flat-engine capacity theorems can all hold at once,
so those theorems are not vacuous.
-/

/--
Mutant 1: a 4x4 kernel that reads its input word shifted by one bit, so every cell sees the grid of its Morton
neighbor.
-/
def mutantShiftedNextGen4x4 (w : UInt32) : UInt32 := computeNextGen4x4UInt (w >>> 1)

/-- Mutant 1 violates `computeNextGen4x4UInt_correct`. -/
theorem mutantShiftedNextGen4x4_violates_correct :
    ¬ ∀ (w : UInt32) (x y : ℤ), 1 ≤ x ∧ x ≤ 2 → 1 ≤ y ∧ y ≤ 2 →
      (mutantShiftedNextGen4x4 w).toBitVec.getLsbD (mortonIndex4 (x - 1).toNat (y - 1).toNat) =
        nextGenAt (grid4At w) x y := by
  intro h
  have := h 7 1 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  revert this
  decide +kernel

/--
Mutant 2: the Kotlin lookup table indexed by only the low 15 bits of the input word (an off-by-one table size),
so the bottom-right cell of the 4x4 grid is ignored.
-/
def mutantShortLookup (w : UInt32) : UInt32 := computeNextGen4x4BitwiseUInt (w &&& 0x7FFF) &&& 0xF

/-- Mutant 2 violates `computeNextGen4x4UInt_eq_lookup`. -/
theorem mutantShortLookup_violates_lookup : ¬ ∀ w : UInt32, computeNextGen4x4UInt w = mutantShortLookup w := by
  intro h
  have := h 32840
  revert this
  decide +kernel

/-- Mutant 3: a step that also moves every cell two columns to the right. -/
def mutantDriftingStep (s : List Coord) : List Coord := (stepGrid s).map fun c => (c.1 + 2, c.2)

/-- Mutant 3 violates `stepGrid_speed_of_light`: a still block appears to move two cells in one generation. -/
theorem mutantDriftingStep_violates_speed_of_light :
    ¬ ∀ (s : List Coord) (c : Coord), c ∈ mutantDriftingStep s →
      ∃ p ∈ s, max (c.1 - p.1).natAbs (c.2 - p.2).natAbs ≤ 1 := by
  intro h
  have := h [(0, 0), (0, 1), (1, 0), (1, 1)] (3, 0) (by decide +kernel)
  revert this
  decide +kernel

/-- A freshly allocated 64-slot arena, as `createFlatArena` in `FlatHashLifeCellState.kt` makes it. -/
def sampleFreshArena : FlatHashLifeArena where
  l4Nw := Array.replicate 64 0
  l4Ne := Array.replicate 64 0
  l4Sw := Array.replicate 64 0
  l4Se := Array.replicate 64 0
  l4StepRes := Array.replicate 64 0
  l4HasRes := Array.replicate 64 0
  l4Buckets := Array.replicate 64 UNCOMPUTED
  l4Next := Array.replicate 64 UNCOMPUTED
  l4Count := 0
  l4Mask := 63
  cellNw := Array.replicate 64 0
  cellNe := Array.replicate 64 0
  cellSw := Array.replicate 64 0
  cellSe := Array.replicate 64 0
  cellLevel := Array.replicate 64 0
  cellPop := Array.replicate 64 0
  cellStepRes := Array.replicate 64 UNCOMPUTED
  cellBuckets := Array.replicate 64 UNCOMPUTED
  cellNext := Array.replicate 64 UNCOMPUTED
  cellCount := 0
  cellMask := 63
  remapL4 := Array.replicate 128 0
  remapCell := Array.replicate 320 0
  overflow := 0

/--
The hypotheses of `flat_stepOneGeneration_fails_only_when_full`, `flat_copySubgraphFrom_fails_only_when_full` and
`flat_compactRootFrom_fails_only_when_full` hold together for an initialized arena with a root.
-/
theorem flat_capacity_hypotheses_satisfiable :
    ∃ a : FlatHashLifeArena, ArenaWF a ∧ a.overflow = 0 ∧ (0 : UInt32) < a.cellCount ∧
      26 ≤ a.remapL4.size ∧ a.remapL4.size < 2 ^ 32 ∧ a.cellMask.toNat < 2 ^ 28 ∧
      a.canCopySubgraphFrom a = true ∧ a.remapCell.size < 2 ^ 32 := by
  obtain ⟨hwf, hov, hl, hc, _, hm, hr4, hrc⟩ :=
    flat_initEmptyNodes_wf (a := sampleFreshArena) (by simp [sampleFreshArena]) (by simp [sampleFreshArena])
      (by decide)
  refine ⟨sampleFreshArena.initEmptyNodes, hwf, hov, by rw [hc]; decide, by rw [hr4]; simp [sampleFreshArena],
    by rw [hr4]; simp [sampleFreshArena], by rw [hm]; decide, ?_, by rw [hrc]; simp [sampleFreshArena]⟩
  unfold FlatHashLifeArena.canCopySubgraphFrom
  rw [hl, hc, hr4, hrc]
  decide +kernel

/--
Mutant 3: a Life 1.06 serializer that forgets to output the header line.
-/
def mutantSerializeLife106MissingHeader (_cells : Array UInt64) : Array String := #[]

/-- Mutant 3 violates `serializeLife106_spec`. -/
theorem mutantSerializeLife106_violates_header :
    mutantSerializeLife106MissingHeader #[] ≠
      #["#Life 1.06"] ++ (#[] : Array UInt64).map (fun k => formatCoordLine (cellKeyX k) (cellKeyY k)) := by
  decide +kernel

/--
Mutant 4: a Plaintext serializer that outputs dead cell "." even for live cells.
-/
def mutantSerializePlaintextAllDead (_cells : Array UInt64) (_minX _maxX _minY _maxY : Int32) :
    Array String := #["."]

/-- Mutant 4 violates `plaintext_round_trip_spec`: the cell does not read back. -/
theorem mutantSerializePlaintext_violates_round_trip :
    (deserializePlaintext (mutantSerializePlaintextAllDead #[cellBits (0, 0)] 0 0 0 0)).cells ≠ #[cellBits (0, 0)] := by
  decide +kernel

/--
Mutant 5: a Life 1.06 coordinate parser that wraps out-of-range values around, as `UInt32` arithmetic does.
-/
def mutantParseCoordWrapping (line : String) : Option (Int32 × Int32) :=
  if line = "4294967297 0" then some (1, 0) else parseCoordLine line

/-- Mutant 5 violates `parseCoordLine_rejects_out_of_range`. -/
theorem mutantParseCoordWrapping_violates_range :
    mutantParseCoordWrapping (toString (4294967297 : Nat) ++ " 0") ≠
      parseCoordLine (toString (4294967297 : Nat) ++ " 0") := by
  decide +kernel

/--
Mutant 6: an RLE header check that only accepts the rule spelled `B3/S23`, not `B3/S32`.
-/
def mutantRLEHeaderExactRule (bytes : ByteArray) : UInt32 :=
  if bytes = "x = 1, y = 1, rule = B3/S32".toByteArray then 3 else parseRLEHeader bytes

/-- Mutant 6 violates `parseRLEHeader_rule_digit_sets`. -/
theorem mutantRLEHeaderExactRule_violates_sets :
    mutantRLEHeaderExactRule "x = 1, y = 1, rule = B3/S32".toByteArray ≠
      parseRLEHeader "x = 1, y = 1, rule = B3/S32".toByteArray := by
  decide +kernel

/--
Mutant 7: a Macrocell deserializer that accepts a node of level 0, which the real one rejects.
-/
def mutantDeserializeMacrocellLevel0 (lines : Array String) : UInt32 :=
  if lines = #["[M2]", "0 0 0 0 0"] then 0 else (deserializeMacrocell lines).status

/-- Mutant 7 violates `deserializeMacrocell_level_0`. -/
theorem mutantDeserializeMacrocellLevel0_violates :
    mutantDeserializeMacrocellLevel0 #["[M2]", "0 0 0 0 0"] ≠ (deserializeMacrocell #["[M2]", "0 0 0 0 0"]).status := by
  decide +kernel

end Algorithm
