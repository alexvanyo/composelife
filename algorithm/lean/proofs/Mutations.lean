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
import theorems.BitComputationModelTheorems
import theorems.HashLifeComputationModelTheorems
import theorems.MacroCellCoordinatesModelTheorems
import theorems.GameOfLifeStepModelTheorems
import theorems.CellWindowModelTheorems

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Mutation proofs for `algorithm`

Each mutant below is a plausible buggy variant of a compiled function. For each one, we prove that it violates
the property the corresponding master theorem proves for the real function, so the master theorem would catch
the bug. `flat_capacity_hypotheses_satisfiable` shows that the hypotheses of the flat-engine capacity theorems can
all hold at once, so those theorems are not vacuous. The last section does the same for the standalone models of
hand-written Kotlin (`models/`).
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

/-- Mutant 3 violates `serializeLife106_eq`. -/
theorem mutantSerializeLife106_violates_header :
    mutantSerializeLife106MissingHeader #[] ≠
      #["#Life 1.06"] ++ (#[] : Array UInt64).map (fun k => formatCoordLine (cellKeyX k) (cellKeyY k)) := by
  decide +kernel

/--
Mutant 4: a Plaintext serializer that outputs dead cell "." even for live cells.
-/
def mutantSerializePlaintextAllDead (_cells : Array UInt64) (_minX _maxX _minY _maxY : Int32) :
    Array String := #["."]

/-- Mutant 4 violates `plaintext_round_trip_box`: the cell does not read back. -/
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
def mutantDeserializeMacrocellLevel0 (lines : Array String) : MacrocellStatus :=
  if lines = #["[M2]", "0 0 0 0 0"] then .ok else (deserializeMacrocell lines).status

/-- Mutant 7 violates `deserializeMacrocell_level_0`. -/
theorem mutantDeserializeMacrocellLevel0_violates :
    mutantDeserializeMacrocellLevel0 #["[M2]", "0 0 0 0 0"] ≠ (deserializeMacrocell #["[M2]", "0 0 0 0 0"]).status := by
  decide +kernel

/-! ## Models of hand-written Kotlin -/

namespace KotlinModel

/--
Mutant 8: a `centeredSubnodeLevel3` that takes the north-west nibble from bits `8..11` of the quadrant instead of
`12..15`.
-/
def mutantCenteredSubnodeLevel3 (w : UInt64) : UInt32 :=
  ((leafNwModel w >>> 8) &&& (15 : UInt32)) |||
  (((leafNeModel w >>> 8) &&& (15 : UInt32)) <<< 4) |||
  (((leafSwModel w >>> 4) &&& (15 : UInt32)) <<< 8) |||
  ((leafSeModel w &&& (15 : UInt32)) <<< 12)

/-- Mutant 8 violates `centeredSubnodeLevel3Model_correct`: the cell `(2, 2)` of the leaf is lost. -/
theorem mutantCenteredSubnodeLevel3_violates_correct :
    ¬ ∀ (w : UInt64) (lx ly : ℤ), 0 ≤ lx ∧ lx < 4 → 0 ≤ ly ∧ ly < 4 →
      grid4At (mutantCenteredSubnodeLevel3 w) lx ly = leafAt w (lx + 2) (ly + 2) := by
  intro h
  have := h 4096 0 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  revert this
  decide +kernel

/-- Mutant 9: a `leafToCoordinates` that transposes the leaf, emitting `(y, x)` for the cell at `(x, y)`. -/
def mutantLeafToCoordinatesTransposed (leaf : UInt64) (ox oy : Int32) : List (Int32 × Int32) :=
  (leafToCoordinatesModel leaf ox oy).map fun p => (p.2 - oy + ox, p.1 - ox + oy)

/-- Mutant 9 violates `coordinatesToLeaf_leafToCoordinates`: the cell `(0, 1)` comes back as `(1, 0)`. -/
theorem mutantLeafToCoordinatesTransposed_violates_round_trip :
    coordinatesToLeafModel (mutantLeafToCoordinatesTransposed 2 0 0) 0 0 ≠ 2 := by
  decide +kernel

/-- Mutant 10: a `coordinatesToLevel4` that offsets the north-east quadrant down and the south-west one right. -/
def mutantCoordinatesToLevel4Swapped (coords : List (Int32 × Int32)) (ox oy : Int32) : Level4Quads :=
  { nw := coordinatesToLeafModel coords ox oy
  , ne := coordinatesToLeafModel coords ox (oy + 8)
  , sw := coordinatesToLeafModel coords (ox + 8) oy
  , se := coordinatesToLeafModel coords (ox + 8) (oy + 8) }

/-- Mutant 10 violates `level4CellAt_coordinatesToLevel4Model`: the cell `(8, 0)` is lost. -/
theorem mutantCoordinatesToLevel4Swapped_violates_cells :
    ¬ ∀ (coords : List (Int32 × Int32)) (ox oy : Int32) (x y : ℤ), 0 ≤ x ∧ x < 16 → 0 ≤ y ∧ y < 16 →
      level4CellAt (mutantCoordinatesToLevel4Swapped coords ox oy).nw
          (mutantCoordinatesToLevel4Swapped coords ox oy).ne (mutantCoordinatesToLevel4Swapped coords ox oy).sw
          (mutantCoordinatesToLevel4Swapped coords ox oy).se x y =
        decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords) := by
  intro h
  have := h [(8, 0)] 0 0 8 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  revert this
  decide +kernel

/-- Mutant 11: a `stepGeneration` that also gives birth to dead cells with two neighbors. -/
def mutantStepGenerationBirthOnTwo (alive : List (Int32 × Int32)) : List (Int32 × Int32) :=
  let a := dedupCoords alive
  let candidates := dedupCoords ((a.flatMap mooreNeighbors32) ++ a)
  candidates.filter fun c =>
    let count := ((mooreNeighbors32 c).filter fun n => a.contains n).length
    count == 3 || count == 2

/-- Mutant 11 violates `mem_stepGenerationModel_iff_nextGenAt`: the dead middle of two cells comes alive. -/
theorem mutantStepGenerationBirthOnTwo_violates_rule :
    ¬ ∀ (alive : List (Int32 × Int32)) (c : Int32 × Int32),
      c ∈ mutantStepGenerationBirthOnTwo alive ↔
        nextGenAt (fun x y => decide ((Int32.ofInt x, Int32.ofInt y) ∈ alive)) c.1.toInt c.2.toInt = true := by
  intro h
  have := (h [(0, 0), (2, 0)] (1, 0)).mp (by decide +kernel)
  revert this
  decide +kernel

/-- Mutant 12: a `containedPoints` that lists the points column by column instead of row by row. -/
def mutantContainedPointsColumnMajor (w : CellWindowModel) : List (Int32 × Int32) :=
  (int32RangeUntil w.left w.right).flatMap fun x => (int32RangeUntil w.top w.bottom).map fun y => (x, y)

/--
Mutant 12 violates `CellWindowModel_containedPoints_getElem?` (it has the same points, so only the row-major
theorem catches it).
-/
theorem mutantContainedPointsColumnMajor_violates_row_major :
    (mutantContainedPointsColumnMajor ⟨0, 0, 2, 2⟩)[0 * 2 + 1]? ≠
      some (Int32.ofInt (0 + (1 : Nat)), Int32.ofInt (0 + (0 : Nat))) := by
  decide +kernel

/-- The hypotheses of `CellWindowModel_translate_containedPoints` hold together for a real translation. -/
theorem cellWindow_translate_hypotheses_satisfiable :
    ∃ (w w' : CellWindowModel) (dx dy : Int32), w.translate dx dy = some w' ∧
      w.left.toInt ≤ w.right.toInt ∧ w.top.toInt ≤ w.bottom.toInt ∧
      Int32.minValue.toInt ≤ w.left.toInt + dx.toInt ∧ w.right.toInt + dx.toInt ≤ Int32.maxValue.toInt ∧
      Int32.minValue.toInt ≤ w.top.toInt + dy.toInt ∧ w.bottom.toInt + dy.toInt ≤ Int32.maxValue.toInt :=
  ⟨⟨0, 0, 2, 3⟩, ⟨1, -1, 3, 2⟩, 1, -1, by decide +kernel⟩

end KotlinModel

end Algorithm
