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

import models.Basic
import models.FloatModel
import GeometryDefs
import proofs.FloatSemantics
import proofs.FloatBounds
import proofs.FloatAnalysis
import Geometry.LineSegment

namespace Geometry

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

/--
Identical cell collections trivially have Hausdorff distance 0 (and therefore ≤ 1).
-/
theorem cellHausdorffDistanceLe_refl (cells : List Cell) :
    cellHausdorffDistanceLe cells cells 0 := by
  constructor
  · intro c hc
    refine ⟨c, hc, ?_⟩
    unfold chebyshevDistance
    simp
  · intro c hc
    refine ⟨c, hc, ?_⟩
    unfold chebyshevDistance
    simp

theorem cellHausdorffDistanceLe_of_eq {cells1 cells2 : List Cell} (h : cells1 = cells2) :
    cellHausdorffDistanceLe cells1 cells2 1 := by
  subst h
  have h0 := cellHausdorffDistanceLe_refl cells1
  rcases h0 with ⟨h1, h2⟩
  constructor
  · intro c hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩
  · intro c hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩

/--
Concatenation preserves discrete cell Hausdorff distance bounds:
if `l1` is near `l2` and `r1` is near `r2`, then `l1 ++ r1` is near `l2 ++ r2`.
-/
theorem cellHausdorffDistanceLe_append {l1 r1 l2 r2 : List Cell} {d : Nat}
    (h_left : cellHausdorffDistanceLe l1 l2 d)
    (h_right : cellHausdorffDistanceLe r1 r2 d) :
    cellHausdorffDistanceLe (l1 ++ r1) (l2 ++ r2) d := by
  rcases h_left with ⟨hl1, hl2⟩
  rcases h_right with ⟨hr1, hr2⟩
  constructor
  · intro c hc
    simp only [List.mem_append] at hc ⊢
    rcases hc with h | h
    · rcases hl1 c h with ⟨c', hc', hd⟩
      exact ⟨c', Or.inl hc', hd⟩
    · rcases hr1 c h with ⟨c', hc', hd⟩
      exact ⟨c', Or.inr hc', hd⟩
  · intro c hc
    simp only [List.mem_append] at hc ⊢
    rcases hc with h | h
    · rcases hl2 c h with ⟨c', hc', hd⟩
      exact ⟨c', Or.inl hc', hd⟩
    · rcases hr2 c h with ⟨c', hc', hd⟩
      exact ⟨c', Or.inr hc', hd⟩

/--
Deduplication preserves discrete cell Hausdorff distance bounds.
-/
theorem cellHausdorffDistanceLe_dedupCells {l1 l2 : List Cell} {d : Nat}
    (h : cellHausdorffDistanceLe l1 l2 d) :
    cellHausdorffDistanceLe (dedupCells l1) (dedupCells l2) d := by
  rcases h with ⟨h1, h2⟩
  constructor
  · intro c hc
    rw [mem_dedupCells] at hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    refine ⟨c', by rwa [mem_dedupCells], hd⟩
  · intro c hc
    rw [mem_dedupCells] at hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    refine ⟨c', by rwa [mem_dedupCells], hd⟩

/--
Reduces the Hausdorff distance bound between deduplicated cell lists with matching endpoints
to proving that intermediate cells are within Chebyshev distance at most 1.
-/
theorem cellHausdorffDistanceLe_dedup_endpoints (s e : Cell) (rest1 rest2 : List Cell)
    (h1 : ∀ c1 ∈ rest1, ∃ c2 ∈ dedupCells ([s, e] ++ rest2), chebyshevDistance c1 c2 ≤ 1)
    (h2 : ∀ c2 ∈ rest2, ∃ c1 ∈ dedupCells ([s, e] ++ rest1), chebyshevDistance c1 c2 ≤ 1) :
    cellHausdorffDistanceLe (dedupCells ([s, e] ++ rest1)) (dedupCells ([s, e] ++ rest2)) 1 := by
  constructor
  · intro c1 hc1
    rw [mem_dedupCells] at hc1
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1
    rcases hc1 with (rfl | rfl) | hrest1
    · refine ⟨c1, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · refine ⟨c1, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · exact h1 c1 hrest1
  · intro c2 hc2
    rw [mem_dedupCells] at hc2
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2
    rcases hc2 with (rfl | rfl) | hrest2
    · refine ⟨c2, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · refine ⟨c2, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · exact h2 c2 hrest2

/--
Unconditional Hausdorff bound for segments within the same discrete grid cell.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_same_cell
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe (cellIntersectionsSegmentFloat A B) (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
  have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
  have h_same_ideal : floorPoint A.toPoint = floorPoint B.toPoint := by
    rw [← h_floorA, ← h_floorB, h_same]
  unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
  rw [h_same, h_same_ideal]
  simp
  rw [h_floorB]
  exact cellHausdorffDistanceLe_of_eq rfl

def FullDiamondTransition
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
   (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
   (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) ∨
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
   (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
   (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)

def RayMarchCasesFloatExt
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  -- Case 1: Step agreement
  ((rayMarchStepFloat start dx dy stepX stepY c).1 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2) ∨
  -- Case 2: 1-step terminal
  ((c == endCell) = true ∨ (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨ (rayMarchStepFloat start dx dy stepX stepY c).1 = endCell) ∨
  -- Case 3: 2-step terminal or corner-sync terminal (extended)
  ((rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 = endCell ∨
   (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).2 = true ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell) ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell) ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell)) ∨
  FullDiamondTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c

def RayMarchCasesIdealExt
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  -- Case 1: Step agreement
  ((rayMarchStepFloat start dx dy stepX stepY c).1 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2) ∨
  -- Case 2: 1-step terminal
  ((c == endCell) = true ∨ (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨ (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = endCell) ∨
  -- Case 3: 2-step terminal or corner-sync terminal (extended)
  ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 = endCell ∨
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).2 = true ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell) ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell) ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true) ∨
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
    (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell)) ∨
  FullDiamondTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c

theorem chebyshevDistance_corner_sync_le_one (c : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨c.x + stepX, c.y + stepY⟩ c ≤ 1 := by
  unfold chebyshevDistance
  dsimp only []
  have hx : (c.x + stepX - c.x).natAbs ≤ 1 := by
    have h : c.x + stepX - c.x = stepX := by ring
    rw [h]
    rcases hX with rfl | rfl | rfl <;> omega
  have hy : (c.y + stepY - c.y).natAbs ≤ 1 := by
    have h : c.y + stepY - c.y = stepY := by ring
    rw [h]
    rcases hY with rfl | rfl | rfl <;> omega
  exact max_le hx hy

theorem rayMarchFloat_two_step_terminal_near_rayMarch_endpoints_ext
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_termF2 : (rayMarchStepFloat start dx dy stepX stepY
                  (rayMarchStepFloat start dx dy stepX stepY current).1).1 = endCell ∨
                (rayMarchStepFloat start dx dy stepX stepY
                  (rayMarchStepFloat start dx dy stepX stepY current).1).2 = true ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x + stepX, current.y⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x, current.y + stepY⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x + stepX, current.y⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell) ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x, current.y + stepY⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell) ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStepFloat start dx dy stepX stepY current).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStepFloat start dx dy stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell))
    (c1 : Cell)
    (hc1 : c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current []) :
    ∃ c2 ∈ dedupCells ([current, endCell] ++
      rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
      chebyshevDistance c1 c2 ≤ 1 := by
  cases fuel with
  | zero =>
    unfold rayMarchFloat at hc1; cases hc1
  | succ fuel =>
    rw [rayMarchFloat_succ] at hc1
    dsimp only [] at hc1
    split_ifs at hc1 with hc hd
    · cases hc1
    · cases hc1
    · simp only [List.mem_cons] at hc1
      rcases hc1 with rfl | htail
      · refine ⟨current, ?_, ?_⟩
        · rw [mem_dedupCells]
          simp only [List.mem_append, List.mem_cons, true_or]
        · rw [chebyshevDistance_symm]
          exact chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY current
      · cases fuel with
        | zero =>
          unfold rayMarchFloat at htail; cases htail
        | succ fuel =>
          rw [rayMarchFloat_succ] at htail
          dsimp only [] at htail
          split_ifs at htail with hc2 hd2
          · cases htail
          · cases htail
          · simp only [List.mem_cons] at htail
            rcases htail with rfl | htail2
            · rcases h_termF2 with h_next2_end | h_next2_done | h_term3_xy | h_term3_yx | h_end3_xy | h_end3_yx | h_diag_done | h_diag_end
              · refine ⟨endCell, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or, or_true]
                · rw [h_next2_end, chebyshevDistance_self]; omega
              · exfalso; apply hd2; exact h_next2_done
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_term3_xy.1, h_term3_xy.2.1]
                  exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_term3_yx.1, h_term3_yx.2.1]
                  exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_end3_xy.1, h_end3_xy.2.1]
                  exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_end3_yx.1, h_end3_yx.2.1]
                  exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · exfalso; apply hd2; rw [h_diag_done.1, h_diag_done.2]
              · refine ⟨endCell, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or, or_true]
                · rw [h_diag_end.1, h_diag_end.2, chebyshevDistance_self]; omega
            · rcases h_termF2 with h_next2_end | h_next2_done | h_term3_xy | h_term3_yx | h_end3_xy | h_end3_yx | h_diag_done | h_diag_end
              · rw [h_next2_end, rayMarchFloat_endCell] at htail2
                cases htail2
              · exfalso; apply hd2; exact h_next2_done
              · cases fuel with
                | zero =>
                  unfold rayMarchFloat at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarchFloat_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_term3_xy.1, h_term3_xy.2.1, h_term3_xy.2.2] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply hd3; rfl
              · cases fuel with
                | zero =>
                  unfold rayMarchFloat at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarchFloat_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_term3_yx.1, h_term3_yx.2.1, h_term3_yx.2.2] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply hd3; rfl
              · cases fuel with
                | zero =>
                  unfold rayMarchFloat at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarchFloat_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_end3_xy.1, h_end3_xy.2.1] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · refine ⟨endCell, ?_, ?_⟩
                      · rw [mem_dedupCells]
                        simp only [List.mem_append, List.mem_cons, true_or, or_true]
                      · rw [h_end3_xy.2.2, chebyshevDistance_self]; omega
                    · rw [h_end3_xy.2.2, rayMarchFloat_endCell] at htail3
                      cases htail3
              · cases fuel with
                | zero =>
                  unfold rayMarchFloat at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarchFloat_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_end3_yx.1, h_end3_yx.2.1] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · refine ⟨endCell, ?_, ?_⟩
                      · rw [mem_dedupCells]
                        simp only [List.mem_append, List.mem_cons, true_or, or_true]
                      · rw [h_end3_yx.2.2, chebyshevDistance_self]; omega
                    · rw [h_end3_yx.2.2, rayMarchFloat_endCell] at htail3
                      cases htail3
              · exfalso; apply hd2; rw [h_diag_done.1, h_diag_done.2]
              · rw [h_diag_end.1, h_diag_end.2, rayMarchFloat_endCell] at htail2
                cases htail2

theorem rayMarch_two_step_terminal_near_rayMarchFloat_endpoints_ext
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_termI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY
                  (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1).1 = endCell ∨
                (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY
                  (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1).2 = true ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x + stepX, current.y⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x, current.y + stepY⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x + stepX, current.y⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell) ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x, current.y + stepY⟩).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell) ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).2 = true) ∨
                ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = ⟨current.x + stepX, current.y + stepY⟩ ∧
                 (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨current.x + stepX, current.y + stepY⟩).1 = endCell))
    (c2 : Cell)
    (hc2 : c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []) :
    ∃ c1 ∈ dedupCells ([current, endCell] ++
      rayMarchFloat fuel start dx dy stepX stepY endCell current []),
      chebyshevDistance c1 c2 ≤ 1 := by
  cases fuel with
  | zero =>
    unfold rayMarch at hc2; cases hc2
  | succ fuel =>
    rw [rayMarch_succ] at hc2
    dsimp only [] at hc2
    split_ifs at hc2 with hc hd
    · cases hc2
    · cases hc2
    · simp only [List.mem_cons] at hc2
      rcases hc2 with rfl | htail
      · refine ⟨current, ?_, ?_⟩
        · rw [mem_dedupCells]
          simp only [List.mem_append, List.mem_cons, true_or]
        · exact chebyshevDistance_step_le_one start.toPoint ptEnd dxQ dyQ stepX stepY hX hY current
      · cases fuel with
        | zero =>
          unfold rayMarch at htail; cases htail
        | succ fuel =>
          rw [rayMarch_succ] at htail
          dsimp only [] at htail
          split_ifs at htail with hc2 hd2
          · cases htail
          · cases htail
          · simp only [List.mem_cons] at htail
            rcases htail with rfl | htail2
            · rcases h_termI2 with h_next2_end | h_next2_done | h_term3_xy | h_term3_yx | h_end3_xy | h_end3_yx | h_diag_done | h_diag_end
              · refine ⟨endCell, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or, or_true]
                · rw [h_next2_end, chebyshevDistance_self]; omega
              · exfalso; apply hd2; exact h_next2_done
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_term3_xy.1, h_term3_xy.2.1]
                  rw [chebyshevDistance_symm]; exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_term3_yx.1, h_term3_yx.2.1]
                  rw [chebyshevDistance_symm]; exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_end3_xy.1, h_end3_xy.2.1]
                  rw [chebyshevDistance_symm]; exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · refine ⟨current, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or]
                · rw [h_end3_yx.1, h_end3_yx.2.1]
                  rw [chebyshevDistance_symm]; exact chebyshevDistance_corner_sync_le_one current stepX stepY hX hY
              · exfalso; apply hd2; rw [h_diag_done.1, h_diag_done.2]
              · refine ⟨endCell, ?_, ?_⟩
                · rw [mem_dedupCells]
                  simp only [List.mem_append, List.mem_cons, true_or, or_true]
                · rw [h_diag_end.1, h_diag_end.2, chebyshevDistance_self]; omega
            · rcases h_termI2 with h_next2_end | h_next2_done | h_term3_xy | h_term3_yx | h_end3_xy | h_end3_yx | h_diag_done | h_diag_end
              · rw [h_next2_end, rayMarch_endCell] at htail2
                cases htail2
              · exfalso; apply hd2; exact h_next2_done
              · cases fuel with
                | zero =>
                  unfold rayMarch at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarch_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_term3_xy.1, h_term3_xy.2.1, h_term3_xy.2.2] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply hd3; rfl
              · cases fuel with
                | zero =>
                  unfold rayMarch at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarch_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_term3_yx.1, h_term3_yx.2.1, h_term3_yx.2.2] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply hd3; rfl
              · cases fuel with
                | zero =>
                  unfold rayMarch at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarch_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_end3_xy.1, h_end3_xy.2.1] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · refine ⟨endCell, ?_, ?_⟩
                      · rw [mem_dedupCells]
                        simp only [List.mem_append, List.mem_cons, true_or, or_true]
                      · rw [h_end3_xy.2.2, chebyshevDistance_self]; omega
                    · rw [h_end3_xy.2.2, rayMarch_endCell] at htail3
                      cases htail3
              · cases fuel with
                | zero =>
                  unfold rayMarch at htail2; cases htail2
                | succ fuel =>
                  rw [rayMarch_succ] at htail2
                  dsimp only [] at htail2
                  rw [h_end3_yx.1, h_end3_yx.2.1] at htail2
                  split_ifs at htail2 with hc3 hd3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · refine ⟨endCell, ?_, ?_⟩
                      · rw [mem_dedupCells]
                        simp only [List.mem_append, List.mem_cons, true_or, or_true]
                      · rw [h_end3_yx.2.2, chebyshevDistance_self]; omega
                    · rw [h_end3_yx.2.2, rayMarch_endCell] at htail3
                      cases htail3
              · exfalso; apply hd2; rw [h_diag_done.1, h_diag_done.2]
              · rw [h_diag_end.1, h_diag_end.2, rayMarch_endCell] at htail2
                cases htail2

theorem rayMarch_mono_fuel (fuel1 fuel2 : ℕ) (start ptEnd : Point)
    (dx dy : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (hle : fuel1 ≤ fuel2) :
    ∀ c ∈ rayMarch fuel1 start ptEnd dx dy stepX stepY endCell current [],
      c ∈ rayMarch fuel2 start ptEnd dx dy stepX stepY endCell current [] := by
  induction fuel1 generalizing fuel2 current with
  | zero =>
    intro c hc
    cases hc
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      intro c hc
      rw [rayMarch_succ] at hc ⊢
      dsimp only [] at hc ⊢
      split_ifs at hc ⊢ with h_end h_done
      · cases hc
      · cases hc
      · simp only [List.mem_cons] at hc ⊢
        rcases hc with rfl | htail
        · left; rfl
        · right; exact ih f2 (rayMarchStep start ptEnd dx dy stepX stepY current).1 (by omega) c htail

theorem rayMarchFloat_mono_fuel (fuel1 fuel2 : ℕ) (start : Point32)
    (dx dy : Binary64) (stepX stepY : ℤ) (endCell current : Cell)
    (hle : fuel1 ≤ fuel2) :
    ∀ c ∈ rayMarchFloat fuel1 start dx dy stepX stepY endCell current [],
      c ∈ rayMarchFloat fuel2 start dx dy stepX stepY endCell current [] := by
  induction fuel1 generalizing fuel2 current with
  | zero =>
    intro c hc
    cases hc
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      intro c hc
      rw [rayMarchFloat_succ] at hc ⊢
      dsimp only [] at hc ⊢
      split_ifs at hc ⊢ with h_end h_done
      · cases hc
      · cases hc
      · simp only [List.mem_cons] at hc ⊢
        rcases hc with rfl | htail
        · left; rfl
        · right; exact ih f2 (rayMarchStepFloat start dx dy stepX stepY current).1 (by omega) c htail

theorem rayMarchFloat_half_diamond_xy_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  rw [rayMarchFloat_succ_succ fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2] at hc1
  have hI_unfold : rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarch_succ (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepI1 h_not_doneI1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hI_unfold]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | rfl | htail
  · refine ⟨c, ?_, h_sync.2.2.2.1⟩
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or]
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; left; rfl
    · left; right; rfl
    · right; right
      exact rayMarch_mono_fuel fuel (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
        ⟨c.x + stepX, c.y + stepY⟩ (by omega) c2 hmem

theorem rayMarchFloat_half_diamond_yx_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  rw [rayMarchFloat_succ_succ_symm fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2] at hc1
  have hI_unfold : rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarch_succ (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepI1 h_not_doneI1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hI_unfold]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | rfl | htail
  · refine ⟨c, ?_, h_sync.2.2.2.2⟩
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or]
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; left; rfl
    · left; right; rfl
    · right; right
      exact rayMarch_mono_fuel fuel (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
        ⟨c.x + stepX, c.y + stepY⟩ (by omega) c2 hmem

theorem rayMarch_half_diamond_xy_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  rw [rayMarch_succ_succ_symm fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2] at hc2
  have hF_unfold : rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepF1 h_not_doneF1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hF_unfold]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | rfl | htail
  · refine ⟨c, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or]
    · rw [chebyshevDistance_symm]; exact h_sync.2.2.2.1
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; left; rfl
    · left; right; rfl
    · right; right
      exact rayMarchFloat_mono_fuel fuel (fuel + 1) start dx dy stepX stepY endCell
        ⟨c.x + stepX, c.y + stepY⟩ (by omega) c1 hmem

theorem rayMarch_half_diamond_yx_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  rw [rayMarch_succ_succ fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2] at hc2
  have hF_unfold : rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepF1 h_not_doneF1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hF_unfold]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | rfl | htail
  · refine ⟨c, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or]
    · rw [chebyshevDistance_symm]; exact h_sync.2.2.2.2
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; left; rfl
    · left; right; rfl
    · right; right
      exact rayMarchFloat_mono_fuel fuel (fuel + 1) start dx dy stepX stepY endCell
        ⟨c.x + stepX, c.y + stepY⟩ (by omega) c1 hmem

def HalfDiamondFloatTransition
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  -- 1. Float 2-step (X then Y), Ideal 1-step diagonal
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
   (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩) ∨
  -- 2. Float 2-step (Y then X), Ideal 1-step diagonal
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
   (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)

def HalfDiamondIdealTransition
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  -- 1. Float 1-step diagonal, Ideal 2-step (X then Y)
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
   (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) ∨
  -- 2. Float 1-step diagonal, Ideal 2-step (Y then X)
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
   (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)

theorem rayMarch_eq_of_dist_lt
    (fuel1 fuel2 : ℕ) (start ptEnd : Point) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (P : Cell → Prop) (hP : P current)
    (h_dist : ∀ c, P c →
      (c == endCell) = false → (rayMarchStep start ptEnd dxQ dyQ stepX stepY c).2 = false →
      P (rayMarchStep start ptEnd dxQ dyQ stepX stepY c).1 ∧
      (endCell.x - (rayMarchStep start ptEnd dxQ dyQ stepX stepY c).1.x).natAbs +
      (endCell.y - (rayMarchStep start ptEnd dxQ dyQ stepX stepY c).1.y).natAbs <
      (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs)
    (h1 : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs < fuel1)
    (h2 : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs < fuel2) :
    rayMarch fuel1 start ptEnd dxQ dyQ stepX stepY endCell current [] =
    rayMarch fuel2 start ptEnd dxQ dyQ stepX stepY endCell current [] := by
  induction fuel1 generalizing fuel2 current with
  | zero => omega
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      rw [rayMarch_succ f1, rayMarch_succ f2]
      dsimp only []
      cases h_end : (current == endCell)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases h_done : (rayMarchStep start ptEnd dxQ dyQ stepX stepY current).2
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [rayMarch_acc f1, rayMarch_acc f2]
          simp only [List.nil_append, List.cons.injEq, true_and]
          obtain ⟨hP_next, h_step_lt⟩ := h_dist current hP h_end h_done
          exact ih f2 (rayMarchStep start ptEnd dxQ dyQ stepX stepY current).1
            hP_next (by omega) (by omega)
        · simp
      · simp

theorem rayMarchFloat_half_diamond_diag_xy_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] =
                 rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [])
    (ih : ∀ c1 ∈ rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  have hF_unfold : rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepF1 h_not_doneF1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hF_unfold] at hc1
  rw [rayMarch_succ_succ_symm fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2]
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | htail
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [h_fuel_eq] at hc2
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

theorem rayMarchFloat_half_diamond_diag_yx_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] =
                 rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [])
    (ih : ∀ c1 ∈ rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  have hF_unfold : rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepF1 h_not_doneF1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hF_unfold] at hc1
  rw [rayMarch_succ_succ fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2]
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | htail
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [h_fuel_eq] at hc2
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

theorem rayMarch_half_diamond_diag_xy_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] =
                 rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [])
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  have hI_unfold : rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarch_succ (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepI1 h_not_doneI1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rayMarch_acc (fuel + 1)]
    simp only [List.nil_append, h_fuel_eq]
  rw [hI_unfold] at hc2
  rw [rayMarchFloat_succ_succ fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2]
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | htail
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

theorem rayMarch_half_diamond_diag_yx_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] =
                 rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [])
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  have hI_unfold : rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
    rw [rayMarch_succ (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c) = (⟨c.x + stepX, c.y + stepY⟩, false) from
      Prod.ext h_stepI1 h_not_doneI1]
    dsimp only []
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rayMarch_acc (fuel + 1)]
    simp only [List.nil_append, h_fuel_eq]
  rw [hI_unfold] at hc2
  rw [rayMarchFloat_succ_succ_symm fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2]
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | htail
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

def RayMarchCasesFloatExt3
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  RayMarchCasesFloatExt start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  HalfDiamondFloatTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  HalfDiamondIdealTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c

def RayMarchCasesIdealExt3
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  RayMarchCasesIdealExt start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  HalfDiamondIdealTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  HalfDiamondFloatTransition start ptEnd dx dy dxQ dyQ stepX stepY endCell c

theorem rayMarchFloat_near_rayMarch_of_cases_visited2
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (P : Cell → Prop) (hP : P current)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_fuel : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs + 2 ≤ fuel)
    (h_dist_I : ∀ c, P c →
      (c == endCell) = false → (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false →
      P (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (endCell.x - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.x).natAbs +
      (endCell.y - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.y).natAbs <
      (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ →
        (endCell.x - (c.x + stepX)).natAbs + (endCell.y - (c.y + stepY)).natAbs + 2 ≤
        (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs))
    (h_cases : ∀ c, P c →
      RayMarchCasesFloatExt3 start ptEnd dx dy dxQ dyQ stepX stepY endCell c) :
    ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current [],
      ∃ c2 ∈ dedupCells ([current, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel using Nat.strong_induction_on generalizing current with
  | h fuel ih =>
    intro c1 hc1
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rcases h_cases current hP with (h_agree | h_term1 | h_term2 | h_dia | h_diasymm) | (h_hd_xy | h_hd_yx) | (h_hdi_xy | h_hdi_yx)
        · have h_not_end : (current == endCell) = false := by
            cases h : (current == endCell)
            · rfl
            · rw [rayMarchFloat_succ] at hc1; dsimp only [] at hc1; rw [h] at hc1; cases hc1
          have hdF : (rayMarchStepFloat start dx dy stepX stepY current).2 = false := by
            cases h : (rayMarchStepFloat start dx dy stepX stepY current).2
            · rfl
            · rw [rayMarchFloat_succ] at hc1; dsimp only [] at hc1; rw [h_not_end, h] at hc1; cases hc1
          have hdI : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = false := by
            rw [← h_agree.2]; exact hdF
          obtain ⟨hP_next, h_step_d, _⟩ := h_dist_I current hP h_not_end hdI
          rw [← h_agree.1] at hP_next h_step_d
          have h_rec := ih (fuel + 1) (by omega) (rayMarchStepFloat start dx dy stepX stepY current).1
            hP_next (by omega)
          have h_rec' : ∀ c1 ∈ rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell
              (rayMarchStepFloat start dx dy stepX stepY current).1 [],
            ∃ c2 ∈ dedupCells ([(rayMarchStepFloat start dx dy stepX stepY current).1, endCell] ++
              rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
                (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 []),
              chebyshevDistance c1 c2 ≤ 1 := by
            intro c1' hc1'
            rcases h_rec c1' hc1' with ⟨c2, hc2, hd2⟩
            refine ⟨c2, ?_, hd2⟩
            rw [← h_agree.1]
            exact hc2
          exact rayMarchFloat_step_agree_near_rayMarch_endpoints (fuel + 1) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_agree.1 h_agree.2 h_rec' c1 hc1
        · exact rayMarchFloat_terminal_near_rayMarch_endpoints (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current h_term1 c1 hc1
        · exact rayMarchFloat_two_step_terminal_near_rayMarch_endpoints_ext (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_term2 c1 hc1
        · rcases h_dia with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_diamond_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c1 hc1
        · rcases h_diasymm with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_diamond_symm_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c1 hc1
        · rcases h_hd_xy with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1⟩
          obtain ⟨hP2, _, hd_diag⟩ := h_dist_I current hP hne hndI1
          have hd2 : (endCell.x - (⟨current.x + stepX, current.y + stepY⟩ : Cell).x).natAbs +
              (endCell.y - (⟨current.x + stepX, current.y + stepY⟩ : Cell).y).natAbs + 2 ≤
              (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs := hd_diag hstI1
          rw [hstI1] at hP2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_half_diamond_xy_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 h_rec c1 hc1
        · rcases h_hd_yx with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1⟩
          obtain ⟨hP2, _, hd_diag⟩ := h_dist_I current hP hne hndI1
          have hd2 : (endCell.x - (⟨current.x + stepX, current.y + stepY⟩ : Cell).x).natAbs +
              (endCell.y - (⟨current.x + stepX, current.y + stepY⟩ : Cell).y).natAbs + 2 ≤
              (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs := hd_diag hstI1
          rw [hstI1] at hP2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_half_diamond_yx_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 h_rec c1 hc1
        · rcases h_hdi_xy with ⟨hne, hndF1, hstF1, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] =
              rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] :=
            rayMarch_eq_of_dist_lt (fuel + 1) fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩
              P hP2 (fun c hc hne_c hnd_c => ⟨(h_dist_I c hc hne_c hnd_c).1, (h_dist_I c hc hne_c hnd_c).2.1⟩) (by omega) (by omega)
          have h_rec := ih (fuel + 1) (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_half_diamond_diag_xy_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hne hndF1 hstF1 hndI1 hstI1 hneI1 hndI2 hstI2 h_fuel_eq h_rec c1 hc1
        · rcases h_hdi_yx with ⟨hne, hndF1, hstF1, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] =
              rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] :=
            rayMarch_eq_of_dist_lt (fuel + 1) fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩
              P hP2 (fun c hc hne_c hnd_c => ⟨(h_dist_I c hc hne_c hnd_c).1, (h_dist_I c hc hne_c hnd_c).2.1⟩) (by omega) (by omega)
          have h_rec := ih (fuel + 1) (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_half_diamond_diag_yx_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hne hndF1 hstF1 hndI1 hstI1 hneI1 hndI2 hstI2 h_fuel_eq h_rec c1 hc1

theorem rayMarch_near_rayMarchFloat_of_cases_visited2
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (P : Cell → Prop) (hP : P current)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_fuel : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs + 2 ≤ fuel)
    (h_dist_I : ∀ c, P c →
      (c == endCell) = false → (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false →
      P (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (endCell.x - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.x).natAbs +
      (endCell.y - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.y).natAbs <
      (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ →
        (endCell.x - (c.x + stepX)).natAbs + (endCell.y - (c.y + stepY)).natAbs + 2 ≤
        (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs))
    (h_cases : ∀ c, P c →
      RayMarchCasesIdealExt3 start ptEnd dx dy dxQ dyQ stepX stepY endCell c) :
    ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current [],
      ∃ c1 ∈ dedupCells ([current, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel using Nat.strong_induction_on generalizing current with
  | h fuel ih =>
    intro c2 hc2
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rcases h_cases current hP with (h_agree | h_term1 | h_term2 | h_dia | h_diasymm) | (h_hd_xy | h_hd_yx) | (h_hdf_xy | h_hdf_yx)
        · have h_not_end : (current == endCell) = false := by
            cases h : (current == endCell)
            · rfl
            · rw [rayMarch_succ] at hc2; dsimp only [] at hc2; rw [h] at hc2; cases hc2
          have hdI : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = false := by
            cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2
            · rfl
            · rw [rayMarch_succ] at hc2; dsimp only [] at hc2; rw [h_not_end, h] at hc2; cases hc2
          obtain ⟨hP_next, h_step_d, _⟩ := h_dist_I current hP h_not_end hdI
          have h_rec := ih (fuel + 1) (by omega) (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1
            hP_next (by omega)
          have h_rec' : ∀ c2 ∈ rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
              (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 [],
            ∃ c1 ∈ dedupCells ([(rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1, endCell] ++
              rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell
                (rayMarchStepFloat start dx dy stepX stepY current).1 []),
              chebyshevDistance c1 c2 ≤ 1 := by
            intro c2' hc2'
            rcases h_rec c2' hc2' with ⟨c1, hc1, hd1⟩
            refine ⟨c1, ?_, hd1⟩
            rw [h_agree.1]
            exact hc1
          exact rayMarch_step_agree_near_rayMarchFloat_endpoints (fuel + 1) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_agree.1 h_agree.2 h_rec' c2 hc2
        · exact rayMarch_terminal_near_rayMarchFloat_endpoints (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current h_term1 c2 hc2
        · exact rayMarch_two_step_terminal_near_rayMarchFloat_endpoints_ext (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_term2 c2 hc2
        · rcases h_dia with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_diamond_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2
        · rcases h_diasymm with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_diamond_symm_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2
        · rcases h_hd_xy with ⟨hne, hndF1, hstF1, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_half_diamond_xy_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2
        · rcases h_hd_yx with ⟨hne, hndF1, hstF1, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1, _⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2, _⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_half_diamond_yx_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2
        · rcases h_hdf_xy with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1⟩
          obtain ⟨hP2, _, hd_diag⟩ := h_dist_I current hP hne hndI1
          have hd2 : (endCell.x - (⟨current.x + stepX, current.y + stepY⟩ : Cell).x).natAbs +
              (endCell.y - (⟨current.x + stepX, current.y + stepY⟩ : Cell).y).natAbs + 2 ≤
              (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs := hd_diag hstI1
          rw [hstI1] at hP2
          have h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] =
              rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] :=
            rayMarch_eq_of_dist_lt (fuel + 1) fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩
              P hP2 (fun c hc hne_c hnd_c => ⟨(h_dist_I c hc hne_c hnd_c).1, (h_dist_I c hc hne_c hnd_c).2.1⟩) (by omega) (by omega)
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_half_diamond_diag_xy_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 h_fuel_eq h_rec c2 hc2
        · rcases h_hdf_yx with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1⟩
          obtain ⟨hP2, _, hd_diag⟩ := h_dist_I current hP hne hndI1
          have hd2 : (endCell.x - (⟨current.x + stepX, current.y + stepY⟩ : Cell).x).natAbs +
              (endCell.y - (⟨current.x + stepX, current.y + stepY⟩ : Cell).y).natAbs + 2 ≤
              (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs := hd_diag hstI1
          rw [hstI1] at hP2
          have h_fuel_eq : rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] =
              rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩ [] :=
            rayMarch_eq_of_dist_lt (fuel + 1) fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨current.x + stepX, current.y + stepY⟩
              P hP2 (fun c hc hne_c hnd_c => ⟨(h_dist_I c hc hne_c hnd_c).1, (h_dist_I c hc hne_c hnd_c).2.1⟩) (by omega) (by omega)
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_half_diamond_diag_yx_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 h_fuel_eq h_rec c2 hc2

theorem cellIntersectionsSegmentFloat_hausdorff_bound_of_cases_visited2
    (A B : Point32)
    (P : Cell → Prop)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_stepX : (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0) =
      (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0))
    (h_stepY : (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) =
      (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0))
    (hP_start : P (floorPoint A.toPoint))
    (h_dist_I : ∀ c, P c →
      (c == floorPoint B.toPoint) = false →
      (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) c).2 = false →
      P (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) c).1 ∧
      ((floorPoint B.toPoint).x - (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) c).1.x).natAbs +
      ((floorPoint B.toPoint).y - (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) c).1.y).natAbs <
      ((floorPoint B.toPoint).x - c.x).natAbs + ((floorPoint B.toPoint).y - c.y).natAbs ∧
      ((rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) c).1 =
        ⟨c.x + (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0),
         c.y + (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)⟩ →
        ((floorPoint B.toPoint).x - (c.x + (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0))).natAbs +
        ((floorPoint B.toPoint).y - (c.y + (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0))).natAbs + 2 ≤
        ((floorPoint B.toPoint).x - c.x).natAbs + ((floorPoint B.toPoint).y - c.y).natAbs))
    (h_cases_F : ∀ c, P c →
      RayMarchCasesFloatExt3 A B.toPoint (deltaX A B) (deltaY A B)
        (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
        (floorPoint B.toPoint) c)
    (h_cases_I : ∀ c, P c →
      RayMarchCasesIdealExt3 A B.toPoint (deltaX A B) (deltaY A B)
        (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
        (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
        (floorPoint B.toPoint) c) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  by_cases h_same : floorPoint32 A = floorPoint32 B
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_same_cell A B h_finiteA h_finiteB h_same
  · have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
    have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
    have h_same_ideal : floorPoint A.toPoint ≠ floorPoint B.toPoint := by
      rw [← h_floorA, ← h_floorB]; exact h_same
    have h_same_bool : (floorPoint32 A == floorPoint32 B) = false := by
      cases h : (floorPoint32 A == floorPoint32 B)
      · rfl
      · exfalso; apply h_same; rw [eq_of_beq h]
    have h_same_ideal_bool : (floorPoint A.toPoint == floorPoint B.toPoint) = false := by
      cases h : (floorPoint A.toPoint == floorPoint B.toPoint)
      · rfl
      · exfalso; apply h_same_ideal; rw [eq_of_beq h]
    unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
    dsimp only []
    rw [h_same_bool, h_same_ideal_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_floorA, h_floorB]
    have hX : (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0) = -1 ∨
              (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0) = 0 ∨
              (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0) = 1 := by
      split_ifs <;> simp
    have hY : (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) = -1 ∨
              (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) = 0 ∨
              (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) = 1 := by
      split_ifs <;> simp
    have h1 := rayMarchFloat_near_rayMarch_of_cases_visited2
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (deltaX A B) (deltaY A B)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
      (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      P hP_start hX hY (le_refl _) h_dist_I h_cases_F
    have h2 := rayMarch_near_rayMarchFloat_of_cases_visited2
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (deltaX A B) (deltaY A B)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
      (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      P hP_start hX hY (le_refl _) h_dist_I h_cases_I
    rw [← h_stepX, ← h_stepY]
    apply cellHausdorffDistanceLe_dedup_endpoints
    · exact h1
    · exact h2

end Geometry