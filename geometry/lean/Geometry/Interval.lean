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

import Geometry.Basic
import Geometry.LineSegment
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry


/--
Checks whether cell `c` is inside the bounding box formed by the floored endpoints `A` and `B`.
-/
def inBoundingBox (c : Cell) (A B : Point) : Bool :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let minX := min startCell.x endCell.x
  let maxX := max startCell.x endCell.x
  let minY := min startCell.y endCell.y
  let maxY := max startCell.y endCell.y
  minX <= c.x && c.x <= maxX && minY <= c.y && c.y <= maxY

/--
Computes the parameter interval [tEnter, tExit] ⊆ [0, 1] along the segment `A + t(B - A)`
that falls within the closed unit square [c.x, c.x + 1] × [c.y, c.y + 1].
Returns `none` if the segment does not intersect the cell's closed area.
-/
def cellIntersectionInterval (c : Cell) (A B : Point) : Option (Rat × Rat) :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let cx0 := ofInt c.x
  let cx1 := ofInt (c.x + 1)
  let cy0 := ofInt c.y
  let cy1 := ofInt (c.y + 1)
  let (tx0, tx1) :=
    if dx == 0 then
      if A.x < cx0 || A.x > cx1 then (1, 0) else (0, 1)
    else if dx > 0 then
      ((cx0 - A.x) / dx, (cx1 - A.x) / dx)
    else
      ((cx1 - A.x) / dx, (cx0 - A.x) / dx)
  let (ty0, ty1) :=
    if dy == 0 then
      if A.y < cy0 || A.y > cy1 then (1, 0) else (0, 1)
    else if dy > 0 then
      ((cy0 - A.y) / dy, (cy1 - A.y) / dy)
    else
      ((cy1 - A.y) / dy, (cy0 - A.y) / dy)
  let tEnter := max 0 (max tx0 ty0)
  let tExit := min 1 (min tx1 ty1)
  if tEnter <= tExit then
    some (tEnter, tExit)
  else
    none

/--
Returns true if the line segment from `A` to `B` intersects cell `c`.
-/
def segmentIntersectsCellBool (c : Cell) (A B : Point) : Bool :=
  if c == floorPoint A || c == floorPoint B then
    true
  else if !inBoundingBox c A B then
    false
  else
    match cellIntersectionInterval c A B with
    | some _ => true
    | none => false

/--
Returns true if cell `c` has an off-axis corner contact with the segment:
it touches the segment at a single corner point, does not enter the interior,
and is not an endpoint cell (start or end).
-/
def isOffAxisCornerBool (c : Cell) (A B : Point) : Bool :=
  if c == floorPoint A || c == floorPoint B then
    false
  else if !inBoundingBox c A B then
    false
  else
    match cellIntersectionInterval c A B with
    | some (tEnter, tExit) => tEnter == tExit
    | none => false

/--
Generates all candidate grid cells within the bounding box of endpoints `A` and `B`.
-/
def candidateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let minX := min startCell.x endCell.x
  let maxX := max startCell.x endCell.x
  let minY := min startCell.y endCell.y
  let maxY := max startCell.y endCell.y
  let xCount := (maxX - minX + 1).toNat
  let yCount := (maxY - minY + 1).toNat
  (List.range xCount).flatMap (fun dx =>
    (List.range yCount).map (fun dy =>
      ⟨minX + Int.ofNat dx, minY + Int.ofNat dy⟩))

/--
Candidate cells strictly between the endpoints that are actively intersected by the line segment.
-/
def intermediateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  (candidateCells A B).filter (fun c =>
    (c != startCell) && (c != endCell) && segmentIntersectsCellBool c A B && !isOffAxisCornerBool c A B)

/--
Intermediate cells traversed via ray-marching in O(W + H) time.
-/
def rayMarchIntermediateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let dx := B.x - A.x
  let dy := B.y - A.y
  let stepX : Int := if dx > 0 then 1 else if dx < 0 then -1 else 0
  let stepY : Int := if dy > 0 then 1 else if dy < 0 then -1 else 0
  let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
  (rayMarch maxSteps A B dx dy stepX stepY endCell startCell []).filter (fun c =>
    (c != startCell) && (c != endCell) && !isOffAxisCornerBool c A B)

/--
Continuous segment membership: point `p` lies on the directed line segment between `A` and `B`.
-/
inductive PointOnSegment (p A B : Point) : Prop where
  | start : p = A → PointOnSegment p A B
  | ptEnd : p = B → PointOnSegment p A B
  | interior (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (hx : p.x = A.x + t * (B.x - A.x))
      (hy : p.y = A.y + t * (B.y - A.y)) : PointOnSegment p A B

/--
A cell is traversed by the line segment if some continuous point on the segment
falls into that half-open grid cell [c.x, c.x + 1) × [c.y, c.y + 1).
-/
def CellTraversedBySegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧ floorPoint p = c

/--
A cell touches the closed line segment if some continuous point on the segment
lies within the closed unit square [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def CellTouchesSegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧
    ofInt c.x ≤ p.x ∧ p.x ≤ ofInt (c.x + 1) ∧
    ofInt c.y ≤ p.y ∧ p.y ≤ ofInt (c.y + 1)

/--
An isolated corner contact occurs when a cell touches the closed segment,
but the line does not traverse the half-open cell (i.e. strictly diagonal corner contact).
-/
def IsIsolatedCornerContact (c : Cell) (A B : Point) : Prop :=
  CellTouchesSegment c A B ∧ ¬ CellTraversedBySegment c A B

/--
A cell's closed bounding square in the continuous 2D plane: [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def InClosedCell (c : Cell) (p : Point) : Prop :=
  ofInt c.x ≤ p.x ∧ p.x ≤ ofInt (c.x + 1) ∧
  ofInt c.y ≤ p.y ∧ p.y ≤ ofInt (c.y + 1)

/--
A cell's open interior in the continuous 2D plane: (c.x, c.x + 1) × (c.y, c.y + 1).
-/
def InInteriorCell (c : Cell) (p : Point) : Prop :=
  ofInt c.x < p.x ∧ p.x < ofInt (c.x + 1) ∧
  ofInt c.y < p.y ∧ p.y < ofInt (c.y + 1)

/--
A point is one of the four corner vertices of cell c.
-/
def IsCellCorner (c : Cell) (p : Point) : Prop :=
  (p.x = ofInt c.x ∨ p.x = ofInt (c.x + 1)) ∧
  (p.y = ofInt c.y ∨ p.y = ofInt (c.y + 1))

/--
A cell touches the closed line segment between A and B if:
1. It is the starting cell (floorPoint A) or ending cell (floorPoint B).
2. It is a candidate cell in the bounding box and segmentIntersectsCellBool is true.
-/
def SegmentIntersectsCell (c : Cell) (A B : Point) : Prop :=
  c = floorPoint A ∨ c = floorPoint B ∨ (c ∈ candidateCells A B ∧ segmentIntersectsCellBool c A B = true)

/--
A cell has an off-axis corner intersection with the segment between A and B if:
1. It is not the starting cell (floorPoint A) or ending cell (floorPoint B).
2. isOffAxisCornerBool is true.
-/
def IsOffAxisCornerIntersection (c : Cell) (A B : Point) : Prop :=
  c ≠ floorPoint A ∧ c ≠ floorPoint B ∧ isOffAxisCornerBool c A B = true

/--
A cell is an active intersected cell of segment AB:
it intersects the segment and is NOT an off-axis corner intersection.
-/
def ActiveIntersectedCell (c : Cell) (A B : Point) : Prop :=
  SegmentIntersectsCell c A B ∧ ¬ IsOffAxisCornerIntersection c A B

/--
Helper: Consecutive pairs along a polyline path.
-/
def consecutivePairs : List Point → List (Point × Point)
  | [] => []
  | [_] => []
  | p1 :: p2 :: rest => (p1, p2) :: consecutivePairs (p2 :: rest)

/--
A cell is an active intersected cell of a polyline path:
either it is the sole floored cell of a singleton path, or it is an active intersected cell
of at least one segment along the path.
-/
def ActiveIntersectedCellPath : List Point → Cell → Prop
  | [], _ => False
  | [p], c => c = floorPoint p
  | p1 :: p2 :: rest, c => ActiveIntersectedCell c p1 p2 ∨ ActiveIntersectedCellPath (p2 :: rest) c

/-!
# Foundational Lemmas: Cells and Deduplication
-/

/--
Theorem: Membership in dedupCells is equivalent to membership in the original list.
-/
@[simp]
theorem mem_dedupCells (c : Cell) (cells : List Cell) : c ∈ dedupCells cells ↔ c ∈ cells :=
  List.mem_eraseDups

/--
Theorem: Two cells are equal if and only if both their x and y coordinates are equal.
-/
theorem cell_ext {c1 c2 : Cell} (hx : c1.x = c2.x) (hy : c1.y = c2.y) : c1 = c2 := by
  cases c1; cases c2
  congr

/--
Theorem: Deduplicating a list of two identical cells yields the singleton cell.
-/
theorem dedupCells_same (c : Cell) : dedupCells [c, c] = [c] := by
  unfold dedupCells
  rw [List.eraseDups_cons]
  have _hbeq : (c == c) = true := beq_self_eq_true c
  simp [List.eraseDups_nil]

/--
Theorem: Deduplicating a two-element list of distinct cells returns the original list.
-/
theorem dedupCells_pair {c1 c2 : Cell} (hne : c1 ≠ c2) :
    dedupCells [c1, c2] = [c1, c2] := by
  unfold dedupCells
  rw [List.eraseDups_cons]
  have hbeq : (c2 == c1) = false := by
    rw [Bool.eq_false_iff]
    intro heq
    have hcell : c2 = c1 := eq_of_beq heq
    exact hne hcell.symm
  simp [hbeq]
  rw [List.eraseDups_cons]
  simp [List.eraseDups_nil]

/--
Theorem: Manhattan distance between identical cells is zero.
-/
theorem manhattanDistance_self (c : Cell) :
    manhattanDistance c c = 0 := by
  unfold manhattanDistance
  simp

/--
Theorem: Chebyshev distance between identical cells is zero.
-/
theorem chebyshevDistance_self (c : Cell) :
    chebyshevDistance c c = 0 := by
  unfold chebyshevDistance
  simp

/--
Theorem: Chebyshev distance is always bounded above by Manhattan distance.
-/
theorem chebyshev_le_manhattan (a b : Cell) :
    chebyshevDistance a b ≤ manhattanDistance a b := by
  unfold chebyshevDistance manhattanDistance
  omega

/--
Theorem: Manhattan distance between two cells is zero if and only if the cells are identical.
-/
theorem manhattanDistance_eq_zero (a b : Cell) :
    manhattanDistance a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold manhattanDistance at h
    have hx : (a.x - b.x).natAbs = 0 := by omega
    have hy : (a.y - b.y).natAbs = 0 := by omega
    have hx2 : a.x = b.x := by
      have := Int.natAbs_eq_zero.mp hx
      omega
    have hy2 : a.y = b.y := by
      have := Int.natAbs_eq_zero.mp hy
      omega
    exact cell_ext hx2 hy2
  · intro h
    rw [h]
    exact manhattanDistance_self b

/--
Theorem: Manhattan distance is symmetric.
-/
theorem manhattanDistance_comm (a b : Cell) :
    manhattanDistance a b = manhattanDistance b a := by
  unfold manhattanDistance
  omega

/--
Theorem: Chebyshev distance is symmetric.
-/
theorem chebyshevDistance_comm (a b : Cell) :
    chebyshevDistance a b = chebyshevDistance b a := by
  unfold chebyshevDistance
  omega

/--
Theorem: Manhattan distance satisfies the triangle inequality.
-/
theorem manhattanDistance_triangle (a b c : Cell) :
    manhattanDistance a c ≤ manhattanDistance a b + manhattanDistance b c := by
  unfold manhattanDistance
  omega

/-!
# Supporting Lemmas for LineSegment Cell Intersections
-/

/--
Theorem: Integer minimum with itself is identity.
-/
theorem int_min_self (a : Int) : min a a = a := by
  show (if a ≤ a then a else a) = a
  simp

/--
Theorem: Integer maximum with itself is identity.
-/
theorem int_max_self (a : Int) : max a a = a := by
  show (if a ≤ a then a else a) = a
  simp

/--
Theorem: Integer minimum is bounded above by integer maximum.
-/
theorem int_min_le_max (a b : Int) : min a b ≤ max a b := by
  show (if a ≤ b then a else b) ≤ (if a ≤ b then b else a)
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]; omega

/--
Theorem: When endpoints floor to the same cell, candidateCells contains only that cell.
-/
theorem candidateCells_of_same (A B : Point) (h : floorPoint A = floorPoint B) :
    candidateCells A B = [floorPoint A] := by
  unfold candidateCells
  have hx : (floorPoint A).x = (floorPoint B).x := by rw [h]
  have hy : (floorPoint A).y = (floorPoint B).y := by rw [h]
  dsimp
  rw [← hx, ← hy]
  rw [int_min_self, int_max_self, int_min_self, int_max_self]
  have hxsub : (floorPoint A).x - (floorPoint A).x + 1 = 1 := by omega
  have hysub : (floorPoint A).y - (floorPoint A).y + 1 = 1 := by omega
  rw [hxsub, hysub]
  change [⟨(floorPoint A).x + 0, (floorPoint A).y + 0⟩] = [floorPoint A]
  have : (⟨(floorPoint A).x + 0, (floorPoint A).y + 0⟩ : Cell) = floorPoint A := by
    cases floorPoint A
    dsimp
    congr 1 <;> omega
  rw [this]

/--
Theorem: When endpoints floor to the same cell, cellIntersectionsSegment is the singleton cell.
-/
theorem cellIntersectionsSegment_of_same (A B : Point) (h : floorPoint A = floorPoint B) :
    cellIntersectionsSegment A B = [floorPoint A] := by
  unfold cellIntersectionsSegment
  have hbeq : (floorPoint A == floorPoint B) = true := by
    rw [h]
    exact beq_self_eq_true (floorPoint B)
  simp only [hbeq, ↓reduceIte]

/--
Theorem: Exact characterization of cell intersections when endpoints floor to the same cell.
-/
theorem cellIntersectionsSegment_exact_iff_of_same (A B : Point) (c : Cell)
    (h : floorPoint A = floorPoint B) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  have hseg : cellIntersectionsSegment A B = [floorPoint A] := cellIntersectionsSegment_of_same A B h
  rw [hseg]
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    unfold ActiveIntersectedCell SegmentIntersectsCell IsOffAxisCornerIntersection
    refine ⟨Or.inl rfl, ?_⟩
    intro ⟨h1, _, _⟩
    exact h1 rfl
  · intro h_act
    unfold ActiveIntersectedCell SegmentIntersectsCell IsOffAxisCornerIntersection at h_act
    rcases h_act with ⟨h_seg, _⟩
    rcases h_seg with hcA | hcB | ⟨hc_cand, _⟩
    · exact hcA
    · rw [hcB, ← h]
    · rw [candidateCells_of_same A B h] at hc_cand
      simp only [List.mem_singleton] at hc_cand
      exact hc_cand

/--
Theorem: Characterization of candidate cells membership via bounding box coordinate inequalities.
-/
theorem mem_candidateCells_iff (A B : Point) (c : Cell) :
    let minX := min (floorPoint A).x (floorPoint B).x
    let maxX := max (floorPoint A).x (floorPoint B).x
    let minY := min (floorPoint A).y (floorPoint B).y
    let maxY := max (floorPoint A).y (floorPoint B).y
    c ∈ candidateCells A B ↔ minX ≤ c.x ∧ c.x ≤ maxX ∧ minY ≤ c.y ∧ c.y ≤ maxY := by
  intro minX maxX minY maxY
  unfold candidateCells
  dsimp [minX, maxX, minY, maxY]
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨dx, hdx, hdy_mem⟩
    rw [List.mem_range] at hdx
    rw [List.mem_map] at hdy_mem
    rcases hdy_mem with ⟨dy, hdy, rfl⟩
    rw [List.mem_range] at hdy
    dsimp
    have hxle := int_min_le_max (floorPoint A).x (floorPoint B).x
    have hyle := int_min_le_max (floorPoint A).y (floorPoint B).y
    omega
  · intro ⟨hx1, hx2, hy1, hy2⟩
    have hx_range : (c.x - minX).toNat < (maxX - minX + 1).toNat := by omega
    have hy_range : (c.y - minY).toNat < (maxY - minY + 1).toNat := by omega
    refine ⟨(c.x - minX).toNat, ?_, ?_⟩
    · rw [List.mem_range]; exact hx_range
    · rw [List.mem_map]
      refine ⟨(c.y - minY).toNat, ?_, ?_⟩
      · rw [List.mem_range]; exact hy_range
      · have hx_nonneg : 0 ≤ c.x - minX := by omega
        have hy_nonneg : 0 ≤ c.y - minY := by omega
        have hx : minX + Int.ofNat (c.x - minX).toNat = c.x := by
          have : Int.ofNat (c.x - minX).toNat = ((c.x - minX).toNat : Int) := rfl
          rw [this, Int.toNat_of_nonneg hx_nonneg]
          omega
        have hy : minY + Int.ofNat (c.y - minY).toNat = c.y := by
          have : Int.ofNat (c.y - minY).toNat = ((c.y - minY).toNat : Int) := rfl
          rw [this, Int.toNat_of_nonneg hy_nonneg]
          omega
        exact cell_ext hx hy

/--
Theorem: Both floored endpoints are always members of candidateCells.
-/
theorem endpoints_in_candidateCells (A B : Point) :
    floorPoint A ∈ candidateCells A B ∧ floorPoint B ∈ candidateCells A B := by
  have hA := mem_candidateCells_iff A B (floorPoint A)
  have hB := mem_candidateCells_iff A B (floorPoint B)
  dsimp at hA hB
  constructor
  · rw [hA]
    simp only [min, max]
    by_cases hx : (floorPoint A).x ≤ (floorPoint B).x <;>
    by_cases hy : (floorPoint A).y ≤ (floorPoint B).y <;>
    simp [hx, hy] <;> omega
  · rw [hB]
    simp only [min, max]
    by_cases hx : (floorPoint A).x ≤ (floorPoint B).x <;>
    by_cases hy : (floorPoint A).y ≤ (floorPoint B).y <;>
    simp [hx, hy] <;> omega

/--
Theorem: inBoundingBox is true if and only if the cell is in candidateCells.
-/
theorem inBoundingBox_iff_mem_candidateCells (A B : Point) (c : Cell) :
    inBoundingBox c A B = true ↔ c ∈ candidateCells A B := by
  have h := mem_candidateCells_iff A B c
  unfold inBoundingBox
  dsimp at h ⊢
  rw [h]
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  omega

/--
Theorem: Both floored endpoints are always active intersected cells.
-/
theorem endpoints_activeIntersectedCell (A B : Point) :
    ActiveIntersectedCell (floorPoint A) A B ∧ ActiveIntersectedCell (floorPoint B) A B := by
  unfold ActiveIntersectedCell SegmentIntersectsCell IsOffAxisCornerIntersection
  constructor
  · refine ⟨Or.inl rfl, ?_⟩
    intro ⟨h1, _, _⟩
    exact h1 rfl
  · refine ⟨Or.inr (Or.inl rfl), ?_⟩
    intro ⟨_, h2, _⟩
    exact h2 rfl

/--
Theorem: Cells outside candidateCells are never active intersected cells.
-/
theorem not_active_of_not_mem_candidates (A B : Point) (c : Cell)
    (h : c ∉ candidateCells A B) : ¬ ActiveIntersectedCell c A B := by
  have hend := endpoints_in_candidateCells A B
  intro h_act
  unfold ActiveIntersectedCell SegmentIntersectsCell at h_act
  rcases h_act.1 with rfl | rfl | ⟨hc_cand, _⟩
  · exact h hend.1
  · exact h hend.2
  · exact h hc_cand

/--
Theorem: When endpoints differ, cellIntersectionsSegment membership reduces to endpoints or rayMarch.
-/
theorem mem_cellIntersectionsSegment_of_ne (A B : Point) (c : Cell)
    (hne : floorPoint A ≠ floorPoint B) :
    c ∈ cellIntersectionsSegment A B ↔
      c = floorPoint A ∨ c = floorPoint B ∨
      c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
        A B (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
        (floorPoint B) (floorPoint A) [] := by
  have hbeq : (floorPoint A == floorPoint B) = false := by
    cases h : (floorPoint A == floorPoint B)
    · rfl
    · exfalso
      apply hne
      exact eq_of_beq h
  unfold cellIntersectionsSegment
  dsimp
  rw [hbeq]
  simp

/--
Theorem: Both floored endpoints are always in cellIntersectionsSegment.
-/
theorem endpoints_in_cellIntersectionsSegment (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B ∧ floorPoint B ∈ cellIntersectionsSegment A B := by
  by_cases h : floorPoint A = floorPoint B
  · rw [cellIntersectionsSegment_of_same A B h]
    constructor
    · simp
    · rw [← h]; simp
  · rw [mem_cellIntersectionsSegment_of_ne A B _ h, mem_cellIntersectionsSegment_of_ne A B _ h]
    constructor
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

/--
Theorem: Accumulator append property for rayMarch.
-/
theorem rayMarch_acc (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) :
    rayMarch fuel start ptEnd dx dy stepX stepY endCell current acc =
      acc ++ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  induction fuel generalizing current acc with
  | zero =>
    unfold rayMarch
    simp
  | succ fuel ih =>
    unfold rayMarch
    dsimp
    cases hc : (current == endCell)
    · dsimp
      cases hd : (rayMarchStep start ptEnd dx dy stepX stepY current).snd
      · dsimp
        rw [ih _ (acc ++ [(rayMarchStep start ptEnd dx dy stepX stepY current).fst])]
        rw [ih _ [(rayMarchStep start ptEnd dx dy stepX stepY current).fst]]
        simp [List.append_assoc]
      · simp
    · simp

/--
Theorem: Membership in rayMarch with accumulator splits into accumulator or empty accumulator.
-/
theorem mem_rayMarch (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) (c : Cell) :
    c ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current acc ↔
      c ∈ acc ∨ c ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  rw [rayMarch_acc]
  simp

/--
Theorem: Unfolding step equation for rayMarch with empty accumulator.
-/
theorem rayMarch_succ (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current [] =
      if current == endCell then []
      else
        let (nextCell, done) := rayMarchStep start ptEnd dx dy stepX stepY current
        if done then []
        else nextCell :: rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell [] := by
  conv =>
    lhs
    rw [rayMarch]
  dsimp
  cases hc : (current == endCell)
  · dsimp
    cases hd : (rayMarchStep start ptEnd dx dy stepX stepY current).snd
    · dsimp
      rw [rayMarch_acc]
      rfl
    · rfl
  · rfl

/--
Theorem: Base case for rayMarch with zero fuel.
-/
theorem rayMarch_zero (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) :
    rayMarch 0 start ptEnd dx dy stepX stepY endCell current acc = acc := by
  rfl

/--
Theorem: When current reaches endCell, rayMarch terminates and returns acc.
-/
theorem rayMarch_at_end (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) (h : (current == endCell) = true) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current acc = acc := by
  conv =>
    lhs
    rw [rayMarch]
  dsimp
  rw [h]
  simp

/--
Theorem: When rayMarchStep indicates done, rayMarch terminates and returns acc.
-/
theorem rayMarch_step_done (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell)
    (h_not_end : (current == endCell) = false)
    (h_done : (rayMarchStep start ptEnd dx dy stepX stepY current).snd = true) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current acc = acc := by
  conv =>
    lhs
    rw [rayMarch]
  dsimp
  rw [h_not_end]
  dsimp
  cases hd : (rayMarchStep start ptEnd dx dy stepX stepY current).snd
  · rw [hd] at h_done
    contradiction
  · simp

/--
Theorem: When rayMarchStep produces nextCell without terminating, rayMarch recurses on nextCell.
-/
theorem rayMarch_step_continue (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell)
    (h_not_end : (current == endCell) = false)
    (h_not_done : (rayMarchStep start ptEnd dx dy stepX stepY current).snd = false) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current acc =
      rayMarch fuel start ptEnd dx dy stepX stepY endCell
        (rayMarchStep start ptEnd dx dy stepX stepY current).fst (acc ++ [(rayMarchStep start ptEnd dx dy stepX stepY current).fst]) := by
  conv =>
    lhs
    rw [rayMarch]
  dsimp
  rw [h_not_end]
  dsimp
  cases hd : (rayMarchStep start ptEnd dx dy stepX stepY current).snd
  · simp
  · rw [hd] at h_not_done
    contradiction

/--
Theorem: If an invariant on cells is preserved by each non-terminating rayMarchStep,
then every cell output by rayMarch satisfies the invariant.
-/
theorem rayMarch_induction_sound (fuel : Nat) (A B : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell current : Cell) (P : Cell → Prop)
    (h_step : ∀ c, P c →
      (rayMarchStep A B dx dy stepX stepY c).2 = false →
      P (rayMarchStep A B dx dy stepX stepY c).1)
    (h_curr : P current) :
    ∀ x ∈ rayMarch fuel A B dx dy stepX stepY endCell current [], P x := by
  induction fuel generalizing current with
  | zero =>
    intro x hx
    unfold rayMarch at hx
    contradiction
  | succ fuel ih =>
    intro x hx
    rw [rayMarch_succ] at hx
    dsimp only [] at hx
    split_ifs at hx with h_end h_done
    · contradiction
    · contradiction
    · have h_done_false : (rayMarchStep A B dx dy stepX stepY current).2 = false := by
        revert h_done
        cases (rayMarchStep A B dx dy stepX stepY current).2 <;> simp
      rw [rayMarch_acc] at hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | h_tail
      · exact h_step current h_curr h_done_false
      · simp only [List.nil_append] at h_tail
        have h_next_prop := h_step current h_curr h_done_false
        exact ih (rayMarchStep A B dx dy stepX stepY current).1 h_next_prop x h_tail

/--
Theorem: Soundness from first step: if the first step produces a valid cell and all subsequent
steps preserve validity, then every cell output by rayMarch satisfies the property.
-/
theorem sound_from_first_step (fuel : Nat) (A B : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell : Cell) (P : Cell → Prop)
    (h_step : ∀ c, P c →
      (rayMarchStep A B dx dy stepX stepY c).2 = false →
      P (rayMarchStep A B dx dy stepX stepY c).1)
    (h_first : (rayMarchStep A B dx dy stepX stepY (floorPoint A)).2 = false →
      P (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1) :
    ∀ x ∈ rayMarch (fuel + 1) A B dx dy stepX stepY endCell (floorPoint A) [], P x := by
  intro x hx
  rw [rayMarch_succ] at hx
  dsimp only [] at hx
  split_ifs at hx with h_end h_done
  · contradiction
  · contradiction
  · have h_done_false : (rayMarchStep A B dx dy stepX stepY (floorPoint A)).2 = false := by
      revert h_done
      cases (rayMarchStep A B dx dy stepX stepY (floorPoint A)).2 <;> simp
    have h_first_prop := h_first h_done_false
    rw [List.mem_cons] at hx
    rcases hx with rfl | h_tail
    · exact h_first_prop
    · exact rayMarch_induction_sound fuel A B dx dy stepX stepY endCell
        (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1
        P h_step h_first_prop x h_tail

/--
Theorem: The start cell floorPoint A is in the bounding box.
-/
theorem inBoundingBox_startCell (A B : Point) :
    inBoundingBox (floorPoint A) A B = true := by
  rw [inBoundingBox_iff_mem_candidateCells]
  exact (endpoints_in_candidateCells A B).1

/--
Theorem: The end cell floorPoint B is in the bounding box.
-/
theorem inBoundingBox_endCell (A B : Point) :
    inBoundingBox (floorPoint B) A B = true := by
  rw [inBoundingBox_iff_mem_candidateCells]
  exact (endpoints_in_candidateCells A B).2

/--
Theorem: When endpoints floor to the same cell, rayMarchIntermediateCells is empty.
-/
theorem rayMarchIntermediateCells_of_same (A B : Point) (h : floorPoint A = floorPoint B) :
    rayMarchIntermediateCells A B = [] := by
  unfold rayMarchIntermediateCells
  have hstart_end : (floorPoint A == floorPoint B) = true := by
    rw [h]
    exact beq_self_eq_true (floorPoint B)
  have hx : (floorPoint B).x - (floorPoint A).x = 0 := by rw [h]; omega
  have hy : (floorPoint B).y - (floorPoint A).y = 0 := by rw [h]; omega
  have hstep : (0 : Int).natAbs + (0 : Int).natAbs + 2 = 2 := rfl
  dsimp
  rw [hx, hy, hstep]
  change List.filter _ (rayMarch (1 + 1) _ _ _ _ _ _ (floorPoint B) (floorPoint A) []) = []
  conv =>
    lhs
    arg 2
    rw [rayMarch]
  dsimp
  rw [hstart_end]
  rfl

/--
Theorem: When endpoints floor to the same cell, intermediateCells is empty.
-/
theorem intermediateCells_of_same (A B : Point) (h : floorPoint A = floorPoint B) :
    intermediateCells A B = [] := by
  unfold intermediateCells
  rw [candidateCells_of_same A B h]
  dsimp
  simp

/--
Theorem: When endpoints floor to the same cell, rayMarchIntermediateCells equals intermediateCells.
-/
theorem rayMarchIntermediateCells_eq_intermediateCells_of_same (A B : Point)
    (h : floorPoint A = floorPoint B) :
    rayMarchIntermediateCells A B = intermediateCells A B := by
  rw [rayMarchIntermediateCells_of_same A B h]
  rw [intermediateCells_of_same A B h]

/--
Theorem: Floored endpoints are never members of intermediateCells.
-/
theorem not_mem_intermediateCells_endpoints (A B : Point) :
    floorPoint A ∉ intermediateCells A B ∧ floorPoint B ∉ intermediateCells A B := by
  unfold intermediateCells
  rw [List.mem_filter, List.mem_filter]
  constructor
  · rintro ⟨_, h_pred⟩
    simp at h_pred
  · rintro ⟨_, h_pred⟩
    simp at h_pred

/--
Theorem: Floored endpoints are never members of rayMarchIntermediateCells.
-/
theorem not_mem_rayMarchIntermediateCells_endpoints (A B : Point) :
    floorPoint A ∉ rayMarchIntermediateCells A B ∧ floorPoint B ∉ rayMarchIntermediateCells A B := by
  unfold rayMarchIntermediateCells
  rw [List.mem_filter, List.mem_filter]
  constructor
  · rintro ⟨_, h_pred⟩
    simp at h_pred
  · rintro ⟨_, h_pred⟩
    simp at h_pred

/--
Theorem: ActiveIntersectedCell is equivalent to endpoints or membership in intermediateCells.
-/
theorem activeIntersectedCell_iff_endpoints_or_intermediate (A B : Point) (c : Cell) :
    ActiveIntersectedCell c A B ↔ c = floorPoint A ∨ c = floorPoint B ∨ c ∈ intermediateCells A B := by
  unfold ActiveIntersectedCell SegmentIntersectsCell IsOffAxisCornerIntersection intermediateCells
  rw [List.mem_filter]
  dsimp
  constructor
  · rintro ⟨(hA | hB | ⟨hc_cand, h_seg⟩), h_not_off⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
    · by_cases hcA : c = floorPoint A
      · exact Or.inl hcA
      · by_cases hcB : c = floorPoint B
        · exact Or.inr (Or.inl hcB)
        · right; right
          have hneA : (c != floorPoint A) = true := by rw [bne_iff_ne]; exact hcA
          have hneB : (c != floorPoint B) = true := by rw [bne_iff_ne]; exact hcB
          have h_off : isOffAxisCornerBool c A B = false := by
            cases h : isOffAxisCornerBool c A B
            · rfl
            · exfalso
              apply h_not_off
              exact ⟨hcA, hcB, h⟩
          refine ⟨hc_cand, ?_⟩
          simp [hneA, hneB, h_seg, h_off]
  · rintro (hA | hB | ⟨hc_cand, h_pred⟩)
    · subst hA
      refine ⟨Or.inl rfl, ?_⟩
      intro ⟨h1, _, _⟩
      exact h1 rfl
    · subst hB
      refine ⟨Or.inr (Or.inl rfl), ?_⟩
      intro ⟨_, h2, _⟩
      exact h2 rfl
    · have h_seg : segmentIntersectsCellBool c A B = true := by
        revert h_pred
        cases c != floorPoint A <;> cases c != floorPoint B <;> cases segmentIntersectsCellBool c A B <;> simp
      have h_not_off_bool : (!isOffAxisCornerBool c A B) = true := by
        revert h_pred
        cases c != floorPoint A <;> cases c != floorPoint B <;> cases segmentIntersectsCellBool c A B <;> cases isOffAxisCornerBool c A B <;> simp
      have h_off : isOffAxisCornerBool c A B = false := by
        revert h_not_off_bool
        cases isOffAxisCornerBool c A B <;> simp
      refine ⟨Or.inr (Or.inr ⟨hc_cand, h_seg⟩), ?_⟩
      intro ⟨_, _, h_off_true⟩
      rw [h_off] at h_off_true
      contradiction

/-!
# RayMarch Boundary Crossing Lemmas
-/

/--
Theorem: Cross product strict inequality is equivalent to division inequality for positive terms.
-/
theorem cross_lt_cross_iff_div_lt_div (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy) :
    remX * absDy < remY * absDx ↔ remX / absDx < remY / absDy :=
  (div_lt_div_iff₀ hdx hdy).symm

/--
Theorem: Cross product non-strict inequality is equivalent to division inequality for positive terms.
-/
theorem cross_le_cross_iff_div_le_div (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy) :
    remX * absDy ≤ remY * absDx ↔ remX / absDx ≤ remY / absDy :=
  (div_le_div_iff₀ hdx hdy).symm

/--
Theorem: Cross product equality is equivalent to division equality for positive terms.
-/
theorem cross_eq_cross_iff_div_eq_div (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy) :
    remX * absDy = remY * absDx ↔ remX / absDx = remY / absDy := by
  constructor
  · intro h
    have h1 : remX * absDy ≤ remY * absDx := by linarith
    have h2 : remY * absDx ≤ remX * absDy := by linarith
    rw [cross_le_cross_iff_div_le_div remX remY absDx absDy hdx hdy] at h1
    rw [cross_le_cross_iff_div_le_div remY remX absDy absDx hdy hdx] at h2
    exact le_antisymm h1 h2
  · intro h
    have h1 : remX / absDx ≤ remY / absDy := by linarith
    have h2 : remY / absDy ≤ remX / absDx := by linarith
    rw [← cross_le_cross_iff_div_le_div remX remY absDx absDy hdx hdy] at h1
    rw [← cross_le_cross_iff_div_le_div remY remX absDy absDx hdy hdx] at h2
    exact le_antisymm h1 h2

/--
Theorem: `min crossX crossY ≥ limitCross` is equivalent to
`remX ≥ absDx ∧ remY ≥ absDy` (i.e. both exit times are ≥ 1).
-/
theorem min_cross_ge_limit_iff (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy) :
    min (remX * absDy) (remY * absDx) ≥ absDx * absDy ↔
      remX ≥ absDx ∧ remY ≥ absDy := by
  rw [ge_iff_le, le_min_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith

/--
Theorem: The negation `min crossX crossY < limitCross` means at least one
boundary is crossed before t = 1.
-/
theorem min_cross_lt_limit_iff (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy) :
    min (remX * absDy) (remY * absDx) < absDx * absDy ↔
      remX < absDx ∨ remY < absDy := by
  rw [min_lt_iff]
  constructor
  · rintro (h1 | h2)
    · left; nlinarith
    · right; nlinarith
  · rintro (h1 | h2)
    · left; nlinarith
    · right; nlinarith

/--
Theorem: When rayMarchStep takes an X step, remX < absDx.
-/
theorem stepX_bounded (remX absDx absDy crossY : Rat)
    (hdy : 0 < absDy)
    (h_step : remX * absDy < crossY)
    (h_not_done : min (remX * absDy) crossY < absDx * absDy) :
    remX < absDx := by
  have h_min : min (remX * absDy) crossY = remX * absDy := min_eq_left (le_of_lt h_step)
  rw [h_min] at h_not_done
  exact (mul_lt_mul_iff_of_pos_right hdy).mp h_not_done

/--
Theorem: When rayMarchStep takes a Y step, remY < absDy.
-/
theorem stepY_bounded (remY absDx absDy crossX : Rat)
    (hdx : 0 < absDx)
    (h_step : remY * absDx < crossX)
    (h_not_done : min crossX (remY * absDx) < absDx * absDy) :
    remY < absDy := by
  have h_min : min crossX (remY * absDx) = remY * absDx := min_eq_right (le_of_lt h_step)
  rw [h_min] at h_not_done
  rw [mul_comm absDx absDy] at h_not_done
  exact (mul_lt_mul_iff_of_pos_right hdx).mp h_not_done

/--
Theorem: When rayMarchStep takes a diagonal step, remX < absDx and remY < absDy.
-/
theorem stepDiag_bounded (remX remY absDx absDy : Rat)
    (hdx : 0 < absDx) (hdy : 0 < absDy)
    (h_eq : remX * absDy = remY * absDx)
    (h_not_done : min (remX * absDy) (remY * absDx) < absDx * absDy) :
    remX < absDx ∧ remY < absDy := by
  rw [h_eq, min_self] at h_not_done
  have h_not_done_y := h_not_done
  rw [mul_comm absDx absDy] at h_not_done_y
  have hY : remY < absDy := (mul_lt_mul_iff_of_pos_right hdx).mp h_not_done_y
  have h_not_done' : remX * absDy < absDx * absDy := by linarith
  have hX : remX < absDx := (mul_lt_mul_iff_of_pos_right hdy).mp h_not_done'
  exact ⟨hX, hY⟩

/--
Theorem: If an integer cast is strictly less than a rational, it is ≤ floor of the rational.
-/
theorem int_le_floor_of_lt (n : Int) (x : Rat) (h : (n : Rat) < x) :
    n ≤ (Rat.floor x) := by
  have := Rat.floor_le x
  by_contra! h_lt
  have : Rat.floor x + 1 ≤ n := h_lt
  have h_le : ((Rat.floor x + 1 : Int) : Rat) ≤ (n : Rat) := Int.cast_le.mpr this
  have h_lt' : x < ((Rat.floor x + 1 : Int) : Rat) := Rat.lt_floor_add_one x
  linarith

/--
Theorem: If a rational is strictly less than an integer cast, its floor is strictly less.
-/
theorem floor_lt_of_lt (n : Int) (x : Rat) (h : x < (n : Rat)) :
    Rat.floor x < n := by
  have := Rat.floor_le x
  have : ((Rat.floor x : Int) : Rat) < (n : Rat) := by linarith
  exact Int.cast_lt.mp this

/--
Theorem: Directional bounding for X step forward (dx > 0).
-/
theorem stepX_next_le_end (cx : Int) (Ax Bx : Rat)
    (h_rem : ((cx + 1 : Int) : Rat) - Ax < Bx - Ax) :
    cx + 1 ≤ (floorPoint ⟨Bx, 0⟩).x := by
  have h_lt : ((cx + 1 : Int) : Rat) < Bx := by linarith
  unfold floorPoint toInt
  dsimp
  exact int_le_floor_of_lt (cx + 1) Bx h_lt

/--
Theorem: Directional bounding for X step backward (dx < 0).
-/
theorem stepX_next_ge_end (cx : Int) (Ax Bx : Rat)
    (h_rem : Ax - ((cx : Int) : Rat) < Ax - Bx) :
    (floorPoint ⟨Bx, 0⟩).x ≤ cx - 1 := by
  have h_lt : Bx < ((cx : Int) : Rat) := by linarith
  have h_floor_lt := floor_lt_of_lt cx Bx h_lt
  unfold floorPoint toInt
  dsimp
  exact Int.le_sub_one_of_lt h_floor_lt

/--
Theorem: Directional bounding for Y step forward (dy > 0).
-/
theorem stepY_next_le_end (cy : Int) (Ay By : Rat)
    (h_rem : ((cy + 1 : Int) : Rat) - Ay < By - Ay) :
    cy + 1 ≤ (floorPoint ⟨0, By⟩).y := by
  have h_lt : ((cy + 1 : Int) : Rat) < By := by linarith
  unfold floorPoint toInt
  dsimp
  exact int_le_floor_of_lt (cy + 1) By h_lt

/--
Theorem: Directional bounding for Y step backward (dy < 0).
-/
theorem stepY_next_ge_end (cy : Int) (Ay By : Rat)
    (h_rem : Ay - ((cy : Int) : Rat) < Ay - By) :
    (floorPoint ⟨0, By⟩).y ≤ cy - 1 := by
  have h_lt : By < ((cy : Int) : Rat) := by linarith
  have h_floor_lt := floor_lt_of_lt cy By h_lt
  unfold floorPoint toInt
  dsimp
  exact Int.le_sub_one_of_lt h_floor_lt

/--
Theorem: Positive interval length for X step transition.
-/
theorem stepX_interval_lt (tx1 ty0 ty1 dx : Rat) (dx_pos : 0 < dx)
    (h_cross : tx1 < ty1)
    (h_lim : tx1 < 1)
    (h_pos : 0 ≤ tx1)
    (h_ty0 : ty0 ≤ tx1) :
    max 0 (max tx1 ty0) < min 1 (min (tx1 + 1 / dx) ty1) := by
  have h_enter : max 0 (max tx1 ty0) = tx1 := by
    rw [max_eq_left h_ty0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : tx1 < 1 := h_lim
  have h2 : tx1 < tx1 + 1 / dx := by
    have : 0 < 1 / dx := one_div_pos.mpr dx_pos
    linarith
  have h3 : tx1 < ty1 := h_cross
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩

/--
Theorem: Positive interval length for Y step transition.
-/
theorem stepY_interval_lt (ty1 tx0 tx1 dy : Rat) (dy_pos : 0 < dy)
    (h_cross : ty1 < tx1)
    (h_lim : ty1 < 1)
    (h_pos : 0 ≤ ty1)
    (h_tx0 : tx0 ≤ ty1) :
    max 0 (max tx0 ty1) < min 1 (min tx1 (ty1 + 1 / dy)) := by
  have h_enter : max 0 (max tx0 ty1) = ty1 := by
    rw [max_eq_right h_tx0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : ty1 < 1 := h_lim
  have h2 : ty1 < tx1 := h_cross
  have h3 : ty1 < ty1 + 1 / dy := by
    have : 0 < 1 / dy := one_div_pos.mpr dy_pos
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩

/--
Theorem: Positive interval length for diagonal step transition.
-/
theorem stepDiag_interval_lt (t dx dy : Rat) (dx_pos : 0 < dx) (dy_pos : 0 < dy)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t + 1 / dx) (t + 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t + 1 / dx := by
    have : 0 < 1 / dx := one_div_pos.mpr dx_pos
    linarith
  have h3 : t < t + 1 / dy := by
    have : 0 < 1 / dy := one_div_pos.mpr dy_pos
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩

/--
Theorem: When tEnter < tExit for cell c, segmentIntersectsCellBool is true
and isOffAxisCornerBool is false.
-/
theorem cell_active_of_interval_lt (c : Cell) (A B : Point)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B)
    (h_bbox : inBoundingBox c A B = true)
    (tEnter tExit : Rat)
    (h_interval : cellIntersectionInterval c A B = some (tEnter, tExit))
    (h_lt : tEnter < tExit) :
    segmentIntersectsCellBool c A B = true ∧ isOffAxisCornerBool c A B = false := by
  have hneA : (c == floorPoint A) = false := by
    cases h : (c == floorPoint A)
    · rfl
    · exfalso; exact hcA (eq_of_beq h)
  have hneB : (c == floorPoint B) = false := by
    cases h : (c == floorPoint B)
    · rfl
    · exfalso; exact hcB (eq_of_beq h)
  constructor
  · unfold segmentIntersectsCellBool
    simp [hneA, hneB, h_bbox, h_interval]
  · unfold isOffAxisCornerBool
    simp [hneA, hneB, h_bbox, h_interval]
    intro h_eq
    linarith

/--
Theorem: When cellIntersectionInterval has tEnter < tExit, isOffAxisCornerBool is false.
-/
theorem not_off_axis_of_interval_lt (c : Cell) (A B : Point)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B)
    (h_bbox : inBoundingBox c A B = true)
    (tEnter tExit : Rat)
    (h_int : cellIntersectionInterval c A B = some (tEnter, tExit))
    (h_lt : tEnter < tExit) :
    isOffAxisCornerBool c A B = false :=
  (cell_active_of_interval_lt c A B hcA hcB h_bbox tEnter tExit h_int h_lt).2

/--
Theorem: If cellIntersectionInterval returns some (tEnter, tExit), then tEnter ≤ tExit.
-/
theorem cellIntersectionInterval_le (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit)) :
    tEnter ≤ tExit := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       assumption)

/--
Theorem: Non-endpoint cell membership in intermediateCells is equivalent to being in
the bounding box with a strictly positive intersection interval (tEnter < tExit).
-/
theorem intermediateCells_iff_interval (A B : Point) (c : Cell)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B) :
    c ∈ intermediateCells A B ↔
      inBoundingBox c A B = true ∧
      ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  unfold intermediateCells
  rw [List.mem_filter]
  rw [← inBoundingBox_iff_mem_candidateCells]
  have hneA : (c != floorPoint A) = true := by
    rw [bne_iff_ne]; exact hcA
  have hneB : (c != floorPoint B) = true := by
    rw [bne_iff_ne]; exact hcB
  constructor
  · rintro ⟨h_bbox, h_pred⟩
    simp [hneA, hneB] at h_pred
    rcases h_pred with ⟨h_seg, h_not_off⟩
    unfold segmentIntersectsCellBool at h_seg
    have h_eqA : (c == floorPoint A) = false := by
      cases h : (c == floorPoint A)
      · rfl
      · exfalso; exact hcA (eq_of_beq h)
    have h_eqB : (c == floorPoint B) = false := by
      cases h : (c == floorPoint B)
      · rfl
      · exfalso; exact hcB (eq_of_beq h)
    simp [h_eqA, h_eqB, h_bbox] at h_seg
    unfold isOffAxisCornerBool at h_not_off
    simp [h_eqA, h_eqB, h_bbox] at h_not_off
    cases h_int : cellIntersectionInterval c A B with
    | none =>
      rw [h_int] at h_seg
      contradiction
    | some pair =>
      cases pair with
      | mk tEnter tExit =>
        rw [h_int] at h_seg h_not_off
        dsimp at h_seg h_not_off
        refine ⟨h_bbox, tEnter, tExit, rfl, ?_⟩
        have h_le := cellIntersectionInterval_le c A B tEnter tExit h_int
        cases h_eq : (tEnter == tExit)
        · have h_ne : tEnter ≠ tExit := by
            intro h
            subst h
            simp at h_eq
          exact lt_of_le_of_ne h_le h_ne
        · simp [h_eq] at h_not_off
  · rintro ⟨h_bbox, tEnter, tExit, h_int, h_lt⟩
    refine ⟨h_bbox, ?_⟩
    have h_act := cell_active_of_interval_lt c A B hcA hcB h_bbox tEnter tExit h_int h_lt
    simp [hneA, hneB, h_act.1, h_act.2]

/--
Theorem: Membership in rayMarchIntermediateCells for non-endpoints reduces to
rayMarch membership and not being an off-axis corner.
-/
theorem mem_rayMarchIntermediateCells (A B : Point) (c : Cell)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B) :
    c ∈ rayMarchIntermediateCells A B ↔
      c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
        A B (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
        (floorPoint B) (floorPoint A) [] ∧
      isOffAxisCornerBool c A B = false := by
  unfold rayMarchIntermediateCells
  rw [List.mem_filter]
  have hneA : (c != floorPoint A) = true := by
    rw [bne_iff_ne]; exact hcA
  have hneB : (c != floorPoint B) = true := by
    rw [bne_iff_ne]; exact hcB
  cases isOffAxisCornerBool c A B <;> simp [hneA, hneB]

/--
Theorem: Equivalence between rayMarch and intermediateCells for non-endpoints follows from
rayMarchIntermediateCells = intermediateCells and the fact that rayMarch contains no off-axis corners.
-/
theorem rayMarch_iff_intermediate_of_eq (A B : Point) (c : Cell)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B)
    (h_eq : rayMarchIntermediateCells A B = intermediateCells A B)
    (h_not_off : c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] → isOffAxisCornerBool c A B = false) :
    (c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] ↔ c ∈ intermediateCells A B) := by
  constructor
  · intro hray
    have h_off := h_not_off hray
    have h_mem : c ∈ rayMarchIntermediateCells A B := by
      rw [mem_rayMarchIntermediateCells A B c hcA hcB]
      exact ⟨hray, h_off⟩
    rw [h_eq] at h_mem
    exact h_mem
  · intro hinter
    have h_mem : c ∈ rayMarchIntermediateCells A B := by
      rw [h_eq]
      exact hinter
    rw [mem_rayMarchIntermediateCells A B c hcA hcB] at h_mem
    exact h_mem.1

/--
Theorem: Equivalence between rayMarch and intermediateCells for non-endpoints follows from
set membership equivalence between rayMarchIntermediateCells and intermediateCells.
-/
theorem rayMarch_iff_intermediate_of_mem_eq (A B : Point) (c : Cell)
    (hcA : c ≠ floorPoint A) (hcB : c ≠ floorPoint B)
    (h_mem_eq : ∀ x, x ≠ floorPoint A → x ≠ floorPoint B →
      (x ∈ rayMarchIntermediateCells A B ↔ x ∈ intermediateCells A B))
    (h_not_off : c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] → isOffAxisCornerBool c A B = false) :
    (c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] ↔ c ∈ intermediateCells A B) := by
  constructor
  · intro hray
    have h_off := h_not_off hray
    have h_mem : c ∈ rayMarchIntermediateCells A B := by
      rw [mem_rayMarchIntermediateCells A B c hcA hcB]
      exact ⟨hray, h_off⟩
    rw [h_mem_eq c hcA hcB] at h_mem
    exact h_mem
  · intro hinter
    have h_mem : c ∈ rayMarchIntermediateCells A B := by
      rw [h_mem_eq c hcA hcB]
      exact hinter
    rw [mem_rayMarchIntermediateCells A B c hcA hcB] at h_mem
    exact h_mem.1

/--
Theorem: Equivalence between rayMarchIntermediateCells and intermediateCells for non-endpoints
reduces to interval soundness and completeness.
-/
theorem rayMarchIntermediateCells_iff_intermediateCells (A B : Point) (x : Cell)
    (hxA : x ≠ floorPoint A) (hxB : x ≠ floorPoint B)
    (h_sound : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] →
      inBoundingBox x A B = true ∧
      ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_complete : inBoundingBox x A B = true →
      (∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit) →
      x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
        A B (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
        (floorPoint B) (floorPoint A) [] ) :
    (x ∈ rayMarchIntermediateCells A B ↔ x ∈ intermediateCells A B) := by
  rw [mem_rayMarchIntermediateCells A B x hxA hxB]
  rw [intermediateCells_iff_interval A B x hxA hxB]
  constructor
  · rintro ⟨hray, _⟩
    exact h_sound hray
  · rintro ⟨h_bbox, tEnter, tExit, h_int, h_lt⟩
    have hray := h_complete h_bbox ⟨tEnter, tExit, h_int, h_lt⟩
    have h_not_off := not_off_axis_of_interval_lt x A B hxA hxB h_bbox tEnter tExit h_int h_lt
    exact ⟨hray, h_not_off⟩

/-!
# Master Characterization Theorems
-/

/--
Theorem: Equivalence between cellIntersectionsSegment and ActiveIntersectedCell
reduces to equivalence between rayMarch and intermediateCells for non-endpoints.
-/
theorem cellIntersectionsSegment_exact_iff_reduction (A B : Point) (c : Cell)
    (h_ray_inter : floorPoint A ≠ floorPoint B → c ≠ floorPoint A → c ≠ floorPoint B →
      (c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
        A B (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
        (floorPoint B) (floorPoint A) [] ↔ c ∈ intermediateCells A B)) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  by_cases h : floorPoint A = floorPoint B
  · exact cellIntersectionsSegment_exact_iff_of_same A B c h
  · rw [mem_cellIntersectionsSegment_of_ne A B c h]
    rw [activeIntersectedCell_iff_endpoints_or_intermediate A B c]
    by_cases hcA : c = floorPoint A
    · subst hcA
      simp
    · by_cases hcB : c = floorPoint B
      · subst hcB
        simp
      · simp only [hcA, hcB, false_or]
        exact h_ray_inter h hcA hcB



/-!
# Part 1: Floor monotonicity and interval bounds
-/

theorem le_floor_of_le (n : Int) (x : Rat) (h : (n : Rat) ≤ x) :
    n ≤ Rat.floor x := by
  by_contra! h_lt
  have : Rat.floor x + 1 ≤ n := h_lt
  have h_le : ((Rat.floor x + 1 : Int) : Rat) ≤ (n : Rat) := Int.cast_le.mpr this
  have h_lt' : x < ((Rat.floor x + 1 : Int) : Rat) := Rat.lt_floor_add_one x
  linarith

theorem rat_floor_mono {a b : Rat} (h : a ≤ b) : Rat.floor a ≤ Rat.floor b := by
  have := Rat.floor_le a
  exact le_floor_of_le (Rat.floor a) b (by linarith)

theorem interval_enter_exit_le_one (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit)) :
    0 ≤ tEnter ∧ tExit ≤ 1 := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       refine ⟨le_max_left 0 _, min_le_left 1 _⟩)

theorem interval_dx_pos (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdx : 0 < B.x - A.x) :
    (ofInt c.x - A.x) / (B.x - A.x) ≤ tEnter ∧
    tExit ≤ (ofInt (c.x + 1) - A.x) / (B.x - A.x) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.x - A.x) == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      linarith
  simp only [h_ne] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       refine ⟨?_, ?_⟩
       · exact le_trans (le_max_left _ _) (le_max_right 0 _)
       · exact le_trans (min_le_right 1 _) (min_le_left _ _))

theorem interval_dx_neg (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdx : B.x - A.x < 0) :
    (ofInt (c.x + 1) - A.x) / (B.x - A.x) ≤ tEnter ∧
    tExit ≤ (ofInt c.x - A.x) / (B.x - A.x) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.x - A.x) == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      linarith
  have h_not_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_ne] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       refine ⟨?_, ?_⟩
       · exact le_trans (le_max_left _ _) (le_max_right 0 _)
       · exact le_trans (min_le_right 1 _) (min_le_left _ _))

theorem interval_dy_pos (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdy : 0 < B.y - A.y) :
    (ofInt c.y - A.y) / (B.y - A.y) ≤ tEnter ∧
    tExit ≤ (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.y - A.y) == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      linarith
  simp only [h_ne] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       refine ⟨?_, ?_⟩
       · exact le_trans (le_max_right _ _) (le_max_right 0 _)
       · exact le_trans (min_le_right 1 _) (min_le_right _ _))

theorem interval_dy_neg (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdy : B.y - A.y < 0) :
    (ofInt (c.y + 1) - A.y) / (B.y - A.y) ≤ tEnter ∧
    tExit ≤ (ofInt c.y - A.y) / (B.y - A.y) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.y - A.y) == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      linarith
  have h_not_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_ne] at h
  split_ifs at h
  all_goals
    first
    | contradiction
    | (injection h with h_eq
       injection h_eq with h1 h2
       subst h1 h2
       refine ⟨?_, ?_⟩
       · exact le_trans (le_max_right _ _) (le_max_right 0 _)
       · exact le_trans (min_le_right 1 _) (min_le_right _ _))

/-!
# Part 2: Bounding box signs
-/

theorem bbox_signs (x : Cell) (A B : Point) (h_bbox : inBoundingBox x A B = true) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    0 ≤ (x.x - (floorPoint A).x) * sx ∧
    0 ≤ ((floorPoint B).x - x.x) * sx ∧
    0 ≤ (x.y - (floorPoint A).y) * sy ∧
    0 ≤ ((floorPoint B).y - x.y) * sy := by
  unfold inBoundingBox at h_bbox
  dsimp only [] at h_bbox
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox
  rcases h_bbox with ⟨⟨⟨h_minX, h_maxX⟩, h_minY⟩, h_maxY⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_ifs with h1 h2
    · have : (floorPoint A).x ≤ (floorPoint B).x := by
        unfold floorPoint toInt
        dsimp
        have : A.x ≤ B.x := by linarith
        exact rat_floor_mono this
      have : min (floorPoint A).x (floorPoint B).x = (floorPoint A).x := min_eq_left this
      linarith
    · have : (floorPoint B).x ≤ (floorPoint A).x := by
        unfold floorPoint toInt
        dsimp
        have : B.x ≤ A.x := by linarith
        exact rat_floor_mono this
      have : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left this
      linarith
    · linarith
  · split_ifs with h1 h2
    · have : (floorPoint A).x ≤ (floorPoint B).x := by
        unfold floorPoint toInt
        dsimp
        have : A.x ≤ B.x := by linarith
        exact rat_floor_mono this
      have : max (floorPoint A).x (floorPoint B).x = (floorPoint B).x := max_eq_right this
      linarith
    · have : (floorPoint B).x ≤ (floorPoint A).x := by
        unfold floorPoint toInt
        dsimp
        have : B.x ≤ A.x := by linarith
        exact rat_floor_mono this
      have : min (floorPoint A).x (floorPoint B).x = (floorPoint B).x := min_eq_right this
      linarith
    · linarith
  · split_ifs with h1 h2
    · have : (floorPoint A).y ≤ (floorPoint B).y := by
        unfold floorPoint toInt
        dsimp
        have : A.y ≤ B.y := by linarith
        exact rat_floor_mono this
      have : min (floorPoint A).y (floorPoint B).y = (floorPoint A).y := min_eq_left this
      linarith
    · have : (floorPoint B).y ≤ (floorPoint A).y := by
        unfold floorPoint toInt
        dsimp
        have : B.y ≤ A.y := by linarith
        exact rat_floor_mono this
      have : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left this
      linarith
    · linarith
  · split_ifs with h1 h2
    · have : (floorPoint A).y ≤ (floorPoint B).y := by
        unfold floorPoint toInt
        dsimp
        have : A.y ≤ B.y := by linarith
        exact rat_floor_mono this
      have : max (floorPoint A).y (floorPoint B).y = (floorPoint B).y := max_eq_right this
      linarith
    · have : (floorPoint B).y ≤ (floorPoint A).y := by
        unfold floorPoint toInt
        dsimp
        have : B.y ≤ A.y := by linarith
        exact rat_floor_mono this
      have : min (floorPoint A).y (floorPoint B).y = (floorPoint B).y := min_eq_right this
      linarith
    · linarith

theorem bbox_sx_zero (x : Cell) (A B : Point) (h_bbox : inBoundingBox x A B = true)
    (hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = 0) :
    x.x = (floorPoint A).x ∧ x.x = (floorPoint B).x := by
  unfold inBoundingBox at h_bbox
  dsimp only [] at h_bbox
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox
  rcases h_bbox with ⟨⟨⟨h_minX, h_maxX⟩, _⟩, _⟩
  have h_eq : (floorPoint A).x = (floorPoint B).x := by
    revert hsx
    split_ifs with h1 h2
    · intro h; contradiction
    · intro h; contradiction
    · intro _
      have : B.x = A.x := by linarith
      unfold floorPoint toInt
      dsimp
      rw [this]
  rw [h_eq] at h_minX h_maxX
  rw [min_self] at h_minX
  rw [max_self] at h_maxX
  exact ⟨by linarith, by linarith⟩

theorem bbox_sy_zero (x : Cell) (A B : Point) (h_bbox : inBoundingBox x A B = true)
    (hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = 0) :
    x.y = (floorPoint A).y ∧ x.y = (floorPoint B).y := by
  unfold inBoundingBox at h_bbox
  dsimp only [] at h_bbox
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox
  rcases h_bbox with ⟨⟨⟨_, _⟩, h_minY⟩, h_maxY⟩
  have h_eq : (floorPoint A).y = (floorPoint B).y := by
    revert hsy
    split_ifs with h1 h2
    · intro h; contradiction
    · intro h; contradiction
    · intro _
      have : B.y = A.y := by linarith
      unfold floorPoint toInt
      dsimp
      rw [this]
  rw [h_eq] at h_minY h_maxY
  rw [min_self] at h_minY
  rw [max_self] at h_maxY
  exact ⟨by linarith, by linarith⟩


end Geometry
