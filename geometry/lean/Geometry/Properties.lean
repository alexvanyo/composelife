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

/-!
# Part 3: Abstract rayMarch reachability induction
-/

lemma rayMarch_reaches_target (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell : Cell) (x : Cell) (D : Cell → Nat)
    (h_step : ∀ c, D c > 0 →
      (c == endCell) = false ∧
      (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false ∧
      ( (rayMarchStep start ptEnd dx dy stepX stepY c).1 = x ∨
        (D (rayMarchStep start ptEnd dx dy stepX stepY c).1 < D c ∧ D (rayMarchStep start ptEnd dx dy stepX stepY c).1 > 0) )) :
    ∀ current, D current > 0 → D current ≤ fuel →
      x ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  induction fuel with
  | zero =>
    intro current h_pos h_le
    omega
  | succ fuel ih =>
    intro current h_pos h_le
    rcases h_step current h_pos with ⟨h_not_end, h_not_done, h_next⟩
    rw [rayMarch_succ]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h_done : (rayMarchStep start ptEnd dx dy stepX stepY current).2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.mem_cons]
      rcases h_next with rfl | ⟨h_lt, h_next_pos⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        have h_next_le : D (rayMarchStep start ptEnd dx dy stepX stepY current).1 ≤ fuel := by omega
        exact ih (rayMarchStep start ptEnd dx dy stepX stepY current).1 h_next_pos h_next_le
    · rw [h_done] at h_not_done
      contradiction



/-!
# Part 4: rayMarchStep possible outputs
-/

theorem rayMarchStep_mem (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) :
    let S : List (Cell × Bool) :=
      [(c, true), (⟨c.x + stepX, c.y⟩, false), (⟨c.x, c.y + stepY⟩, false), (⟨c.x + stepX, c.y + stepY⟩, false)]
    rayMarchStep start ptEnd dx dy stepX stepY c ∈ S := by
  intro S
  unfold rayMarchStep
  dsimp only []
  have h_in1 : (c, true) ∈ S := by simp [S]
  have h_in2 : (⟨c.x + stepX, c.y⟩, false) ∈ S := by simp [S]
  have h_in3 : (⟨c.x, c.y + stepY⟩, false) ∈ S := by simp [S]
  have h_in4 : (⟨c.x + stepX, c.y + stepY⟩, false) ∈ S := by simp [S]
  by_cases hx0 : stepX == 0
  · simp only [hx0, ite_true]
    by_cases hremY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
      else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ (if dy ≥ 0 then dy else -dy)
    · simp only [hremY, ite_true]; exact h_in1
    · simp only [hremY, ite_false]; exact h_in3
  · simp only [hx0]
    by_cases hy0 : stepY == 0
    · simp only [hy0, ite_true]
      by_cases hremX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
          (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
        else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ (if dx ≥ 0 then dx else -dx)
      · simp only [hremX, ite_true]; exact h_in1
      · simp only [hremX, ite_false]; exact h_in2
    · simp only [hy0]
      by_cases hlim : min
            ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy)
            ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx) ≥
          (if dx ≥ 0 then dx else -dx) * if dy ≥ 0 then dy else -dy
      · simp only [hlim, ite_true]; exact h_in1
      · simp only [hlim, ite_false]
        by_cases hxy : ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy) <
            (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx
        · simp only [hxy, ite_true]; exact h_in2
        · simp only [hxy, ite_false]
          by_cases hyx : ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                  (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
                else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
                if dx ≥ 0 then dx else -dx) <
              (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                  (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
                else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
                if dy ≥ 0 then dy else -dy
          · simp only [hyx, ite_true]; exact h_in3
          · simp only [hyx, ite_false]; exact h_in4

theorem rayMarchStep_fst_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (h_not_done : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false) :
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ := by
  have h_mem := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  dsimp only [] at h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h1 | h2 | h3 | h4
  · have : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = true := by rw [h1]
    rw [this] at h_not_done
    contradiction
  · left
    exact congrArg Prod.fst h2
  · right; left
    exact congrArg Prod.fst h3
  · right; right
    exact congrArg Prod.fst h4




/-! # 1. crossY < crossX when cx = xx -/

theorem cross_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcx : cx = xx) (hcy : cy + 1 ≤ xy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    remY * dx < remX * dy := by
  intro remX remY
  have h_remY_le : remY ≤ ofInt xy - Ay := by
    dsimp [remY, ofInt]
    have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h_remX_ge : ofInt (xx + 1) - Ax ≤ remX := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) = ((cx + 1 : Int) : Rat) := by rw [hcx]
    linarith
  have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
  have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xx + 1) - Ax) / dx := h_tx.2
  have h5 : (ofInt (xx + 1) - Ax) / dx ≤ remX / dx := div_le_div_of_nonneg_right h_remX_ge (le_of_lt hdx)
  have h_lt : remY / dy < remX / dx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX dy dx hdy hdx).mpr h_lt
  linarith

theorem cross_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcx : cx = xx) (hcy : xy + 1 ≤ cy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    remY * dx < remX * absDy := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
  have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
    dsimp [absDy]
    have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xx + 1) - Ax) / dx := h_tx.2
  have h_remX_ge : ofInt (xx + 1) - Ax ≤ remX := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) = ((cx + 1 : Int) : Rat) := by rw [hcx]
    linarith
  have h5 : (ofInt (xx + 1) - Ax) / dx ≤ remX / dx := div_le_div_of_nonneg_right h_remX_ge (le_of_lt hdx)
  have h_lt : remY / absDy < remX / dx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX absDy dx habsDy hdx).mpr h_lt
  linarith

theorem cross_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcx : cx = xx) (hcy : cy + 1 ≤ xy) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    remY * absDx < remX * dy := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have h_remY_le : remY ≤ ofInt xy - Ay := by
    dsimp [remY, ofInt]
    have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / dy ≤ (ofInt xy - Ay) / dy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
  have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xx - Ax) / dx := h_tx.2
  have h_remX_eq : remX / absDx = (ofInt xx - Ax) / dx := by
    dsimp [remX, absDx]
    rw [hcx]
    have : Ax - ofInt xx = -(ofInt xx - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remX / absDx := by rw [h_remX_eq]; exact h4
  have h_lt : remY / dy < remX / absDx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX dy absDx hdy habsDx).mpr h_lt
  linarith

theorem cross_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcx : cx = xx) (hcy : xy + 1 ≤ cy) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    remY * absDx < remX * absDy := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
  have h_eqY : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
    dsimp [absDy]
    have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eqY]; exact h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xx - Ax) / dx := h_tx.2
  have h_eqX : remX / absDx = (ofInt xx - Ax) / dx := by
    dsimp [remX, absDx]
    rw [hcx]
    have : Ax - ofInt xx = -(ofInt xx - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remX / absDx := by rw [h_eqX]; exact h4
  have h_lt : remY / absDy < remX / absDx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX absDy absDx habsDy habsDx).mpr h_lt
  linarith

/-! # 2. crossX < crossY when cy = xy -/

theorem cross_ge_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcy : cy = xy) (hcx : cx + 1 ≤ xx) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    remX * dy < remY * dx := by
  intro remX remY
  have h_remX_le : remX ≤ ofInt xx - Ax := by
    dsimp [remX, ofInt]
    have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h_remY_ge : ofInt (xy + 1) - Ay ≤ remY := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) = ((cy + 1 : Int) : Rat) := by rw [hcy]
    linarith
  have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
  have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xy + 1) - Ay) / dy := h_ty.2
  have h5 : (ofInt (xy + 1) - Ay) / dy ≤ remY / dy := div_le_div_of_nonneg_right h_remY_ge (le_of_lt hdy)
  have h_lt : remX / dx < remY / dy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY dx dy hdx hdy).mpr h_lt
  linarith

theorem cross_ge_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcy : cy = xy) (hcx : cx + 1 ≤ xx) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    remX * absDy < remY * dx := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remX_le : remX ≤ ofInt xx - Ax := by
    dsimp [remX, ofInt]
    have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
  have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xy - Ay) / dy := h_ty.2
  have h_eqY : remY / absDy = (ofInt xy - Ay) / dy := by
    dsimp [remY, absDy]
    rw [hcy]
    have : Ay - ofInt xy = -(ofInt xy - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remY / absDy := by rw [h_eqY]; exact h4
  have h_lt : remX / dx < remY / absDy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY dx absDy hdx habsDy).mpr h_lt
  linarith

theorem cross_ge_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcy : cy = xy) (hcx : xx + 1 ≤ cx) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    remX * dy < remY * absDx := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
    div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
  have h_eqX : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
    dsimp [absDx]
    have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eqX]; exact h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xy + 1) - Ay) / dy := h_ty.2
  have h_remY_ge : ofInt (xy + 1) - Ay ≤ remY := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) = ((cy + 1 : Int) : Rat) := by rw [hcy]
    linarith
  have h5 : (ofInt (xy + 1) - Ay) / dy ≤ remY / dy := div_le_div_of_nonneg_right h_remY_ge (le_of_lt hdy)
  have h_lt : remX / absDx < remY / dy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY absDx dy habsDx hdy).mpr h_lt
  linarith

theorem cross_ge_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcy : cy = xy) (hcx : xx + 1 ≤ cx) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    remX * absDy < remY * absDx := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
    div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
  have h_eqX : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
    dsimp [absDx]
    have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eqX]; exact h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xy - Ay) / dy := h_ty.2
  have h_eqY : remY / absDy = (ofInt xy - Ay) / dy := by
    dsimp [remY, absDy]
    rw [hcy]
    have : Ay - ofInt xy = -(ofInt xy - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remY / absDy := by rw [h_eqY]; exact h4
  have h_lt : remX / absDx < remY / absDy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY absDx absDy habsDx habsDy).mpr h_lt
  linarith


/-! # 3. min crossX crossY < limitCross when cx not reached or cy not reached -/

theorem min_cross_lt_limit_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (h_cases : cx + 1 ≤ xx ∨ cy + 1 ≤ xy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    min (remX * dy) (remY * dx) < dx * dy := by
  intro remX remY
  rw [min_cross_lt_limit_iff remX remY dx dy hdx hdy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ ofInt xx - Ax := by
      dsimp [remX, ofInt]
      have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
    have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / dx < 1 := by linarith
    exact (div_lt_one hdx).mp this
  · right
    have h_remY_le : remY ≤ ofInt xy - Ay := by
      dsimp [remY, ofInt]
      have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
    have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / dy < 1 := by linarith
    exact (div_lt_one hdy).mp this

theorem min_cross_lt_limit_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (h_cases : cx + 1 ≤ xx ∨ xy + 1 ≤ cy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    min (remX * absDy) (remY * dx) < dx * absDy := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  rw [min_cross_lt_limit_iff remX remY dx absDy hdx habsDy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ ofInt xx - Ax := by
      dsimp [remX, ofInt]
      have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
    have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / dx < 1 := by linarith
    exact (div_lt_one hdx).mp this
  · right
    have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
      dsimp [remY, ofInt]
      have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
      dsimp [absDy]
      have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / absDy < 1 := by linarith
    exact (div_lt_one habsDy).mp this

theorem min_cross_lt_limit_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (h_cases : xx + 1 ≤ cx ∨ cy + 1 ≤ xy) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    min (remX * dy) (remY * absDx) < absDx * dy := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  rw [min_cross_lt_limit_iff remX remY absDx dy habsDx hdy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
      dsimp [remX, ofInt]
      have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
      dsimp [absDx]
      have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eq]; exact h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / absDx < 1 := by linarith
    exact (div_lt_one habsDx).mp this
  · right
    have h_remY_le : remY ≤ ofInt xy - Ay := by
      dsimp [remY, ofInt]
      have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
    have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / dy < 1 := by linarith
    exact (div_lt_one hdy).mp this

theorem min_cross_lt_limit_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (h_cases : xx + 1 ≤ cx ∨ xy + 1 ≤ cy) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    min (remX * absDy) (remY * absDx) < absDx * absDy := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  rw [min_cross_lt_limit_iff remX remY absDx absDy habsDx habsDy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
      dsimp [remX, ofInt]
      have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
      dsimp [absDx]
      have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eq]; exact h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / absDx < 1 := by linarith
    exact (div_lt_one habsDx).mp this
  · right
    have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
      dsimp [remY, ofInt]
      have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
      dsimp [absDy]
      have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / absDy < 1 := by linarith
    exact (div_lt_one habsDy).mp this


theorem rayMarchStep_sx_zero (A B : Point) (c : Cell)
    (dy : Rat) (stepY : Int) :
    let stepX : Int := 0
    let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDy := if dy >= 0 then dy else -dy
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    rayMarchStep A B 0 dy stepX stepY c =
      if remY >= absDy then (c, true)
      else (⟨c.x, c.y + stepY⟩, false) := by
  intro stepX yb absDy remY
  unfold rayMarchStep
  dsimp only []
  rfl

theorem step_sx_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (hdx : B.x - A.x = 0) (hdy_ne : B.y - A.y ≠ 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_inter : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_cy_le : 0 ≤ (x.y - c.y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (h_cy_ne : c.y ≠ x.y)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) :
    let stepY : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 stepY c) = (⟨c.x, c.y + stepY⟩, false) ∧
    (x.y - (c.y + stepY)) * stepY < (x.y - c.y) * stepY ∧
    0 ≤ (x.y - (c.y + stepY)) * stepY ∧
    0 ≤ (c.y + stepY - (floorPoint A).y) * stepY := by
  intro stepY
  have h_step := rayMarchStep_sx_zero A B c (B.y - A.y) stepY
  rw [hdx]
  dsimp only [] at h_step
  rw [h_step]
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_inter).2
  by_cases hdy_pos : B.y - A.y > 0
  · have hsy : stepY = 1 := by dsimp [stepY]; simp [hdy_pos]
    have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
      split_ifs with h <;> [rfl; linarith]
    have h_yb : (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) := by
      rw [hsy]; rfl
    have h_cA : (floorPoint A).y ≤ c.y := by
      have : 0 ≤ (c.y - (floorPoint A).y) * 1 := by rw [← hsy]; exact h_cA_y
      omega
    have h_cx_le : c.y + 1 ≤ x.y := by
      have : 0 ≤ (x.y - c.y) * 1 := by rw [← hsy]; exact h_cy_le
      omega
    have h_fl : (floorPoint A).y = toInt A.y := rfl
    have h_lt : A.y < ((floorPoint A).y : Rat) + 1 := by
      have := Rat.lt_floor_add_one A.y
      unfold toInt at h_fl
      rw [← h_fl] at this
      push_cast at this
      exact this
    have h_cast_cA : ((floorPoint A).y : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_cA
    have h_ge : A.y < ofInt (c.y + 1) := by
      dsimp [ofInt]
      push_cast
      linarith
    have h_remY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
      rw [h_yb]
      split_ifs with h <;> [rfl; linarith]
    have h_ty := interval_dy_pos x A B tEnter tExit h_inter hdy_pos
    have h_remY_le : ofInt (c.y + 1) - A.y ≤ ofInt x.y - A.y := by
      dsimp [ofInt]
      have : ((c.y + 1 : Int) : Rat) ≤ ((x.y : Int) : Rat) := Int.cast_le.mpr h_cx_le
      linarith
    have h1 : (ofInt (c.y + 1) - A.y) / (B.y - A.y) ≤ (ofInt x.y - A.y) / (B.y - A.y) :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy_pos)
    have h2 : (ofInt (c.y + 1) - A.y) / (B.y - A.y) < 1 := by linarith [h1, h_ty.1, h_enter_lt_exit, h_exit_le_one]
    have h_remY_lt : ofInt (c.y + 1) - A.y < B.y - A.y := (div_lt_one hdy_pos).mp h2
    have h_not_ge : ¬(ofInt (c.y + 1) - A.y ≥ B.y - A.y) := by linarith
    rw [h_absDy, h_remY]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsy]; omega
    · rw [hsy]; omega
    · rw [hsy]; omega
  · have hdy_neg : B.y - A.y < 0 := by
      rcases lt_or_gt_of_ne hdy_ne with h | h
      · exact h
      · contradiction
    have hsy : stepY = -1 := by
      dsimp [stepY]
      have : ¬(B.y - A.y > 0) := by linarith
      simp [this, hdy_neg]
    have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
      split_ifs with h <;> [linarith; rfl]
    have habsDy : 0 < -(B.y - A.y) := by linarith
    have h_yb : (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt c.y := by
      rw [hsy]; rfl
    have h_cA : c.y ≤ (floorPoint A).y := by
      have : 0 ≤ (c.y - (floorPoint A).y) * (-1) := by rw [← hsy]; exact h_cA_y
      omega
    have h_cx_le : x.y + 1 ≤ c.y := by
      have : 0 ≤ (x.y - c.y) * (-1) := by rw [← hsy]; exact h_cy_le
      omega
    have h_fl : (floorPoint A).y = toInt A.y := rfl
    have h_le : ((floorPoint A).y : Rat) ≤ A.y := by
      have := Rat.floor_le A.y
      unfold toInt at h_fl
      rw [← h_fl] at this
      exact this
    have h_le_A : ofInt c.y ≤ A.y := by
      have : (c.y : Rat) ≤ ((floorPoint A).y : Rat) := Int.cast_le.mpr h_cA
      dsimp [ofInt]
      linarith
    have h_remY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
      rw [h_yb]
      split_ifs with h
      · have : ofInt c.y = A.y := by linarith
        linarith
      · rfl
    have h_ty := interval_dy_neg x A B tEnter tExit h_inter hdy_neg
    have h_remY_le : A.y - ofInt c.y ≤ A.y - ofInt (x.y + 1) := by
      dsimp [ofInt]
      have : ((x.y + 1 : Int) : Rat) ≤ ((c.y : Int) : Rat) := Int.cast_le.mpr h_cx_le
      linarith
    have h1 : (A.y - ofInt c.y) / -(B.y - A.y) ≤ (A.y - ofInt (x.y + 1)) / -(B.y - A.y) :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (A.y - ofInt (x.y + 1)) / -(B.y - A.y) = (ofInt (x.y + 1) - A.y) / (B.y - A.y) := by
      have : A.y - ofInt (x.y + 1) = -(ofInt (x.y + 1) - A.y) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := by linarith [h1, h_eq, h_ty.1, h_enter_lt_exit, h_exit_le_one]
    have h_remY_lt : A.y - ofInt c.y < -(B.y - A.y) := (div_lt_one habsDy).mp h2
    have h_not_ge : ¬(A.y - ofInt c.y ≥ -(B.y - A.y)) := by linarith
    rw [h_absDy, h_remY]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsy]; omega
    · rw [hsy]; omega
    · rw [hsy]; omega


theorem rayMarchStep_sy_zero (A B : Point) (c : Cell)
    (dx : Rat) (stepX : Int) (hx : (stepX == 0) = false) :
    let stepY : Int := 0
    let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let absDx := if dx >= 0 then dx else -dx
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    rayMarchStep A B dx 0 stepX stepY c =
      if remX >= absDx then (c, true)
      else (⟨c.x + stepX, c.y⟩, false) := by
  intro stepY xb absDx remX
  unfold rayMarchStep
  dsimp only []
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem step_sy_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (hdy : B.y - A.y = 0) (hdx_ne : B.x - A.x ≠ 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_inter : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_cx_le : 0 ≤ (x.x - c.x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (h_cx_ne : c.x ≠ x.x)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) :
    let stepX : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) stepX 0 c) = (⟨c.x + stepX, c.y⟩, false) ∧
    (x.x - (c.x + stepX)) * stepX < (x.x - c.x) * stepX ∧
    0 ≤ (x.x - (c.x + stepX)) * stepX ∧
    0 ≤ (c.x + stepX - (floorPoint A).x) * stepX := by
  intro stepX
  have hsx_ne : (stepX == 0) = false := by
    dsimp [stepX]
    rcases lt_or_gt_of_ne hdx_ne with h | h
    · have : ¬(B.x - A.x > 0) := by linarith
      simp [this, h]
    · simp [h]
  have h_step := rayMarchStep_sy_zero A B c (B.x - A.x) stepX hsx_ne
  rw [hdy]
  dsimp only [] at h_step
  rw [h_step]
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_inter).2
  by_cases hdx_pos : B.x - A.x > 0
  · have hsx : stepX = 1 := by dsimp [stepX]; simp [hdx_pos]
    have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
      split_ifs with h <;> [rfl; linarith]
    have h_xb : (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) := by
      rw [hsx]; rfl
    have h_cA : (floorPoint A).x ≤ c.x := by
      have : 0 ≤ (c.x - (floorPoint A).x) * 1 := by rw [← hsx]; exact h_cA_x
      omega
    have h_cx_le' : c.x + 1 ≤ x.x := by
      have : 0 ≤ (x.x - c.x) * 1 := by rw [← hsx]; exact h_cx_le
      omega
    have h_fl : (floorPoint A).x = toInt A.x := rfl
    have h_lt : A.x < ((floorPoint A).x : Rat) + 1 := by
      have := Rat.lt_floor_add_one A.x
      unfold toInt at h_fl
      rw [← h_fl] at this
      push_cast at this
      exact this
    have h_cast_cA : ((floorPoint A).x : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_cA
    have h_ge : A.x < ofInt (c.x + 1) := by
      dsimp [ofInt]
      push_cast
      linarith
    have h_remX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
      rw [h_xb]
      split_ifs with h <;> [rfl; linarith]
    have h_tx := interval_dx_pos x A B tEnter tExit h_inter hdx_pos
    have h_remX_le : ofInt (c.x + 1) - A.x ≤ ofInt x.x - A.x := by
      dsimp [ofInt]
      have : ((c.x + 1 : Int) : Rat) ≤ ((x.x : Int) : Rat) := Int.cast_le.mpr h_cx_le'
      linarith
    have h1 : (ofInt (c.x + 1) - A.x) / (B.x - A.x) ≤ (ofInt x.x - A.x) / (B.x - A.x) :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx_pos)
    have h2 : (ofInt (c.x + 1) - A.x) / (B.x - A.x) < 1 := by linarith [h1, h_tx.1, h_enter_lt_exit, h_exit_le_one]
    have h_remX_lt : ofInt (c.x + 1) - A.x < B.x - A.x := (div_lt_one hdx_pos).mp h2
    have h_not_ge : ¬(ofInt (c.x + 1) - A.x ≥ B.x - A.x) := by linarith
    rw [h_absDx, h_remX]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsx]; omega
    · rw [hsx]; omega
    · rw [hsx]; omega
  · have hdx_neg : B.x - A.x < 0 := by
      rcases lt_or_gt_of_ne hdx_ne with h | h
      · exact h
      · contradiction
    have hsx : stepX = -1 := by
      dsimp [stepX]
      have : ¬(B.x - A.x > 0) := by linarith
      simp [this, hdx_neg]
    have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
      split_ifs with h <;> [linarith; rfl]
    have habsDx : 0 < -(B.x - A.x) := by linarith
    have h_xb : (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt c.x := by
      rw [hsx]; rfl
    have h_cA : c.x ≤ (floorPoint A).x := by
      have : 0 ≤ (c.x - (floorPoint A).x) * (-1) := by rw [← hsx]; exact h_cA_x
      omega
    have h_cx_le' : x.x + 1 ≤ c.x := by
      have : 0 ≤ (x.x - c.x) * (-1) := by rw [← hsx]; exact h_cx_le
      omega
    have h_fl : (floorPoint A).x = toInt A.x := rfl
    have h_le : ((floorPoint A).x : Rat) ≤ A.x := by
      have := Rat.floor_le A.x
      unfold toInt at h_fl
      rw [← h_fl] at this
      exact this
    have h_le_A : ofInt c.x ≤ A.x := by
      have : (c.x : Rat) ≤ ((floorPoint A).x : Rat) := Int.cast_le.mpr h_cA
      dsimp [ofInt]
      linarith
    have h_remX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
      rw [h_xb]
      split_ifs with h
      · have : ofInt c.x = A.x := by linarith
        linarith
      · rfl
    have h_tx := interval_dx_neg x A B tEnter tExit h_inter hdx_neg
    have h_remX_le : A.x - ofInt c.x ≤ A.x - ofInt (x.x + 1) := by
      dsimp [ofInt]
      have : ((x.x + 1 : Int) : Rat) ≤ ((c.x : Int) : Rat) := Int.cast_le.mpr h_cx_le'
      linarith
    have h1 : (A.x - ofInt c.x) / -(B.x - A.x) ≤ (A.x - ofInt (x.x + 1)) / -(B.x - A.x) :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (A.x - ofInt (x.x + 1)) / -(B.x - A.x) = (ofInt (x.x + 1) - A.x) / (B.x - A.x) := by
      have : A.x - ofInt (x.x + 1) = -(ofInt (x.x + 1) - A.x) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := by linarith [h1, h_eq, h_tx.1, h_enter_lt_exit, h_exit_le_one]
    have h_remX_lt : A.x - ofInt c.x < -(B.x - A.x) := (div_lt_one habsDx).mp h2
    have h_not_ge : ¬(A.x - ofInt c.x ≥ -(B.x - A.x)) := by linarith
    rw [h_absDx, h_remX]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsx]; omega
    · rw [hsx]; omega
    · rw [hsx]; omega




theorem rayMarchStep_diag (A B : Point) (c : Cell)
    (dx dy : Rat) (stepX stepY : Int) (hx : (stepX == 0) = false) (hy : (stepY == 0) = false) :
    let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDx := if dx >= 0 then dx else -dx
    let absDy := if dy >= 0 then dy else -dy
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    let crossX := remX * absDy
    let crossY := remY * absDx
    let limitCross := absDx * absDy
    rayMarchStep A B dx dy stepX stepY c =
      if min crossX crossY >= limitCross then (c, true)
      else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
      else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
      else (⟨c.x + stepX, c.y + stepY⟩, false) := by
  intro xb yb absDx absDy remX remY crossX crossY limitCross
  unfold rayMarchStep
  dsimp only []
  simp only [hx, hy, Bool.false_eq_true, ↓reduceIte]
  rfl

def targetDist (sx sy : Int) (x c A : Cell) : Nat :=
  let dx := (x.x - c.x) * sx
  let dy := (x.y - c.y) * sy
  if 0 ≤ (c.x - A.x) * sx ∧ 0 ≤ (c.y - A.y) * sy ∧
     0 ≤ dx ∧ 0 ≤ dy ∧
     (c.x = A.x ∨ sx ≠ 0) ∧ (c.y = A.y ∨ sy ≠ 0) ∧
     c ≠ x then
    (dx + dy).toNat
  else
    0

theorem eq_of_mul_sign_zero (x_val a_val : Int) (dx : Rat)
    (e : (x_val - a_val) * (if dx > 0 then 1 else if dx < 0 then -1 else (0 : Int)) = 0)
    (h_zero : dx = 0 → x_val = a_val) :
    x_val = a_val := by
  split_ifs at e with h1 h2
  · linarith
  · linarith
  · exact h_zero (by linarith)

theorem targetDist_start_pos (A B : Point) (x : Cell)
    (h_bbox : inBoundingBox x A B = true)
    (hxA : x ≠ floorPoint A) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    0 < targetDist sx sy x (floorPoint A) (floorPoint A) := by
  intro sx sy
  unfold targetDist
  dsimp only []
  have h_signs := bbox_signs x A B h_bbox
  have h_ne : floorPoint A ≠ x := hxA.symm
  have h_sum_pos : 0 < (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy := by
    by_contra! h_le
    have h1 := h_signs.1
    have h2 := h_signs.2.2.1
    have e1 : (x.x - (floorPoint A).x) * sx = 0 := by linarith
    have e2 : (x.y - (floorPoint A).y) * sy = 0 := by linarith
    have hx_eq : x.x = (floorPoint A).x :=
      eq_of_mul_sign_zero x.x (floorPoint A).x (B.x - A.x) e1 (fun h => (bbox_sx_zero x A B h_bbox (by simp [h])).1)
    have hy_eq : x.y = (floorPoint A).y :=
      eq_of_mul_sign_zero x.y (floorPoint A).y (B.y - A.y) e2 (fun h => (bbox_sy_zero x A B h_bbox (by simp [h])).1)
    have : x = floorPoint A := by
      cases x
      dsimp at hx_eq hy_eq
      rw [hx_eq, hy_eq]
    contradiction
  have h_all : 0 ≤ ((floorPoint A).x - (floorPoint A).x) * sx ∧
    0 ≤ ((floorPoint A).y - (floorPoint A).y) * sy ∧
    0 ≤ (x.x - (floorPoint A).x) * sx ∧
    0 ≤ (x.y - (floorPoint A).y) * sy ∧
    ((floorPoint A).x = (floorPoint A).x ∨ sx ≠ 0) ∧
    ((floorPoint A).y = (floorPoint A).y ∨ sy ≠ 0) ∧
    floorPoint A ≠ x := ⟨by simp, by simp, h_signs.1, h_signs.2.2.1, Or.inl rfl, Or.inl rfl, h_ne⟩
  split_ifs
  omega

theorem mul_sign_le_natAbs (z : Int) (s : Int) (hs : s = 1 ∨ s = -1 ∨ s = 0) :
    z * s ≤ (z.natAbs : Int) := by
  rcases hs with rfl | rfl | rfl
  · simp
    exact le_max_left z (-z)
  · simp
    exact le_max_right z (-z)
  · simp

theorem sign_cases (v : Rat) :
    (if v > 0 then 1 else if v < 0 then -1 else (0 : Int)) = 1 ∨
    (if v > 0 then 1 else if v < 0 then -1 else (0 : Int)) = -1 ∨
    (if v > 0 then 1 else if v < 0 then -1 else (0 : Int)) = 0 := by
  split_ifs <;> simp

theorem targetDist_start_le (A B : Point) (x : Cell)
    (h_bbox : inBoundingBox x A B = true) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    let fuel := (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
    targetDist sx sy x (floorPoint A) (floorPoint A) ≤ fuel := by
  intro sx sy fuel
  unfold targetDist
  dsimp only []
  have h_signs := bbox_signs x A B h_bbox
  have h_le_x : (x.x - (floorPoint A).x) * sx ≤ ((floorPoint B).x - (floorPoint A).x) * sx := by
    have h1 := h_signs.2.1
    have : ((floorPoint B).x - (floorPoint A).x) * sx =
      (x.x - (floorPoint A).x) * sx + ((floorPoint B).x - x.x) * sx := by ring
    linarith
  have h_le_y : (x.y - (floorPoint A).y) * sy ≤ ((floorPoint B).y - (floorPoint A).y) * sy := by
    have h2 := h_signs.2.2.2
    have : ((floorPoint B).y - (floorPoint A).y) * sy =
      (x.y - (floorPoint A).y) * sy + ((floorPoint B).y - x.y) * sy := by ring
    linarith
  have hsx : sx = 1 ∨ sx = -1 ∨ sx = 0 := sign_cases (B.x - A.x)
  have hsy : sy = 1 ∨ sy = -1 ∨ sy = 0 := sign_cases (B.y - A.y)
  have h_abs_x := mul_sign_le_natAbs ((floorPoint B).x - (floorPoint A).x) sx hsx
  have h_abs_y := mul_sign_le_natAbs ((floorPoint B).y - (floorPoint A).y) sy hsy
  have h_sum : (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy ≤
    (((floorPoint B).x - (floorPoint A).x).natAbs : Int) + (((floorPoint B).y - (floorPoint A).y).natAbs : Int) := by
    linarith
  have h_fuel : (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy ≤ (fuel : Int) := by
    dsimp [fuel]
    omega
  split_ifs <;> omega



theorem targetDist_step_sx_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = 0)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (h_cy : 0 ≤ (x.y - c.y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (hc_x : c.x = (floorPoint A).x)
    (h_ne : c ≠ x) :
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 = x ∨
      (targetDist 0 sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 (floorPoint A) < targetDist 0 sy x c (floorPoint A) ∧
       0 < targetDist 0 sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 (floorPoint A)) ) := by
  intro sy
  have hdx : B.x - A.x = 0 := by
    revert hsx; split_ifs with h1 h2 <;> intro h <;> [contradiction; contradiction; linarith]
  have hdy_ne : B.y - A.y ≠ 0 := by
    intro hdy0
    have hx_eq := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
    have hy_eq := (bbox_sy_zero x A B h_bbox (by simp [hdy0])).1
    have : x = floorPoint A := by cases x; dsimp at hx_eq hy_eq; rw [hx_eq, hy_eq]
    exact hxA this
  have h_cy_ne : c.y ≠ x.y := by
    intro hcy_eq
    have hx_eq : c.x = x.x := by
      have := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
      rw [hc_x, this]
    have : c = x := by cases c; dsimp at hx_eq hcy_eq; rw [hx_eq, hcy_eq]
    exact h_ne this
  have h_step := step_sx_zero A B x c tEnter tExit hdx hdy_ne h_enter_lt_exit h_int h_cy h_cy_ne h_cA_y
  rw [h_step.1]
  dsimp only []
  refine ⟨rfl, ?_⟩
  by_cases h_next_eq : ({ x := c.x, y := c.y + sy } : Cell) = x
  · left; exact h_next_eq
  · right
    have h_Dc : targetDist 0 sy x c (floorPoint A) = ((x.y - c.y) * sy).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * 0 ∧
        0 ≤ (c.y - (floorPoint A).y) * sy ∧
        0 ≤ (x.x - c.x) * 0 ∧
        0 ≤ (x.y - c.y) * sy ∧
        (c.x = (floorPoint A).x ∨ (0 : Int) ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ sy ≠ 0) ∧
        c ≠ x := ⟨by simp, h_cA_y, by simp, h_cy, Or.inl hc_x, Or.inr (by
          dsimp [sy]
          rcases lt_or_gt_of_ne hdy_ne with h | h
          · have : ¬(B.y - A.y > 0) := by linarith
            simp [this, h]
          · simp [h]), h_ne⟩
      split_ifs; simp
    have h_Dnext : targetDist 0 sy x { x := c.x, y := c.y + sy } (floorPoint A) =
        ((x.y - (c.y + sy)) * sy).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * 0 ∧
        0 ≤ (c.y + sy - (floorPoint A).y) * sy ∧
        0 ≤ (x.x - c.x) * 0 ∧
        0 ≤ (x.y - (c.y + sy)) * sy ∧
        (c.x = (floorPoint A).x ∨ (0 : Int) ≠ 0) ∧
        (c.y + sy = (floorPoint A).y ∨ sy ≠ 0) ∧
        ({ x := c.x, y := c.y + sy } : Cell) ≠ x := ⟨by simp, h_step.2.2.2, by simp, h_step.2.2.1, Or.inl hc_x, Or.inr (by
          dsimp [sy]
          rcases lt_or_gt_of_ne hdy_ne with h | h
          · have : ¬(B.y - A.y > 0) := by linarith
            simp [this, h]
          · simp [h]), h_next_eq⟩
      split_ifs; simp
    rw [h_Dc, h_Dnext]
    have h_lt := h_step.2.1
    have h_ge := h_step.2.2.1
    have h_sy_ne : sy ≠ 0 := by
      dsimp [sy]
      rcases lt_or_gt_of_ne hdy_ne with h | h
      · have : ¬(B.y - A.y > 0) := by linarith
        simp [this, h]
      · simp [h]
    have h_next_y_ne : c.y + sy ≠ x.y := by
      intro h_eq
      apply h_next_eq
      have h_x_eq : c.x = x.x := by
        have := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
        rw [hc_x, this]
      cases c
      cases x
      dsimp at h_x_eq h_eq
      rw [h_x_eq, h_eq]
    dsimp [sy] at *
    have h_pos : 0 < (x.y - (c.y + if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)) *
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) := by
      have : (x.y - (c.y + if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)) *
          (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) ≠ 0 := by
        intro h0
        rcases mul_eq_zero.mp h0 with h1 | h2
        · apply h_next_y_ne; linarith
        · contradiction
      omega
    refine ⟨by omega, by omega⟩


theorem targetDist_step_sy_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (h_cx : 0 ≤ (x.x - c.x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (hc_y : c.y = (floorPoint A).y)
    (h_ne : c ≠ x) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 = x ∨
      (targetDist sx 0 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 (floorPoint A) < targetDist sx 0 x c (floorPoint A) ∧
       0 < targetDist sx 0 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 (floorPoint A)) ) := by
  intro sx
  have hdy : B.y - A.y = 0 := by
    revert hsy; split_ifs with h1 h2 <;> intro h <;> [contradiction; contradiction; linarith]
  have hdx_ne : B.x - A.x ≠ 0 := by
    intro hdx0
    have hx_eq := (bbox_sx_zero x A B h_bbox (by simp [hdx0])).1
    have hy_eq := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
    have : x = floorPoint A := by cases x; dsimp at hx_eq hy_eq; rw [hx_eq, hy_eq]
    exact hxA this
  have h_cx_ne : c.x ≠ x.x := by
    intro hcx_eq
    have hy_eq : c.y = x.y := by
      have := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
      rw [hc_y, this]
    have : c = x := by cases c; dsimp at hcx_eq hy_eq; rw [hcx_eq, hy_eq]
    exact h_ne this
  have h_step := step_sy_zero A B x c tEnter tExit hdy hdx_ne h_enter_lt_exit h_int h_cx h_cx_ne h_cA_x
  rw [h_step.1]
  dsimp only []
  refine ⟨rfl, ?_⟩
  by_cases h_next_eq : ({ x := c.x + sx, y := c.y } : Cell) = x
  · left; exact h_next_eq
  · right
    have h_Dc : targetDist sx 0 x c (floorPoint A) = ((x.x - c.x) * sx).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * sx ∧
        0 ≤ (c.y - (floorPoint A).y) * 0 ∧
        0 ≤ (x.x - c.x) * sx ∧
        0 ≤ (x.y - c.y) * 0 ∧
        (c.x = (floorPoint A).x ∨ sx ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ (0 : Int) ≠ 0) ∧
        c ≠ x := ⟨h_cA_x, by simp, h_cx, by simp, Or.inr (by
          dsimp [sx]
          rcases lt_or_gt_of_ne hdx_ne with h | h
          · have : ¬(B.x - A.x > 0) := by linarith
            simp [this, h]
          · simp [h]), Or.inl hc_y, h_ne⟩
      split_ifs; simp
    have h_Dnext : targetDist sx 0 x { x := c.x + sx, y := c.y } (floorPoint A) =
        ((x.x - (c.x + sx)) * sx).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x + sx - (floorPoint A).x) * sx ∧
        0 ≤ (c.y - (floorPoint A).y) * 0 ∧
        0 ≤ (x.x - (c.x + sx)) * sx ∧
        0 ≤ (x.y - c.y) * 0 ∧
        (c.x + sx = (floorPoint A).x ∨ sx ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ (0 : Int) ≠ 0) ∧
        ({ x := c.x + sx, y := c.y } : Cell) ≠ x := ⟨h_step.2.2.2, by simp, h_step.2.2.1, by simp, Or.inr (by
          dsimp [sx]
          rcases lt_or_gt_of_ne hdx_ne with h | h
          · have : ¬(B.x - A.x > 0) := by linarith
            simp [this, h]
          · simp [h]), Or.inl hc_y, h_next_eq⟩
      split_ifs; simp
    rw [h_Dc, h_Dnext]
    have h_lt := h_step.2.1
    have h_ge := h_step.2.2.1
    have h_sx_ne : sx ≠ 0 := by
      dsimp [sx]
      rcases lt_or_gt_of_ne hdx_ne with h | h
      · have : ¬(B.x - A.x > 0) := by linarith
        simp [this, h]
      · simp [h]
    have h_next_x_ne : c.x + sx ≠ x.x := by
      intro h_eq
      apply h_next_eq
      have h_y_eq : c.y = x.y := by
        have := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
        rw [hc_y, this]
      cases c
      cases x
      dsimp at h_eq h_y_eq
      rw [h_eq, h_y_eq]
    dsimp [sx] at *
    have h_pos : 0 < (x.x - (c.x + if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)) *
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) := by
      have : (x.x - (c.x + if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)) *
          (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) ≠ 0 := by
        intro h0
        rcases mul_eq_zero.mp h0 with h1 | h2
        · apply h_next_x_ne; linarith
        · contradiction
      omega
    refine ⟨by omega, by omega⟩


theorem targetDist_step_pos_pos (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * 1)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * 1)
    (h_cx : 0 ≤ (x.x - c.x) * 1)
    (h_cy : 0 ≤ (x.y - c.y) * 1)
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 = x ∨
      (targetDist 1 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 (floorPoint A) < targetDist 1 1 x c (floorPoint A) ∧
       0 < targetDist 1 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 (floorPoint A)) ) := by
  have hsx_ne : ((1 : Int) == 0) = false := rfl
  have hsy_ne : ((1 : Int) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) 1 1 hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_pos x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_pos x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
    split_ifs with h <;> [rfl; linarith]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
    split_ifs with h <;> [rfl; linarith]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_lt_x : A.x < ((floorPoint A).x : Rat) + 1 := by
    have := Rat.lt_floor_add_one A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; push_cast at this; exact this
  have h_cast_cA_x : ((floorPoint A).x : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr (by omega)
  have h_ge_x : A.x < ofInt (c.x + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_lt_y : A.y < ((floorPoint A).y : Rat) + 1 := by
    have := Rat.lt_floor_add_one A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; push_cast at this; exact this
  have h_cast_cA_y : ((floorPoint A).y : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr (by omega)
  have h_ge_y : A.y < ofInt (c.y + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_one_pos : (1 : Int) > 0 := by decide
  have h_remX : (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_remY : (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_cases : c.x + 1 ≤ x.x ∨ c.y + 1 ≤ x.y := by
    rcases lt_or_eq_of_le (show c.x ≤ x.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show c.y ≤ x.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((ofInt (c.x + 1) - A.x) * (B.y - A.y)) ((ofInt (c.y + 1) - A.y) * (B.x - A.x)) ≥
      (B.x - A.x) * (B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (ofInt (c.x + 1) - A.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * (B.x - A.x) then
      (({ x := c.x + 1, y := c.y } : Cell), false)
    else if (ofInt (c.y + 1) - A.y) * (B.x - A.x) < (ofInt (c.x + 1) - A.x) * (B.y - A.y) then
      (({ x := c.x, y := c.y + 1 } : Cell), false)
    else (({ x := c.x + 1, y := c.y + 1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : Int), (floorPoint A).x ≤ px → (floorPoint A).y ≤ py →
      px ≤ x.x → py ≤ x.y → ({ x := px, y := py } : Cell) ≠ x →
      targetDist 1 1 x { x := px, y := py } (floorPoint A) = ((x.x - px) + (x.y - py)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * 1 ∧
      0 ≤ (py - (floorPoint A).y) * 1 ∧
      0 ≤ (x.x - px) * 1 ∧
      0 ≤ (x.y - py) * 1 ∧
      (px = (floorPoint A).x ∨ (1 : Int) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (1 : Int) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; simp
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist 1 1 x c (floorPoint A) = ((x.x - c.x) + (x.y - c.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : Int, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show c.x ≤ x.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so cy + 1 ≤ xy
    have hcy_le : c.y + 1 ≤ x.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((ofInt (c.x + 1) - A.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * (B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show c.y ≤ x.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so cx + 1 ≤ xx
      have hcx_le : c.x + 1 ≤ x.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : c.x + 1 ≤ x.x := hcx_lt
      have hcy_le : c.y + 1 ≤ x.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_pos_neg (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * 1)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * (-1))
    (h_cx : 0 ≤ (x.x - c.x) * 1)
    (h_cy : 0 ≤ (x.y - c.y) * (-1))
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 = x ∨
      (targetDist 1 (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 (floorPoint A) < targetDist 1 (-1) x c (floorPoint A) ∧
       0 < targetDist 1 (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 (floorPoint A)) ) := by
  have hsx_ne : ((1 : Int) == 0) = false := rfl
  have hsy_ne : ((-1 : Int) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) 1 (-1) hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_pos x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_neg x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
    split_ifs with h <;> [rfl; linarith]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
    split_ifs with h <;> [linarith; rfl]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_lt_x : A.x < ((floorPoint A).x : Rat) + 1 := by
    have := Rat.lt_floor_add_one A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; push_cast at this; exact this
  have h_cast_cA_x : ((floorPoint A).x : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr (by omega)
  have h_ge_x : A.x < ofInt (c.x + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_le_y : ((floorPoint A).y : Rat) ≤ A.y := by
    have := Rat.floor_le A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; exact this
  have h_cast_cA_y : (c.y : Rat) ≤ ((floorPoint A).y : Rat) := Int.cast_le.mpr (by omega)
  have h_le_cA_y : ofInt c.y ≤ A.y := by dsimp [ofInt]; linarith
  have h_one_pos : (1 : Int) > 0 := by decide
  have h_neg_one_not_pos : ¬((-1 : Int) > 0) := by decide
  have h_remX : (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_remY : (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_cases : c.x + 1 ≤ x.x ∨ x.y + 1 ≤ c.y := by
    rcases lt_or_eq_of_le (show c.x ≤ x.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show x.y ≤ c.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((ofInt (c.x + 1) - A.x) * -(B.y - A.y)) ((A.y - ofInt c.y) * (B.x - A.x)) ≥
      (B.x - A.x) * -(B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (ofInt (c.x + 1) - A.x) * -(B.y - A.y) < (A.y - ofInt c.y) * (B.x - A.x) then
      (({ x := c.x + 1, y := c.y } : Cell), false)
    else if (A.y - ofInt c.y) * (B.x - A.x) < (ofInt (c.x + 1) - A.x) * -(B.y - A.y) then
      (({ x := c.x, y := c.y + -1 } : Cell), false)
    else (({ x := c.x + 1, y := c.y + -1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : Int), (floorPoint A).x ≤ px → py ≤ (floorPoint A).y →
      px ≤ x.x → x.y ≤ py → ({ x := px, y := py } : Cell) ≠ x →
      targetDist 1 (-1) x { x := px, y := py } (floorPoint A) = ((x.x - px) + (py - x.y)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * 1 ∧
      0 ≤ (py - (floorPoint A).y) * (-1) ∧
      0 ≤ (x.x - px) * 1 ∧
      0 ≤ (x.y - py) * (-1) ∧
      (px = (floorPoint A).x ∨ (1 : Int) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (-1 : Int) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist 1 (-1) x c (floorPoint A) = ((x.x - c.x) + (c.y - x.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : Int, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show c.x ≤ x.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so xy + 1 ≤ cy
    have hcy_le : x.y + 1 ≤ c.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((ofInt (c.x + 1) - A.x) * -(B.y - A.y) < (A.y - ofInt c.y) * (B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show x.y ≤ c.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so cx + 1 ≤ xx
      have hcx_le : c.x + 1 ≤ x.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq.symm hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : c.x + 1 ≤ x.x := hcx_lt
      have hcy_le : x.y + 1 ≤ c.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_neg_pos (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * (-1))
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * 1)
    (h_cx : 0 ≤ (x.x - c.x) * (-1))
    (h_cy : 0 ≤ (x.y - c.y) * 1)
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 = x ∨
      (targetDist (-1) 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 (floorPoint A) < targetDist (-1) 1 x c (floorPoint A) ∧
       0 < targetDist (-1) 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 (floorPoint A)) ) := by
  have hsx_ne : (((-1 : Int) == 0) = false) := rfl
  have hsy_ne : ((1 : Int) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) (-1) 1 hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_neg x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_pos x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
    split_ifs with h <;> [linarith; rfl]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
    split_ifs with h <;> [rfl; linarith]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_le_x : ((floorPoint A).x : Rat) ≤ A.x := by
    have := Rat.floor_le A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; exact this
  have h_cast_cA_x : (c.x : Rat) ≤ ((floorPoint A).x : Rat) := Int.cast_le.mpr (by omega)
  have h_le_cA_x : ofInt c.x ≤ A.x := by dsimp [ofInt]; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_lt_y : A.y < ((floorPoint A).y : Rat) + 1 := by
    have := Rat.lt_floor_add_one A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; push_cast at this; exact this
  have h_cast_cA_y : ((floorPoint A).y : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr (by omega)
  have h_ge_y : A.y < ofInt (c.y + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_one_pos : (1 : Int) > 0 := by decide
  have h_neg_one_not_pos : ¬((-1 : Int) > 0) := by decide
  have h_remX : (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_remY : (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_cases : x.x + 1 ≤ c.x ∨ c.y + 1 ≤ x.y := by
    rcases lt_or_eq_of_le (show x.x ≤ c.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show c.y ≤ x.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((A.x - ofInt c.x) * (B.y - A.y)) ((ofInt (c.y + 1) - A.y) * -(B.x - A.x)) ≥
      -(B.x - A.x) * (B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (A.x - ofInt c.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * -(B.x - A.x) then
      (({ x := c.x + -1, y := c.y } : Cell), false)
    else if (ofInt (c.y + 1) - A.y) * -(B.x - A.x) < (A.x - ofInt c.x) * (B.y - A.y) then
      (({ x := c.x, y := c.y + 1 } : Cell), false)
    else (({ x := c.x + -1, y := c.y + 1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : Int), px ≤ (floorPoint A).x → (floorPoint A).y ≤ py →
      x.x ≤ px → py ≤ x.y → ({ x := px, y := py } : Cell) ≠ x →
      targetDist (-1) 1 x { x := px, y := py } (floorPoint A) = ((px - x.x) + (x.y - py)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * (-1) ∧
      0 ≤ (py - (floorPoint A).y) * 1 ∧
      0 ≤ (x.x - px) * (-1) ∧
      0 ≤ (x.y - py) * 1 ∧
      (px = (floorPoint A).x ∨ (-1 : Int) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (1 : Int) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist (-1) 1 x c (floorPoint A) = ((c.x - x.x) + (x.y - c.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : Int, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show x.x ≤ c.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so cy + 1 ≤ xy
    have hcy_le : c.y + 1 ≤ x.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq.symm hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((A.x - ofInt c.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * -(B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show c.y ≤ x.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so xx + 1 ≤ cx
      have hcx_le : x.x + 1 ≤ c.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : x.x + 1 ≤ c.x := hcx_lt
      have hcy_le : c.y + 1 ≤ x.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_neg_neg (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * (-1))
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * (-1))
    (h_cx : 0 ≤ (x.x - c.x) * (-1))
    (h_cy : 0 ≤ (x.y - c.y) * (-1))
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 = x ∨
      (targetDist (-1) (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 (floorPoint A) < targetDist (-1) (-1) x c (floorPoint A) ∧
       0 < targetDist (-1) (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 (floorPoint A)) ) := by
  have hsx_ne : (((-1 : Int) == 0) = false) := rfl
  have hsy_ne : (((-1 : Int) == 0) = false) := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) (-1) (-1) hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_neg x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_neg x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
    split_ifs with h <;> [linarith; rfl]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
    split_ifs with h <;> [linarith; rfl]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_le_x : ((floorPoint A).x : Rat) ≤ A.x := by
    have := Rat.floor_le A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; exact this
  have h_cast_cA_x : (c.x : Rat) ≤ ((floorPoint A).x : Rat) := Int.cast_le.mpr (by omega)
  have h_le_cA_x : ofInt c.x ≤ A.x := by dsimp [ofInt]; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_le_y : ((floorPoint A).y : Rat) ≤ A.y := by
    have := Rat.floor_le A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; exact this
  have h_cast_cA_y : (c.y : Rat) ≤ ((floorPoint A).y : Rat) := Int.cast_le.mpr (by omega)
  have h_le_cA_y : ofInt c.y ≤ A.y := by dsimp [ofInt]; linarith
  have h_neg_one_not_pos : ¬((-1 : Int) > 0) := by decide
  have h_remX : (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_remY : (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_cases : x.x + 1 ≤ c.x ∨ x.y + 1 ≤ c.y := by
    rcases lt_or_eq_of_le (show x.x ≤ c.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show x.y ≤ c.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((A.x - ofInt c.x) * -(B.y - A.y)) ((A.y - ofInt c.y) * -(B.x - A.x)) ≥
      -(B.x - A.x) * -(B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (A.x - ofInt c.x) * -(B.y - A.y) < (A.y - ofInt c.y) * -(B.x - A.x) then
      (({ x := c.x + -1, y := c.y } : Cell), false)
    else if (A.y - ofInt c.y) * -(B.x - A.x) < (A.x - ofInt c.x) * -(B.y - A.y) then
      (({ x := c.x, y := c.y + -1 } : Cell), false)
    else (({ x := c.x + -1, y := c.y + -1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : Int), px ≤ (floorPoint A).x → py ≤ (floorPoint A).y →
      x.x ≤ px → x.y ≤ py → ({ x := px, y := py } : Cell) ≠ x →
      targetDist (-1) (-1) x { x := px, y := py } (floorPoint A) = ((px - x.x) + (py - x.y)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * (-1) ∧
      0 ≤ (py - (floorPoint A).y) * (-1) ∧
      0 ≤ (x.x - px) * (-1) ∧
      0 ≤ (x.y - py) * (-1) ∧
      (px = (floorPoint A).x ∨ (-1 : Int) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (-1 : Int) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist (-1) (-1) x c (floorPoint A) = ((c.x - x.x) + (c.y - x.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : Int, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show x.x ≤ c.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so xy + 1 ≤ cy
    have hcy_le : x.y + 1 ≤ c.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq.symm hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((A.x - ofInt c.x) * -(B.y - A.y) < (A.y - ofInt c.y) * -(B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show x.y ≤ c.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so xx + 1 ≤ cx
      have hcx_le : x.x + 1 ≤ c.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq.symm hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : x.x + 1 ≤ c.x := hcx_lt
      have hcy_le : x.y + 1 ≤ c.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem not_endCell_of_dist_pos (A B : Point) (x c : Cell)
    (h_bbox : inBoundingBox x A B = true) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    targetDist sx sy x c (floorPoint A) > 0 → (c == floorPoint B) = false := by
  intro sx sy hD
  have h_signs := bbox_signs x A B h_bbox
  unfold targetDist at hD
  dsimp only [] at hD
  split_ifs at hD with hcond
  · cases h_eq : (c == floorPoint B)
    · rfl
    · exfalso
      have hcB : c = floorPoint B := eq_of_beq h_eq
      have hBx : ((floorPoint B).x - x.x) * sx ≥ 0 := h_signs.2.1
      have hBy : ((floorPoint B).y - x.y) * sy ≥ 0 := h_signs.2.2.2
      have h1 : (x.x - c.x) * sx ≤ 0 := by
        rw [hcB]
        have : (x.x - (floorPoint B).x) * sx = -(((floorPoint B).x - x.x) * sx) := by ring
        linarith
      have h2 : (x.y - c.y) * sy ≤ 0 := by
        rw [hcB]
        have : (x.y - (floorPoint B).y) * sy = -(((floorPoint B).y - x.y) * sy) := by ring
        linarith
      have hdx0 : (x.x - c.x) * sx = 0 := by linarith [hcond.2.2.1]
      have hdy0 : (x.y - c.y) * sy = 0 := by linarith [hcond.2.2.2.1]
      rw [hdx0, hdy0] at hD
      revert hD; decide
  · contradiction



theorem targetDist_step_combined (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit) :
    let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    targetDist sx sy x c (floorPoint A) > 0 →
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 = x ∨
      (targetDist sx sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 (floorPoint A) < targetDist sx sy x c (floorPoint A) ∧
       0 < targetDist sx sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 (floorPoint A)) ) := by
  intro sx sy hD
  have hD_copy := hD
  unfold targetDist at hD
  dsimp only [] at hD
  split_ifs at hD with hcond
  swap
  · contradiction
  rcases hcond with ⟨h_cA_x, h_cA_y, h_cx, h_cy, hc_x_or, hc_y_or, h_ne⟩
  by_cases hsx : sx = 0
  · have hc_x : c.x = (floorPoint A).x := by
      cases hc_x_or with
      | inl h => exact h
      | inr h => contradiction
    rw [hsx]
    exact targetDist_step_sx_zero A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hsx h_cA_y h_cy hc_x h_ne
  · by_cases hsy : sy = 0
    · have hc_y : c.y = (floorPoint A).y := by
        cases hc_y_or with
        | inl h => exact h
        | inr h => contradiction
      rw [hsy]
      exact targetDist_step_sy_zero A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hsy h_cA_x h_cx hc_y h_ne
    · -- both non-zero
      have hsx_cases : (B.x - A.x > 0 ∧ sx = 1) ∨ (B.x - A.x < 0 ∧ sx = -1) := by
        dsimp [sx] at hsx ⊢
        split_ifs with h1 h2
        · left; exact ⟨h1, rfl⟩
        · right; exact ⟨h2, rfl⟩
        · exfalso; apply hsx; simp only [h1, h2, ↓reduceIte]
      have hsy_cases : (B.y - A.y > 0 ∧ sy = 1) ∨ (B.y - A.y < 0 ∧ sy = -1) := by
        dsimp [sy] at hsy ⊢
        split_ifs with h1 h2
        · left; exact ⟨h1, rfl⟩
        · right; exact ⟨h2, rfl⟩
        · exfalso; apply hsy; simp only [h1, h2, ↓reduceIte]
      rcases hsx_cases with ⟨hdx_pos, hsx1⟩ | ⟨hdx_neg, hsx_neg1⟩
      · rcases hsy_cases with ⟨hdy_pos, hsy1⟩ | ⟨hdy_neg, hsy_neg1⟩
        · -- pos_pos
          rw [hsx1, hsy1]
          rw [hsx1] at h_cA_x h_cx
          rw [hsy1] at h_cA_y h_cy
          exact targetDist_step_pos_pos A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_pos hdy_pos h_cA_x h_cA_y h_cx h_cy h_ne
        · -- pos_neg
          rw [hsx1, hsy_neg1]
          rw [hsx1] at h_cA_x h_cx
          rw [hsy_neg1] at h_cA_y h_cy
          exact targetDist_step_pos_neg A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_pos hdy_neg h_cA_x h_cA_y h_cx h_cy h_ne
      · rcases hsy_cases with ⟨hdy_pos, hsy1⟩ | ⟨hdy_neg, hsy_neg1⟩
        · -- neg_pos
          rw [hsx_neg1, hsy1]
          rw [hsx_neg1] at h_cA_x h_cx
          rw [hsy1] at h_cA_y h_cy
          exact targetDist_step_neg_pos A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_neg hdy_pos h_cA_x h_cA_y h_cx h_cy h_ne
        · -- neg_neg
          rw [hsx_neg1, hsy_neg1]
          rw [hsx_neg1] at h_cA_x h_cx
          rw [hsy_neg1] at h_cA_y h_cy
          exact targetDist_step_neg_neg A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_neg hdy_neg h_cA_x h_cA_y h_cx h_cy h_ne

theorem rayMarch_completeness (A B : Point) (x : Cell)
    (hxA : x ≠ floorPoint A) (_hxB : x ≠ floorPoint B)
    (h_bbox : inBoundingBox x A B = true)
    (h_int : ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit) :
    x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] := by
  rcases h_int with ⟨tEnter, tExit, h_inter, h_enter_lt_exit⟩
  let sx : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
  let sy : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
  let fuel : Nat := ((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2
  let D := fun c => targetDist sx sy x c (floorPoint A)
  have h_step : ∀ c, D c > 0 →
      (c == floorPoint B) = false ∧
      (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).2 = false ∧
      ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 = x ∨
        (D (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 < D c ∧
         D (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 > 0) ) := by
    intro c hcD
    refine ⟨not_endCell_of_dist_pos A B x c h_bbox hcD, ?_⟩
    exact targetDist_step_combined A B x c tEnter tExit h_bbox hxA h_inter h_enter_lt_exit hcD
  have h_start_pos : D (floorPoint A) > 0 := targetDist_start_pos A B x h_bbox hxA
  have h_start_le : D (floorPoint A) ≤ fuel := targetDist_start_le A B x h_bbox
  exact rayMarch_reaches_target fuel A B (B.x - A.x) (B.y - A.y) sx sy (floorPoint B) x D h_step (floorPoint A) h_start_pos h_start_le



/- =========================================================================
   Common Base Lemmas
   ========================================================================= -/

def absVal (r : Rat) : Rat := if r ≥ 0 then r else -r


def remX_val (start : Point) (stepX : Int) (c : Cell) : Rat :=
  let xb := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
  if xb ≥ start.x then xb - start.x else start.x - xb


def remY_val (start : Point) (stepY : Int) (c : Cell) : Rat :=
  let yb := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
  if yb ≥ start.y then yb - start.y else start.y - yb


theorem rayMarchStep_mem_dup (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) :
    let S : List (Cell × Bool) :=
      [(c, true), (⟨c.x + stepX, c.y⟩, false), (⟨c.x, c.y + stepY⟩, false), (⟨c.x + stepX, c.y + stepY⟩, false)]
    rayMarchStep start ptEnd dx dy stepX stepY c ∈ S := by
  intro S
  unfold rayMarchStep
  dsimp only []
  have h_in1 : (c, true) ∈ S := by simp [S]
  have h_in2 : (⟨c.x + stepX, c.y⟩, false) ∈ S := by simp [S]
  have h_in3 : (⟨c.x, c.y + stepY⟩, false) ∈ S := by simp [S]
  have h_in4 : (⟨c.x + stepX, c.y + stepY⟩, false) ∈ S := by simp [S]
  by_cases hx0 : stepX == 0
  · simp only [hx0]
    by_cases hremY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
      else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ (if dy ≥ 0 then dy else -dy)
    · simp only [hremY, ↓reduceIte]
      exact h_in1
    · simp only [hremY, ↓reduceIte]
      exact h_in3
  · simp only [hx0]
    by_cases hy0 : stepY == 0
    · simp only [hy0]
      by_cases hremX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
          (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
        else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ (if dx ≥ 0 then dx else -dx)
      · simp only [hremX, ↓reduceIte]
        exact h_in1
      · simp only [hremX, ↓reduceIte]
        exact h_in2
    · simp only [hy0]
      by_cases hlim : min
            ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy)
            ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx) ≥
          (if dx ≥ 0 then dx else -dx) * if dy ≥ 0 then dy else -dy
      · simp only [hlim, ↓reduceIte]
        exact h_in1
      · simp only [hlim, ↓reduceIte]
        by_cases hxy : ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy) <
            (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx
        · simp only [hxy, ↓reduceIte]
          exact h_in2
        · simp only [hxy, ↓reduceIte]
          by_cases hyx : ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                  (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
                else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
                if dx ≥ 0 then dx else -dx) <
              (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                  (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
                else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
                if dy ≥ 0 then dy else -dy
          · simp only [hyx, ↓reduceIte]
            exact h_in3
          · simp only [hyx, ↓reduceIte]
            exact h_in4


theorem rayMarchStep_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) :
    rayMarchStep start ptEnd dx dy stepX stepY c = (c, true) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x + stepX, c.y⟩, false) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x, c.y + stepY⟩, false) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x + stepX, c.y + stepY⟩, false) := by
  have h_mem := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  exact h_mem


theorem rayMarchStep_not_done_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (h_not_done : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false) :
    let next := (rayMarchStep start ptEnd dx dy stepX stepY c).1
    next = ⟨c.x + stepX, c.y⟩ ∨ next = ⟨c.x, c.y + stepY⟩ ∨ next = ⟨c.x + stepX, c.y + stepY⟩ := by
  have h := rayMarchStep_cases start ptEnd dx dy stepX stepY c
  rcases h with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done
    contradiction
  · rw [h2]
    exact Or.inl rfl
  · rw [h3]
    exact Or.inr (Or.inl rfl)
  · rw [h4]
    exact Or.inr (Or.inr rfl)


theorem rayMarch_same_endpoints (fuel : Nat) (A B : Point) (dx dy : Rat) (stepX stepY : Int)
    (h : floorPoint A = floorPoint B) :
    rayMarch (fuel + 1) A B dx dy stepX stepY (floorPoint B) (floorPoint A) [] = [] := by
  rw [rayMarch_succ]
  dsimp only []
  have : (floorPoint A == floorPoint B) = true := by rw [h]; exact beq_self_eq_true _
  simp [this]


theorem floor_mono {x y : Rat} (h : x ≤ y) : Rat.floor x ≤ Rat.floor y := by
  have h1 : ((Rat.floor x : Int) : Rat) ≤ x := Rat.floor_le x
  have h2 : ((Rat.floor x : Int) : Rat) ≤ y := le_trans h1 h
  by_contra! h_lt
  have : Rat.floor y + 1 ≤ Rat.floor x := h_lt
  have h_le : ((Rat.floor y + 1 : Int) : Rat) ≤ ((Rat.floor x : Int) : Rat) := Int.cast_le.mpr this
  have h_lt_cast : y < ((Rat.floor y + 1 : Int) : Rat) := Rat.lt_floor_add_one y
  linarith


theorem floor_le_sub_one_of_lt (y : Rat) (cy : Int) (h : y < ofInt cy) :
    Rat.floor y ≤ cy - 1 := by
  have h1 : ((Rat.floor y : Int) : Rat) ≤ y := Rat.floor_le y
  have h2 : ((Rat.floor y : Int) : Rat) < ofInt cy := lt_of_le_of_lt h1 h
  unfold ofInt at h2
  change ((Rat.floor y : Int) : Rat) < ((cy : Int) : Rat) at h2
  have h3 : Rat.floor y < cy := Int.cast_lt.mp h2
  omega


theorem stepX_pos_next_le_end (cx : Int) (Ax : Rat) (B : Point)
    (_hdx : 0 < B.x - Ax)
    (h_bnd : ofInt cx - Ax < B.x - Ax) :
    cx ≤ (floorPoint B).x := by
  have h_lt : ((cx : Int) : Rat) ≤ B.x := by
    change ((cx : Int) : Rat) - Ax < B.x - Ax at h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact le_floor_of_le cx B.x h_lt


theorem stepY_pos_next_le_end (cy : Int) (Ay : Rat) (B : Point)
    (_hdy : 0 < B.y - Ay)
    (h_bnd : ofInt cy - Ay < B.y - Ay) :
    cy ≤ (floorPoint B).y := by
  have h_lt : ((cy : Int) : Rat) ≤ B.y := by
    change ((cy : Int) : Rat) - Ay < B.y - Ay at h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact le_floor_of_le cy B.y h_lt


theorem stepX_neg_next_ge_end (cx : Int) (Ax : Rat) (B : Point)
    (hdx : B.x - Ax < 0)
    (h_bnd : (ofInt cx - Ax) / (B.x - Ax) < 1) :
    (floorPoint B).x ≤ cx - 1 := by
  have h_gt : B.x < ofInt cx := by
    have := (div_lt_one_of_neg hdx).mp h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact floor_le_sub_one_of_lt B.x cx h_gt


theorem stepY_neg_next_ge_end (cy : Int) (Ay : Rat) (B : Point)
    (hdy : B.y - Ay < 0)
    (h_bnd : (ofInt cy - Ay) / (B.y - Ay) < 1) :
    (floorPoint B).y ≤ cy - 1 := by
  have h_gt : B.y < ofInt cy := by
    have := (div_lt_one_of_neg hdy).mp h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact floor_le_sub_one_of_lt B.y cy h_gt


theorem inBoundingBox_stepX_forward (c : Cell) (A B : Point)
    (hdx : 0 < B.x - A.x)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : c.x + 1 ≤ (floorPoint B).x) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorA : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
  have h_min : min (floorPoint A).x (floorPoint B).x = (floorPoint A).x := min_eq_left h_floorA
  have h_max : max (floorPoint A).x (floorPoint B).x = (floorPoint B).x := max_eq_right h_floorA
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨by omega, h_next⟩, h3⟩, h4⟩


theorem inBoundingBox_stepX_backward (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : (floorPoint B).x ≤ c.x - 1) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorB : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
  have h_min : min (floorPoint A).x (floorPoint B).x = (floorPoint B).x := min_eq_right h_floorB
  have h_max : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_floorB
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h_next, by omega⟩, h3⟩, h4⟩


theorem inBoundingBox_stepY_forward (c : Cell) (A B : Point)
    (hdy : 0 < B.y - A.y)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : c.y + 1 ≤ (floorPoint B).y) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorA : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
  have h_min : min (floorPoint A).y (floorPoint B).y = (floorPoint A).y := min_eq_left h_floorA
  have h_max : max (floorPoint A).y (floorPoint B).y = (floorPoint B).y := max_eq_right h_floorA
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h1, h2⟩, by omega⟩, h_next⟩


theorem inBoundingBox_stepY_backward (c : Cell) (A B : Point)
    (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorB : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
  have h_min : min (floorPoint A).y (floorPoint B).y = (floorPoint B).y := min_eq_right h_floorB
  have h_max : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_floorB
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h1, h2⟩, h_next⟩, by omega⟩


theorem stepX_interval_lt_neg (tx1 ty0 ty1 dx : Rat) (dx_neg : dx < 0)
    (h_cross : tx1 < ty1)
    (h_lim : tx1 < 1)
    (h_pos : 0 ≤ tx1)
    (h_ty0 : ty0 ≤ tx1) :
    max 0 (max tx1 ty0) < min 1 (min (tx1 - 1 / dx) ty1) := by
  have h_enter : max 0 (max tx1 ty0) = tx1 := by
    rw [max_eq_left h_ty0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : tx1 < 1 := h_lim
  have h2 : tx1 < tx1 - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : tx1 < ty1 := h_cross
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem stepY_interval_lt_neg (ty1 tx0 tx1 dy : Rat) (dy_neg : dy < 0)
    (h_cross : ty1 < tx1)
    (h_lim : ty1 < 1)
    (h_pos : 0 ≤ ty1)
    (h_tx0 : tx0 ≤ ty1) :
    max 0 (max tx0 ty1) < min 1 (min tx1 (ty1 - 1 / dy)) := by
  have h_enter : max 0 (max tx0 ty1) = ty1 := by
    rw [max_eq_right h_tx0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : ty1 < 1 := h_lim
  have h2 : ty1 < tx1 := h_cross
  have h3 : ty1 < ty1 - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


/- =========================================================================
   Quadrant 1: dx > 0, dy > 0
   ========================================================================= -/

theorem inBoundingBox_diag (c : Cell) (A B : Point) (stepX stepY : Int)
    (hX : inBoundingBox ⟨c.x + stepX, c.y⟩ A B = true)
    (hY : inBoundingBox ⟨c.x, c.y + stepY⟩ A B = true) :
    inBoundingBox ⟨c.x + stepX, c.y + stepY⟩ A B = true := by
  unfold inBoundingBox at hX hY ⊢
  dsimp only [] at hX hY ⊢
  simp only [Bool.and_eq_true] at hX hY ⊢
  exact ⟨⟨⟨hX.1.1.1, hX.1.1.2⟩, hY.1.2⟩, hY.2⟩


theorem interval_dx_pos_dup (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdx : 0 < B.x - A.x) :
    (ofInt c.x - A.x) / (B.x - A.x) ≤ tEnter ∧
    tExit ≤ (ofInt (c.x + 1) - A.x) / (B.x - A.x) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.x - A.x) == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_ne, hdx, ↓reduceIte] at h
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


theorem interval_dy_pos_dup (c : Cell) (A B : Point) (tEnter tExit : Rat)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (hdy : 0 < B.y - A.y) :
    (ofInt c.y - A.y) / (B.y - A.y) ≤ tEnter ∧
    tExit ≤ (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
  unfold cellIntersectionInterval at h
  dsimp only [] at h
  have h_ne : ((B.y - A.y) == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_ne, hdy, ↓reduceIte] at h
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


theorem cellIntersectionInterval_stepX_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty0 := (ofInt c.y - A.y) / dy
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 + 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : Int) : Rat) = ((c.x + 1 : Int) : Rat) + 1
    push_cast
    ring
  rw [h_cx1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = tx1 + 1 / dx := by
    dsimp [tx1, dx]
    ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt c.x - A.x) / dx
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 + 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt
    change ((c.y + 1 + 1 : Int) : Rat) = ((c.y + 1 : Int) : Rat) + 1
    push_cast
    ring
  rw [h_cy1]
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = ty1 + 1 / dy := by
    dsimp [ty1, dy]
    ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_pos (A B : Point) (c : Cell) (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt (c.x + 1) - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t + 1 / dx) (t + 1 / dy))
    t = (ofInt (c.y + 1) - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : Int) : Rat) = ((c.x + 1 : Int) : Rat) + 1
    push_cast
    ring
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt
    change ((c.y + 1 + 1 : Int) : Rat) = ((c.y + 1 : Int) : Rat) + 1
    push_cast
    ring
  rw [h_cx1, h_cy1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = t + 1 / dx := by
    dsimp [t, dx]
    ring
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = t + 1 / dy := by
    have h_split : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) =
        (ofInt (c.y + 1) - A.y) / (B.y - A.y) + 1 / (B.y - A.y) := by ring
    rw [h_split]
    dsimp [dy]
    rw [← h_eq]
  rw [h_divx, h_divy]
  have h_ty : (ofInt (c.y + 1) - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq
    exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal
      dsimp only []
      simp only [show (1 : Int) > 0 by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with _ hy
        omega


theorem extract_stepY_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x, c.y + 1⟩, false)) :
    remY_val A 1 c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step
      injection h_step with h_cell _
      injection h_cell with hx _
      omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal
        dsimp only []
        simp only [show (1 : Int) > 0 by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega


theorem extract_stepDiag_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y + 1⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step
      injection h_step with h_cell _
      injection h_cell with _ hy
      omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega
      · unfold remX_val remY_val absVal
        dsimp only []
        simp only [show (1 : Int) > 0 by decide, ↓reduceIte]
        simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at hxy hyx hlim
        have h_eq : ((if ofInt (c.x + 1) ≥ A.x then ofInt (c.x + 1) - A.x else A.x - ofInt (c.x + 1)) *
              if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) =
            ((if ofInt (c.y + 1) ≥ A.y then ofInt (c.y + 1) - A.y else A.y - ofInt (c.y + 1)) *
              if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) := le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)
        refine ⟨h_eq, not_le.mp hlim⟩


theorem rayMarchStep_X_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal
    simp [le_of_lt hdy, hdy]
  have h_bnd := stepX_bounded (remX_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A 1 c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd
  simp [le_of_lt hdx] at h_bnd
  unfold remX_val at h_bnd
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_ge, ↓reduceIte] at h_bnd
  have h_le := stepX_next_le_end c.x A.x B.x h_bnd
  have h_bbox_next := inBoundingBox_stepX_forward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  rcases hc_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
  have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
  have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
  unfold remY_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, h_ge] at h_step
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_cross : tx1 < ty1 := by
    dsimp [tx1, ty1]
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.x + 1) - A.x) (ofInt (c.y + 1) - A.y) (B.x - A.x) (B.y - A.y) hdx hdy).mp h_step
  have h_lim : tx1 < 1 := by
    dsimp [tx1]
    exact (div_lt_one hdx).mpr h_bnd
  have h_pos' : 0 ≤ tx1 := by
    dsimp [tx1]
    exact div_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0 : ty0 ≤ tx1 := by
    dsimp [tx1, ty0]
    linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos' h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 + 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A 1 c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal
    simp [le_of_lt hdx, hdx]
  have h_bnd := stepY_bounded (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A 1 c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd
  simp [le_of_lt hdy] at h_bnd
  unfold remY_val at h_bnd
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_remY_ge, ↓reduceIte] at h_bnd
  have h_le := stepY_next_le_end c.y A.y B.y h_bnd
  have h_bbox_next := inBoundingBox_stepY_forward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  rcases hc_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
  have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
  have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
  unfold remY_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, h_ge] at h_step
  let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_cross : ty1 < tx1 := by
    dsimp [tx1, ty1]
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.y + 1) - A.y) (ofInt (c.x + 1) - A.x) (B.y - A.y) (B.x - A.x) hdy hdx).mp h_step
  have h_lim : ty1 < 1 := by
    dsimp [ty1]
    exact (div_lt_one hdy).mpr h_bnd
  have h_pos' : 0 ≤ ty1 := by
    dsimp [ty1]
    exact div_nonneg (by linarith) (le_of_lt hdy)
  have h_tx0 : tx0 ≤ ty1 := by
    dsimp [tx0, ty1]
    linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos' h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal
    simp [le_of_lt hdx, hdx]
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal
    simp [le_of_lt hdy, hdy]
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A 1 c) (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [le_of_lt hdx] at h_bndX
  simp [le_of_lt hdy] at h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bndX h_bndY
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_ge, ↓reduceIte] at h_bndX
  simp only [h_remY_ge, ↓reduceIte] at h_bndY
  have h_leX := stepX_next_le_end c.x A.x B.x h_bndX
  have h_leY := stepY_next_le_end c.y A.y B.y h_bndY
  have h_bboxX := inBoundingBox_stepX_forward c A B hdx hc_bbox h_leX
  have h_bboxY := inBoundingBox_stepY_forward c A B hdy hc_bbox h_leY
  have h_bbox_next := inBoundingBox_diag c A B 1 1 h_bboxX h_bboxY
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_ge, h_remY_ge] at h_step
  let t := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  have h_cross : t = (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
    dsimp [t]
    exact (cross_eq_cross_iff_div_eq_div (ofInt (c.x + 1) - A.x) (ofInt (c.y + 1) - A.y) (B.x - A.x) (B.y - A.y) hdx hdy).mp h_step
  have h_lim : t < 1 := by
    dsimp [t]
    exact (div_lt_one hdx).mpr h_bndX
  have h_pos : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (by linarith) (le_of_lt hdx)
  have h_lt := stepDiag_interval_lt t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t + 1 / (B.x - A.x)) (t + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_pos A B c hdx hdy h_cross h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem cellIntersectionInterval_startCell_pos_pos (A B : Point)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    ∃ tEnter tExit, cellIntersectionInterval (floorPoint A) A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, Bool.false_eq_true, ↓reduceIte]
  have h_flA : ((floorPoint A).x : Rat) ≤ A.x := by
    unfold floorPoint toInt; dsimp
    exact Rat.floor_le A.x
  have h_flAy : ((floorPoint A).y : Rat) ≤ A.y := by
    unfold floorPoint toInt; dsimp
    exact Rat.floor_le A.y
  have h_ltX : A.x < ((floorPoint A).x : Rat) + 1 := by
    unfold floorPoint toInt; dsimp
    have := Rat.lt_floor_add_one A.x
    push_cast at this
    exact this
  have h_ltY : A.y < ((floorPoint A).y : Rat) + 1 := by
    unfold floorPoint toInt; dsimp
    have := Rat.lt_floor_add_one A.y
    push_cast at this
    exact this
  have h_ofIntX0 : ofInt (floorPoint A).x = ((floorPoint A).x : Rat) := rfl
  have h_ofIntX1 : ofInt ((floorPoint A).x + 1) = ((floorPoint A).x : Rat) + 1 := by
    unfold ofInt; change (((floorPoint A).x + 1 : Int) : Rat) = ((floorPoint A).x : Rat) + 1; push_cast; ring
  have h_ofIntY0 : ofInt (floorPoint A).y = ((floorPoint A).y : Rat) := rfl
  have h_ofIntY1 : ofInt ((floorPoint A).y + 1) = ((floorPoint A).y : Rat) + 1 := by
    unfold ofInt; change (((floorPoint A).y + 1 : Int) : Rat) = ((floorPoint A).y : Rat) + 1; push_cast; ring
  rw [h_ofIntX0, h_ofIntX1, h_ofIntY0, h_ofIntY1]
  let tx0 := (((floorPoint A).x : Rat) - A.x) / (B.x - A.x)
  let tx1 := (((floorPoint A).x : Rat) + 1 - A.x) / (B.x - A.x)
  let ty0 := (((floorPoint A).y : Rat) - A.y) / (B.y - A.y)
  let ty1 := (((floorPoint A).y : Rat) + 1 - A.y) / (B.y - A.y)
  have h_tx0_nonpos : tx0 ≤ 0 := by
    dsimp [tx0]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0_nonpos : ty0 ≤ 0 := by
    dsimp [ty0]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdy)
  have h_tx1_pos : 0 < tx1 := by
    dsimp [tx1]
    exact div_pos (by linarith) hdx
  have h_ty1_pos : 0 < ty1 := by
    dsimp [ty1]
    exact div_pos (by linarith) hdy
  have h_enter : max 0 (max tx0 ty0) = 0 := by
    have : max tx0 ty0 ≤ 0 := max_le h_tx0_nonpos h_ty0_nonpos
    exact max_eq_left this
  have h_exit_pos : 0 < min 1 (min tx1 ty1) := by
    rw [lt_min_iff]
    refine ⟨by linarith, ?_⟩
    rw [lt_min_iff]
    exact ⟨h_tx1_pos, h_ty1_pos⟩
  have h_le : max 0 (max tx0 ty0) ≤ min 1 (min tx1 ty1) := by
    rw [h_enter]
    exact le_of_lt h_exit_pos
  change ∃ tEnter tExit, (if max 0 (max tx0 ty0) ≤ min 1 (min tx1 ty1) then some (max 0 (max tx0 ty0), min 1 (min tx1 ty1)) else none) = some (tEnter, tExit) ∧ tEnter < tExit
  simp only [h_le, ↓reduceIte]
  refine ⟨max 0 (max tx0 ty0), min 1 (min tx1 ty1), rfl, ?_⟩
  rw [h_enter]
  exact h_exit_pos


theorem rayMarchStep_sound_step_pos_pos (A B : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos : 0 < dx ∧ 0 < dy)
    (hc : inBoundingBox c A B = true ∧ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = 1 := by rw [hstepX]; simp [h_pos.1]
  have hsy : stepY = 1 := by rw [hstepY]; simp [h_pos.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done
    contradiction
  · rw [h2]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim
  · rw [h3]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim
  · rw [h4]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim


theorem rayMarchStep_sound_base_pos_pos (A B : Point) (dx dy : Rat) (stepX stepY : Int)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos : 0 < dx ∧ 0 < dy)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY (floorPoint A)).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_bbox := inBoundingBox_startCell A B
  have h_inter := cellIntersectionInterval_startCell_pos_pos A B (by linarith) (by linarith)
  exact rayMarchStep_sound_step_pos_pos A B dx dy stepX stepY (floorPoint A) hdx hdy hstepX hstepY h_pos ⟨h_bbox, h_inter⟩ h_not_done



theorem rayMarch_soundness_pos_pos (A B : Point) (x : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = 1 := by simp [hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = 1 := by simp [hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    have h_res := rayMarchStep_sound_step_pos_pos A B (B.x - A.x) (B.y - A.y) 1 1 c rfl rfl (by simp [hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ hc h_not_done
    exact h_res
  · intro h_not_done
    have h_res := rayMarchStep_sound_base_pos_pos A B (B.x - A.x) (B.y - A.y) 1 1 rfl rfl (by simp [hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ h_not_done
    exact h_res


/- =========================================================================
   Quadrant 2: dx > 0, dy < 0
   ========================================================================= -/

theorem inBoundingBox_diag_pos_neg (c : Cell) (A B : Point)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : c.x + 1 ≤ (floorPoint B).x)
    (h_next_y : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x + 1, c.y - 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_forward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_backward ⟨c.x + 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_pos_neg (t dx dy : Rat) (dx_pos : 0 < dx) (dy_neg : dy < 0)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t + 1 / dx) (t - 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t + 1 / dx := by
    have : 0 < 1 / dx := one_div_pos.mpr dx_pos
    linarith
  have h3 : t < t - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty0 := (ofInt (c.y + 1) - A.y) / dy
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 + 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : Int) : Rat) = ((c.x + 1 : Int) : Rat) + 1
    push_cast
    ring
  rw [h_cx1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = tx1 + 1 / dx := by
    dsimp [tx1, dx]
    ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt c.x - A.x) / dx
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 - 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt
    congr 1
    omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt
    change ((c.y - 1 : Int) : Rat) = ((c.y : Int) : Rat) - 1
    push_cast
    ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 - 1 / dy := by
    dsimp [ty1, dy]
    ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt (c.x + 1) - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t + 1 / dx) (t - 1 / dy))
    t = (ofInt c.y - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : Int) : Rat) = ((c.x + 1 : Int) : Rat) + 1
    push_cast
    ring
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt
    congr 1
    omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt
    change ((c.y - 1 : Int) : Rat) = ((c.y : Int) : Rat) - 1
    push_cast
    ring
  rw [h_cx1, h_cy1, h_cy0]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = t + 1 / dx := by
    dsimp [t, dx]
    ring
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = t - 1 / dy := by
    have h_split : (ofInt c.y - 1 - A.y) / (B.y - A.y) =
        (ofInt c.y - A.y) / (B.y - A.y) - 1 / (B.y - A.y) := by ring
    rw [h_split]
    dsimp [dy]
    rw [← h_eq]
  rw [h_divx, h_divy]
  have h_ty : (ofInt c.y - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq
    exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show (1 : Int) > 0 by decide, show ¬((-1 : Int) > 0) by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega


theorem extract_stepY_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x, c.y - 1⟩, false)) :
    remY_val A (-1) c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show (1 : Int) > 0 by decide, show ¬((-1 : Int) > 0) by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepDiag_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y - 1⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show (1 : Int) > 0 by decide, show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A (-1) c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [le_of_lt hdx] at h_bnd
  unfold remX_val at h_bnd; simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  simp only [h_ge, ↓reduceIte] at h_bnd
  have h_le := stepX_next_le_end c.x A.x B.x h_bnd
  have h_bbox_next := inBoundingBox_stepX_forward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte, show ¬(B.y - A.y ≥ 0) by linarith, le_of_lt hdx] at h_step
  unfold remX_val at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, h_ge] at h_step
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_step
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    dsimp [tx1]
    rw [← h_ty1_eq]
    have h_pos_neg_dy : 0 < -(B.y - A.y) := by linarith
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.x + 1) - A.x) (A.y - ofInt c.y) (B.x - A.x) (-(B.y - A.y)) hdx h_pos_neg_dy).mp h_step
  have h_lim : tx1 < 1 := (div_lt_one hdx).mpr h_bnd
  have h_pos_val : 0 ≤ tx1 := div_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt ((floorPoint A).y + 1) - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
        have h_num : 0 < ofInt (A.y.floor + 1) - A.y := by
          unfold ofInt; change 0 < ((A.y.floor + 1 : Int) : Rat) - A.y; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 + 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_pos_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A (-1) c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A 1 c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.y - A.y ≥ 0) by linarith] at h_bnd
  unfold remY_val at h_bnd; simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_bnd
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bnd]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_stepY_backward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith, h_ge] at h_step
  unfold remY_val at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remY_split] at h_step
  let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    dsimp [tx1]; rw [← h_ty1_eq]
    have h_pos_neg_dy : 0 < -(B.y - A.y) := by linarith
    exact (cross_lt_cross_iff_div_lt_div (A.y - ofInt c.y) (ofInt (c.x + 1) - A.x) (-(B.y - A.y)) (B.x - A.x) h_pos_neg_dy hdx).mp h_step
  have h_lim : ty1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ ty1 := by rw [← h_ty1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt (floorPoint A).x - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt ofInt; dsimp
        have h_le := Rat.floor_le A.x
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt_neg ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_pos_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A 1 c) (remY_val A (-1) c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bndX
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA; have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : Int) : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : Rat) + 1 := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) = (c.x : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy; have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  simp only [h_ge, ↓reduceIte] at h_bndX
  rw [h_remY_split] at h_bndY
  have h_le_x := stepX_next_le_end c.x A.x B.x h_bndX
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bndY]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_y := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_diag_pos_neg c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, show ¬((-1 : Int) > 0) by decide, ↓reduceIte,
    le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith, h_ge] at h_step
  rw [h_remY_split] at h_step
  let t := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt c.y - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (ofInt (c.x + 1) - A.x) (A.y - ofInt c.y) (B.x - A.x) (-(B.y - A.y)) hdx (by linarith)).mp h_step
    rw [h_cross]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_lim : t < 1 := (div_lt_one hdx).mpr h_bndX
  have h_pos : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hdx)
  have h_lt := stepDiag_interval_lt_pos_neg t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t + 1 / (B.x - A.x)) (t - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_pos_neg A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_pos_neg (A B : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos_neg : 0 < dx ∧ dy < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = 1 := by rw [hstepX]; simp [h_pos_neg.1]
  have hsy : stepY = -1 := by rw [hstepY]; simp [show ¬(dy > 0) by linarith [h_pos_neg.2], h_pos_neg.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_pos_neg (A B : Point) (x : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = 1 := by simp [hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = -1 := by
    simp [show ¬(B.y - A.y > 0) by linarith, hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_pos_neg A B (B.x - A.x) (B.y - A.y) 1 (-1) c rfl rfl (by simp [hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_pos_neg A B (B.x - A.x) (B.y - A.y) 1 (-1) (floorPoint A) rfl rfl (by simp [hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Quadrant 3: dx < 0, dy > 0
   ========================================================================= -/

theorem inBoundingBox_diag_neg_pos (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : (floorPoint B).x ≤ c.x - 1)
    (h_next_y : c.y + 1 ≤ (floorPoint B).y) :
    inBoundingBox ⟨c.x - 1, c.y + 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_backward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_forward ⟨c.x - 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_neg_pos (t dx dy : Rat) (dx_neg : dx < 0) (dy_pos : 0 < dy)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t - 1 / dx) (t + 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : t < t + 1 / dy := by
    have : 0 < 1 / dy := one_div_pos.mpr dy_pos
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt c.x - A.x) / dx
    let ty0 := (ofInt c.y - A.y) / dy
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 - 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : Int) : Rat) = ((c.x : Int) : Rat) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 - 1 / dx := by
    dsimp [tx1, dx]; ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt (c.x + 1) - A.x) / dx
    let tx1 := (ofInt c.x - A.x) / dx
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 + 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt; change ((c.y + 1 + 1 : Int) : Rat) = ((c.y + 1 : Int) : Rat) + 1; push_cast; ring
  rw [h_cy1]
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = ty1 + 1 / dy := by
    dsimp [ty1, dy]; ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt c.x - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t - 1 / dx) (t + 1 / dy))
    t = (ofInt (c.y + 1) - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : Int) : Rat) = ((c.x : Int) : Rat) - 1; push_cast; ring
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt; change ((c.y + 1 + 1 : Int) : Rat) = ((c.y + 1 : Int) : Rat) + 1; push_cast; ring
  rw [h_cx1, h_cx0, h_cy1]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = t - 1 / dx := by
    dsimp [t, dx]; ring
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = t + 1 / dy := by
    rw [h_eq]; dsimp [dy]; ring
  rw [h_divx, h_divy]
  have h_ty : (ofInt (c.y + 1) - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq; exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show ¬((-1 : Int) > 0) by decide, show (1 : Int) > 0 by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepY_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x, c.y + 1⟩, false)) :
    remY_val A 1 c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : Int) > 0) by decide, show (1 : Int) > 0 by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega


theorem extract_stepDiag_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y + 1⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : Int) > 0) by decide, show (1 : Int) > 0 by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A 1 c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.x - A.x ≥ 0) by linarith] at h_bnd
  unfold remX_val at h_bnd; simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bnd
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bnd]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_bbox_next := inBoundingBox_stepX_backward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remX_split] at h_step
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.x - ofInt c.x) (ofInt (c.y + 1) - A.y) (-(B.x - A.x)) (B.y - A.y) (by linarith) hdy).mp h_step
    rw [h_tx1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : tx1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ tx1 := by rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt (floorPoint A).y - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt ofInt; dsimp
        have h_le := Rat.floor_le A.y
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt_neg tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 - 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_neg_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A 1 c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A (-1) c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [le_of_lt hdy] at h_bnd
  unfold remY_val at h_bnd; simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  simp only [h_remY_ge, ↓reduceIte] at h_bnd
  have h_le := stepY_next_le_end c.y A.y B.y h_bnd
  have h_bbox_next := inBoundingBox_stepY_forward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte, le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  unfold remY_val at h_step
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte, h_remY_ge] at h_step
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_step
  let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (ofInt (c.y + 1) - A.y) (A.x - ofInt c.x) (B.y - A.y) (-(B.x - A.x)) hdy (by linarith)).mp h_step
    rw [h_tx1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : ty1 < 1 := (div_lt_one hdy).mpr h_bnd
  have h_pos_val : 0 ≤ ty1 := div_nonneg (by linarith) (le_of_lt hdy)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt ((floorPoint A).x + 1) - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
        have h_num : 0 < ofInt (A.x.floor + 1) - A.x := by
          unfold ofInt; change 0 < ((A.x.floor + 1 : Int) : Rat) - A.x; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_neg_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A (-1) c) (remY_val A 1 c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [show ¬(B.x - A.x ≥ 0) by linarith, le_of_lt hdy] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bndX
  simp only [show (1 : Int) > 0 by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : Int) : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : Rat) + 1 := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) = (c.y : Rat) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bndX
  simp only [h_remY_ge, ↓reduceIte] at h_bndY
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bndX]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_x := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_le_y := stepY_next_le_end c.y A.y B.y h_bndY
  have h_bbox_next := inBoundingBox_diag_neg_pos c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, show (1 : Int) > 0 by decide, ↓reduceIte,
    le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith, h_remY_ge] at h_step
  rw [h_remX_split] at h_step
  let t := (ofInt c.x - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (A.x - ofInt c.x) (ofInt (c.y + 1) - A.y) (-(B.x - A.x)) (B.y - A.y) (by linarith) hdy).mp h_step
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [← h_cross, h_num, neg_div_neg_eq]
  have h_lim : t < 1 := h_div_bnd
  have h_pos : 0 ≤ t := by
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = t := by dsimp [t]; rw [h_num, neg_div_neg_eq]
    rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_lt := stepDiag_interval_lt_neg_pos t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t - 1 / (B.x - A.x)) (t + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_neg_pos A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_neg_pos (A B : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_neg_pos : dx < 0 ∧ 0 < dy)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = -1 := by rw [hstepX]; simp [show ¬(dx > 0) by linarith [h_neg_pos.1], h_neg_pos.1]
  have hsy : stepY = 1 := by rw [hstepY]; simp [h_neg_pos.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_neg_pos (A B : Point) (x : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = -1 := by
    simp [show ¬(B.x - A.x > 0) by linarith, hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = 1 := by simp [hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_neg_pos A B (B.x - A.x) (B.y - A.y) (-1) 1 c rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_neg_pos A B (B.x - A.x) (B.y - A.y) (-1) 1 (floorPoint A) rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Quadrant 4: dx < 0, dy < 0
   ========================================================================= -/

theorem inBoundingBox_diag_neg_neg (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : (floorPoint B).x ≤ c.x - 1)
    (h_next_y : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x - 1, c.y - 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_backward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_backward ⟨c.x - 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_neg_neg (t dx dy : Rat) (dx_neg : dx < 0) (dy_neg : dy < 0)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t - 1 / dx) (t - 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : t < t - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt c.x - A.x) / dx
    let ty0 := (ofInt (c.y + 1) - A.y) / dy
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 - 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : Int) : Rat) = ((c.x : Int) : Rat) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 - 1 / dx := by
    dsimp [tx1, dx]; ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt (c.x + 1) - A.x) / dx
    let tx1 := (ofInt c.x - A.x) / dx
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 - 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : Int) : Rat) = ((c.y : Int) : Rat) - 1; push_cast; ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 - 1 / dy := by
    dsimp [ty1, dy]; ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt c.x - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t - 1 / dx) (t - 1 / dy))
    t = (ofInt c.y - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : Int) : Rat) = ((c.x : Int) : Rat) - 1; push_cast; ring
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : Int) : Rat) = ((c.y : Int) : Rat) - 1; push_cast; ring
  rw [h_cx1, h_cx0, h_cy1, h_cy0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = t - 1 / dx := by
    dsimp [t, dx]; ring
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = t - 1 / dy := by
    rw [h_eq]; dsimp [dy]; ring
  rw [h_divx, h_divy]
  have h_ty : (ofInt c.y - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq; exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepY_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x, c.y - 1⟩, false)) :
    remY_val A (-1) c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepDiag_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y - 1⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A (-1) c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.x - A.x ≥ 0) by linarith] at h_bnd
  unfold remX_val at h_bnd; simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bnd
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bnd]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_bbox_next := inBoundingBox_stepX_backward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte, show ¬(B.y - A.y ≥ 0) by linarith, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  unfold remX_val at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remX_split] at h_step
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_step
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]; have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.x - ofInt c.x) (A.y - ofInt c.y) (-(B.x - A.x)) (-(B.y - A.y)) (by linarith) (by linarith)).mp h_step
    rw [h_tx1_eq, h_ty1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : tx1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ tx1 := by rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt ((floorPoint A).y + 1) - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
        have h_num : 0 < ofInt (A.y.floor + 1) - A.y := by
          unfold ofInt; change 0 < ((A.y.floor + 1 : Int) : Rat) - A.y; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt_neg tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 - 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_neg_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A (-1) c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A (-1) c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.y - A.y ≥ 0) by linarith] at h_bnd
  unfold remY_val at h_bnd; simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_bnd
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bnd]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_stepY_backward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte, show ¬(B.x - A.x ≥ 0) by linarith, show ¬(B.y - A.y ≥ 0) by linarith] at h_step
  unfold remY_val at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remY_split] at h_step
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_step
  let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]; have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.y - ofInt c.y) (A.x - ofInt c.x) (-(B.y - A.y)) (-(B.x - A.x)) (by linarith) (by linarith)).mp h_step
    rw [h_tx1_eq, h_ty1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : ty1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ ty1 := by rw [← h_ty1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt ((floorPoint A).x + 1) - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
        have h_num : 0 < ofInt (A.x.floor + 1) - A.x := by
          unfold ofInt; change 0 < ((A.x.floor + 1 : Int) : Rat) - A.x; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt_neg ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_neg_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A (-1) c) (remY_val A (-1) c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [show ¬(B.x - A.x ≥ 0) by linarith, show ¬(B.y - A.y ≥ 0) by linarith] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bndX
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : Rat) ≤ ((A.x.floor : Int) : Rat) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : Rat) ≤ ((A.y.floor : Int) : Rat) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : Rat) := rfl
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bndX
  rw [h_remY_split] at h_bndY
  have h_div_bndX : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bndX]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_div_bndY : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bndY]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_x := stepX_neg_next_ge_end c.x A.x B hdx h_div_bndX
  have h_le_y := stepY_neg_next_ge_end c.y A.y B hdy h_div_bndY
  have h_bbox_next := inBoundingBox_diag_neg_neg c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show ¬((-1 : Int) > 0) by decide, ↓reduceIte,
    show ¬(B.y - A.y ≥ 0) by linarith, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  rw [h_remX_split, h_remY_split] at h_step
  let t := (ofInt c.x - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt c.y - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (A.x - ofInt c.x) (A.y - ofInt c.y) (-(B.x - A.x)) (-(B.y - A.y)) (by linarith) (by linarith)).mp h_step
    have h_numX : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_numY : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    have h_LHS : (A.x - ofInt c.x) / -(B.x - A.x) = (ofInt c.x - A.x) / (B.x - A.x) := by rw [h_numX, neg_div_neg_eq]
    have h_RHS : (A.y - ofInt c.y) / -(B.y - A.y) = (ofInt c.y - A.y) / (B.y - A.y) := by rw [h_numY, neg_div_neg_eq]
    rw [h_LHS, h_RHS] at h_cross
    exact h_cross
  have h_lim : t < 1 := h_div_bndX
  have h_pos : 0 ≤ t := by
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = t := by dsimp [t]; rw [h_num, neg_div_neg_eq]
    rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_lt := stepDiag_interval_lt_neg_neg t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t - 1 / (B.x - A.x)) (t - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_neg_neg A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_neg_neg (A B : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_neg_neg : dx < 0 ∧ dy < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = -1 := by rw [hstepX]; simp [show ¬(dx > 0) by linarith [h_neg_neg.1], h_neg_neg.1]
  have hsy : stepY = -1 := by rw [hstepY]; simp [show ¬(dy > 0) by linarith [h_neg_neg.2], h_neg_neg.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_neg_neg (A B : Point) (x : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = -1 := by
    simp [show ¬(B.x - A.x > 0) by linarith, hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = -1 := by
    simp [show ¬(B.y - A.y > 0) by linarith, hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_neg_neg A B (B.x - A.x) (B.y - A.y) (-1) (-1) c rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_neg_neg A B (B.x - A.x) (B.y - A.y) (-1) (-1) (floorPoint A) rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Axis-parallel: dx = 0 or dy = 0
   ========================================================================= -/

theorem cellIntersectionInterval_sx_zero_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x = 0) (hdy : 0 < B.y - A.y)
    (hcx : c.x = (floorPoint A).x)
    (hcy : (floorPoint A).y ≤ c.y)
    (h_bnd : ofInt (c.y + 1) - A.y < B.y - A.y) :
    let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
    let ty1 := (ofInt (c.y + 1 + 1) - A.y) / (B.y - A.y)
    let tEnter := max 0 ty0
    let tExit := min 1 ty1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro ty0 ty1 tEnter tExit
  have h_dx_eq : (B.x - A.x == 0) = true := beq_iff_eq.mpr hdx
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_x : ofInt (floorPoint A).x ≤ A.x := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
  have h_flA_x_lt : A.x < ofInt ((floorPoint A).x + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
  have hcx_le : ofInt c.x ≤ A.x := by rw [hcx]; exact h_flA_x
  have hcx_lt : A.x < ofInt (c.x + 1) := by rw [hcx]; exact h_flA_x_lt
  have h_pos : 0 < ofInt (c.y + 1) - A.y := by
    have h_flAy : A.y < ofInt ((floorPoint A).y + 1) := by
      unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
    have h_int_le : (floorPoint A).y + 1 ≤ c.y + 1 := by omega
    have h_le_cy : ofInt ((floorPoint A).y + 1) ≤ ofInt (c.y + 1) := by
      unfold ofInt; exact Int.cast_le.mpr h_int_le
    linarith
  have h_ty0_pos : 0 < ty0 := div_pos h_pos hdy
  have h_enter : tEnter = ty0 := max_eq_right (le_of_lt h_ty0_pos)
  have h1 : ty0 < 1 := (div_lt_one hdy).mpr h_bnd
  have h2 : ty0 < ty1 := by
    dsimp [ty0, ty1]
    have h_lt_num : ofInt (c.y + 1) - A.y < ofInt (c.y + 1 + 1) - A.y := by
      unfold ofInt; change ((c.y + 1 : Int) : Rat) - A.y < ((c.y + 1 + 1 : Int) : Rat) - A.y
      push_cast; linarith
    exact div_lt_div_of_pos_right h_lt_num hdy
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  simp only [h_dx_eq, h_dy_ne, hdy, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cx : ¬(A.x < ofInt c.x) := by linarith
  have h_not_gt_cx1 : ¬(A.x > ofInt (c.x + 1)) := by linarith
  have h_cx_eval : (if (A.x < ofInt c.x || A.x > ofInt (c.x + 1)) then (1, 0) else (0, 1) : Rat × Rat) = (0, 1) := by
    simp [h_not_lt_cx, h_not_gt_cx1]
  rw [h_cx_eval]
  dsimp only []
  rw [← max_assoc, max_self, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sx_zero_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x = 0) (hdy : B.y - A.y < 0)
    (hcx : c.x = (floorPoint A).x)
    (hcy : c.y ≤ (floorPoint A).y)
    (h_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1) :
    let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
    let ty1 := ty0 - 1 / (B.y - A.y)
    let tEnter := max 0 ty0
    let tExit := min 1 ty1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro ty0 ty1 tEnter tExit
  have h_dx_eq : (B.x - A.x == 0) = true := beq_iff_eq.mpr hdx
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_x : ofInt (floorPoint A).x ≤ A.x := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
  have h_flA_x_lt : A.x < ofInt ((floorPoint A).x + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
  have hcx_le : ofInt c.x ≤ A.x := by rw [hcx]; exact h_flA_x
  have hcx_lt : A.x < ofInt (c.x + 1) := by rw [hcx]; exact h_flA_x_lt
  have h_nonpos : ofInt c.y - A.y ≤ 0 := by
    have h_flAy : ofInt (floorPoint A).y ≤ A.y := by
      unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
    have h_cy_le : ofInt c.y ≤ ofInt (floorPoint A).y := by
      unfold ofInt; exact Int.cast_le.mpr hcy
    linarith
  have h_num : ofInt c.y - A.y = -(A.y - ofInt c.y) := by ring
  have h_den : B.y - A.y = -(A.y - B.y) := by ring
  have h_ty0_eq : ty0 = (A.y - ofInt c.y) / (A.y - B.y) := by
    dsimp [ty0]; rw [h_num, h_den, neg_div_neg_eq]
  have h_ty0_pos : 0 ≤ ty0 := by
    rw [h_ty0_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_enter : tEnter = ty0 := max_eq_right h_ty0_pos
  have h1 : ty0 < 1 := h_bnd
  have h2 : ty0 < ty1 := by
    dsimp [ty1]
    have : 0 < -(B.y - A.y) := by linarith
    have h := one_div_pos.mpr this
    rw [div_neg] at h
    linarith
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_eq, h_dy_ne, h_not_dy_pos, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cx : ¬(A.x < ofInt c.x) := by linarith
  have h_not_gt_cx1 : ¬(A.x > ofInt (c.x + 1)) := by linarith
  have h_cx_eval : (if (A.x < ofInt c.x || A.x > ofInt (c.x + 1)) then (1, 0) else (0, 1) : Rat × Rat) = (0, 1) := by
    simp [h_not_lt_cx, h_not_gt_cx1]
  rw [h_cx_eval]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : Int) : Rat) = ((c.y : Int) : Rat) - 1; push_cast; ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 := by
    dsimp [ty1, ty0]; ring
  rw [h_divy]
  dsimp only []
  rw [← max_assoc, max_self, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sy_zero_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y = 0)
    (hcy : c.y = (floorPoint A).y)
    (hcx : (floorPoint A).x ≤ c.x)
    (h_bnd : ofInt (c.x + 1) - A.x < B.x - A.x) :
    let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
    let tx1 := (ofInt (c.x + 1 + 1) - A.x) / (B.x - A.x)
    let tEnter := max 0 tx0
    let tExit := min 1 tx1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro tx0 tx1 tEnter tExit
  have h_dy_eq : (B.y - A.y == 0) = true := beq_iff_eq.mpr hdy
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_y : ofInt (floorPoint A).y ≤ A.y := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
  have h_flA_y_lt : A.y < ofInt ((floorPoint A).y + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
  have hcy_le : ofInt c.y ≤ A.y := by rw [hcy]; exact h_flA_y
  have hcy_lt : A.y < ofInt (c.y + 1) := by rw [hcy]; exact h_flA_y_lt
  have h_pos : 0 < ofInt (c.x + 1) - A.x := by
    have h_flAx : A.x < ofInt ((floorPoint A).x + 1) := by
      unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
    have h_int_le : (floorPoint A).x + 1 ≤ c.x + 1 := by omega
    have h_le_cx : ofInt ((floorPoint A).x + 1) ≤ ofInt (c.x + 1) := by
      unfold ofInt; exact Int.cast_le.mpr h_int_le
    linarith
  have h_tx0_pos : 0 < tx0 := div_pos h_pos hdx
  have h_enter : tEnter = tx0 := max_eq_right (le_of_lt h_tx0_pos)
  have h1 : tx0 < 1 := (div_lt_one hdx).mpr h_bnd
  have h2 : tx0 < tx1 := by
    dsimp [tx0, tx1]
    have h_lt_num : ofInt (c.x + 1) - A.x < ofInt (c.x + 1 + 1) - A.x := by
      unfold ofInt; change ((c.x + 1 : Int) : Rat) - A.x < ((c.x + 1 + 1 : Int) : Rat) - A.x
      push_cast; linarith
    exact div_lt_div_of_pos_right h_lt_num hdx
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  simp only [h_dy_eq, h_dx_ne, hdx, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cy : ¬(A.y < ofInt c.y) := by linarith
  have h_not_gt_cy1 : ¬(A.y > ofInt (c.y + 1)) := by linarith
  have h_cy_eval : (if (A.y < ofInt c.y || A.y > ofInt (c.y + 1)) then (1, 0) else (0, 1) : Rat × Rat) = (0, 1) := by
    simp [h_not_lt_cy, h_not_gt_cy1]
  rw [h_cy_eval]
  dsimp only []
  rw [max_comm tx0 0, ← max_assoc, max_self]
  rw [min_comm tx1 1, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sy_zero_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y = 0)
    (hcy : c.y = (floorPoint A).y)
    (hcx : c.x ≤ (floorPoint A).x)
    (h_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1) :
    let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
    let tx1 := tx0 - 1 / (B.x - A.x)
    let tEnter := max 0 tx0
    let tExit := min 1 tx1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro tx0 tx1 tEnter tExit
  have h_dy_eq : (B.y - A.y == 0) = true := beq_iff_eq.mpr hdy
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_y : ofInt (floorPoint A).y ≤ A.y := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
  have h_flA_y_lt : A.y < ofInt ((floorPoint A).y + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
  have hcy_le : ofInt c.y ≤ A.y := by rw [hcy]; exact h_flA_y
  have hcy_lt : A.y < ofInt (c.y + 1) := by rw [hcy]; exact h_flA_y_lt
  have h_nonpos : ofInt c.x - A.x ≤ 0 := by
    have h_flAx : ofInt (floorPoint A).x ≤ A.x := by
      unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
    have h_cx_le : ofInt c.x ≤ ofInt (floorPoint A).x := by
      unfold ofInt; exact Int.cast_le.mpr hcx
    linarith
  have h_num : ofInt c.x - A.x = -(A.x - ofInt c.x) := by ring
  have h_den : B.x - A.x = -(A.x - B.x) := by ring
  have h_tx0_eq : tx0 = (A.x - ofInt c.x) / (A.x - B.x) := by
    dsimp [tx0]; rw [h_num, h_den, neg_div_neg_eq]
  have h_tx0_pos : 0 ≤ tx0 := by
    rw [h_tx0_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_enter : tEnter = tx0 := max_eq_right h_tx0_pos
  have h1 : tx0 < 1 := h_bnd
  have h2 : tx0 < tx1 := by
    dsimp [tx1]
    have : 0 < -(B.x - A.x) := by linarith
    have h := one_div_pos.mpr this
    rw [div_neg] at h
    linarith
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dy_eq, h_dx_ne, h_not_dx_pos, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cy : ¬(A.y < ofInt c.y) := by linarith
  have h_not_gt_cy1 : ¬(A.y > ofInt (c.y + 1)) := by linarith
  have h_cy_eval : (if (A.y < ofInt c.y || A.y > ofInt (c.y + 1)) then (1, 0) else (0, 1) : Rat × Rat) = (0, 1) := by
    simp [h_not_lt_cy, h_not_gt_cy1]
  rw [h_cy_eval]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : Int) : Rat) = ((c.x : Int) : Rat) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 := by
    dsimp [tx1, tx0]; ring
  rw [h_divx]
  dsimp only []
  rw [max_comm tx0 0, ← max_assoc, max_self]
  rw [min_comm tx1 1, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem rayMarchStep_sx_zero_step (A B : Point) (c : Cell)
    (dy : Rat) (stepY : Int)
    (h_not_done : (rayMarchStep A B 0 dy 0 stepY c).2 = false) :
    let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDy := if dy >= 0 then dy else -dy
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    (rayMarchStep A B 0 dy 0 stepY c) = (⟨c.x, c.y + stepY⟩, false) ∧ remY < absDy := by
  intro yb absDy remY
  have h_step := rayMarchStep_sx_zero A B c dy stepY
  dsimp only [] at h_step
  rw [h_step] at h_not_done ⊢
  by_cases h : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ if dy ≥ 0 then dy else -dy
  · simp only [h, ↓reduceIte] at h_not_done
    contradiction
  · simp only [h, ↓reduceIte]
    exact ⟨trivial, not_le.mp h⟩


theorem rayMarchStep_sy_zero_step (A B : Point) (c : Cell)
    (dx : Rat) (stepX : Int)
    (hsx_ne : (stepX == 0) = false)
    (h_not_done : (rayMarchStep A B dx 0 stepX 0 c).2 = false) :
    let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let absDx := if dx >= 0 then dx else -dx
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    (rayMarchStep A B dx 0 stepX 0 c) = (⟨c.x + stepX, c.y⟩, false) ∧ remX < absDx := by
  intro xb absDx remX
  have h_step := rayMarchStep_sy_zero A B c dx stepX hsx_ne
  dsimp only [] at h_step
  rw [h_step] at h_not_done ⊢
  by_cases h : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ if dx >= 0 then dx else -dx
  · simp only [h, ↓reduceIte] at h_not_done
    contradiction
  · simp only [h, ↓reduceIte]
    exact ⟨trivial, not_le.mp h⟩


theorem rayMarchStep_sound_step_sx_zero (A B : Point) (stepY : Int) (c : Cell)
    (hdx : B.x - A.x = 0)
    (hstepY : stepY = if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_x : c.x = (floorPoint A).x)
    (hc_y : (0 < B.y - A.y ∧ (floorPoint A).y ≤ c.y) ∨ (B.y - A.y < 0 ∧ c.y ≤ (floorPoint A).y))
    (h_not_done : (rayMarchStep A B 0 (B.y - A.y) 0 stepY c).2 = false) :
    let next := (rayMarchStep A B 0 (B.y - A.y) 0 stepY c).1
    inBoundingBox next A B = true ∧
    next.x = (floorPoint A).x ∧
    ((0 < B.y - A.y ∧ (floorPoint A).y ≤ next.y) ∨ (B.y - A.y < 0 ∧ next.y ≤ (floorPoint A).y)) ∧
    ∃ tEnter tExit, cellIntersectionInterval next A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  intro next
  have h_step := rayMarchStep_sx_zero_step A B c (B.y - A.y) stepY h_not_done
  rcases h_step with ⟨h_step_eq, h_rem⟩
  dsimp [next]
  rw [h_step_eq]
  rcases hc_y with ⟨hdy_pos, hcy_le⟩ | ⟨hdy_neg, hcy_ge⟩
  · have hsy : stepY = 1 := by rw [hstepY]; simp [hdy_pos]
    rw [hsy] at h_step_eq h_rem ⊢
    have h_yb : (if (1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) := by rfl
    have h_abs : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
      simp [show B.y - A.y ≥ 0 by linarith]
    rw [h_yb, h_abs] at h_rem
    have h_yb_ge : ofInt (c.y + 1) ≥ A.y := by
      have h_flAy : A.y < ofInt ((floorPoint A).y + 1) := by
        unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
      have h_int_le : (floorPoint A).y + 1 ≤ c.y + 1 := by omega
      have h_le_cy : ofInt ((floorPoint A).y + 1) ≤ ofInt (c.y + 1) := by
        unfold ofInt; exact Int.cast_le.mpr h_int_le
      linarith
    have h_case : (if ofInt (c.y + 1) ≥ A.y then ofInt (c.y + 1) - A.y else A.y - ofInt (c.y + 1)) = ofInt (c.y + 1) - A.y := by
      simp [h_yb_ge]
    rw [h_case] at h_rem
    have h_bnd_y : c.y + 1 ≤ (floorPoint B).y := stepY_pos_next_le_end (c.y + 1) A.y B hdy_pos h_rem
    have h_bbox_next : inBoundingBox ⟨c.x, c.y + 1⟩ A B = true :=
      inBoundingBox_stepY_forward c A B hdy_pos hc_bbox h_bnd_y
    have h_inter := cellIntersectionInterval_sx_zero_pos A B c hdx hdy_pos hc_x hcy_le h_rem
    dsimp only []
    refine ⟨h_bbox_next, hc_x, Or.inl ⟨hdy_pos, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩
  · have hsy : stepY = -1 := by
      rw [hstepY]
      simp [show ¬(B.y - A.y > 0) by linarith, hdy_neg]
    rw [hsy] at h_step_eq h_rem ⊢
    have h_yb : (if (-1 : Int) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt c.y := by rfl
    have h_abs : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
      simp [show ¬(B.y - A.y ≥ 0) by linarith]
    rw [h_yb, h_abs] at h_rem
    have h_yb_le : ofInt c.y ≤ A.y := by
      have h_flAy : ofInt (floorPoint A).y ≤ A.y := by
        unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
      have h_cy_le : ofInt c.y ≤ ofInt (floorPoint A).y := by
        unfold ofInt; exact Int.cast_le.mpr hcy_ge
      linarith
    have h_case : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
      by_cases h_eq : ofInt c.y ≥ A.y
      · have : ofInt c.y = A.y := le_antisymm h_yb_le h_eq
        simp [this]
      · simp [h_eq]
    rw [h_case] at h_rem
    have h_div_lt : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
      have h_eq : (ofInt c.y - A.y) / (B.y - A.y) = (A.y - ofInt c.y) / (A.y - B.y) := by
        have h1 : ofInt c.y - A.y = -(A.y - ofInt c.y) := by ring
        have h2 : B.y - A.y = -(A.y - B.y) := by ring
        rw [h1, h2, neg_div_neg_eq]
      rw [h_eq]
      have h_pos_den : 0 < A.y - B.y := by linarith
      have h_rem' : A.y - ofInt c.y < A.y - B.y := by linarith
      exact (div_lt_one h_pos_den).mpr h_rem'
    have h_bnd_y : (floorPoint B).y ≤ c.y - 1 := stepY_neg_next_ge_end c.y A.y B hdy_neg h_div_lt
    have h_bbox_next : inBoundingBox ⟨c.x, c.y - 1⟩ A B = true :=
      inBoundingBox_stepY_backward c A B hdy_neg hc_bbox h_bnd_y
    have h_inter := cellIntersectionInterval_sx_zero_neg A B c hdx hdy_neg hc_x hcy_ge h_div_lt
    dsimp only []
    refine ⟨h_bbox_next, hc_x, Or.inr ⟨hdy_neg, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩


theorem rayMarchStep_sound_step_sy_zero (A B : Point) (stepX : Int) (c : Cell)
    (hdy : B.y - A.y = 0)
    (hsx_ne : (stepX == 0) = false)
    (hstepX : stepX = if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_y : c.y = (floorPoint A).y)
    (hc_x : (0 < B.x - A.x ∧ (floorPoint A).x ≤ c.x) ∨ (B.x - A.x < 0 ∧ c.x ≤ (floorPoint A).x))
    (h_not_done : (rayMarchStep A B (B.x - A.x) 0 stepX 0 c).2 = false) :
    let next := (rayMarchStep A B (B.x - A.x) 0 stepX 0 c).1
    inBoundingBox next A B = true ∧
    next.y = (floorPoint A).y ∧
    ((0 < B.x - A.x ∧ (floorPoint A).x ≤ next.x) ∨ (B.x - A.x < 0 ∧ next.x ≤ (floorPoint A).x)) ∧
    ∃ tEnter tExit, cellIntersectionInterval next A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  intro next
  have h_step := rayMarchStep_sy_zero_step A B c (B.x - A.x) stepX hsx_ne h_not_done
  rcases h_step with ⟨h_step_eq, h_rem⟩
  dsimp [next]
  rw [h_step_eq]
  rcases hc_x with ⟨hdx_pos, hcx_le⟩ | ⟨hdx_neg, hcx_ge⟩
  · have hsx : stepX = 1 := by rw [hstepX]; simp [hdx_pos]
    rw [hsx] at h_step_eq h_rem ⊢
    have h_xb : (if (1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) := by rfl
    have h_abs : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
      simp [show B.x - A.x ≥ 0 by linarith]
    rw [h_xb, h_abs] at h_rem
    have h_xb_ge : ofInt (c.x + 1) ≥ A.x := by
      have h_flAx : A.x < ofInt ((floorPoint A).x + 1) := by
        unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
      have h_int_le : (floorPoint A).x + 1 ≤ c.x + 1 := by omega
      have h_le_cx : ofInt ((floorPoint A).x + 1) ≤ ofInt (c.x + 1) := by
        unfold ofInt; exact Int.cast_le.mpr h_int_le
      linarith
    have h_case : (if ofInt (c.x + 1) ≥ A.x then ofInt (c.x + 1) - A.x else A.x - ofInt (c.x + 1)) = ofInt (c.x + 1) - A.x := by
      simp [h_xb_ge]
    rw [h_case] at h_rem
    have h_bnd_x : c.x + 1 ≤ (floorPoint B).x := stepX_pos_next_le_end (c.x + 1) A.x B hdx_pos h_rem
    have h_bbox_next : inBoundingBox ⟨c.x + 1, c.y⟩ A B = true :=
      inBoundingBox_stepX_forward c A B hdx_pos hc_bbox h_bnd_x
    have h_inter := cellIntersectionInterval_sy_zero_pos A B c hdx_pos hdy hc_y hcx_le h_rem
    dsimp only []
    refine ⟨h_bbox_next, hc_y, Or.inl ⟨hdx_pos, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩
  · have hsx : stepX = -1 := by
      rw [hstepX]
      simp [show ¬(B.x - A.x > 0) by linarith, hdx_neg]
    rw [hsx] at h_step_eq h_rem ⊢
    have h_xb : (if (-1 : Int) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt c.x := by rfl
    have h_abs : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
      simp [show ¬(B.x - A.x ≥ 0) by linarith]
    rw [h_xb, h_abs] at h_rem
    have h_xb_le : ofInt c.x ≤ A.x := by
      have h_flAx : ofInt (floorPoint A).x ≤ A.x := by
        unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
      have h_cx_le : ofInt c.x ≤ ofInt (floorPoint A).x := by
        unfold ofInt; exact Int.cast_le.mpr hcx_ge
      linarith
    have h_case : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
      by_cases h_eq : ofInt c.x ≥ A.x
      · have : ofInt c.x = A.x := le_antisymm h_xb_le h_eq
        simp [this]
      · simp [h_eq]
    rw [h_case] at h_rem
    have h_div_lt : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
      have h_eq : (ofInt c.x - A.x) / (B.x - A.x) = (A.x - ofInt c.x) / (A.x - B.x) := by
        have h1 : ofInt c.x - A.x = -(A.x - ofInt c.x) := by ring
        have h2 : B.x - A.x = -(A.x - B.x) := by ring
        rw [h1, h2, neg_div_neg_eq]
      rw [h_eq]
      have h_pos_den : 0 < A.x - B.x := by linarith
      have h_rem' : A.x - ofInt c.x < A.x - B.x := by linarith
      exact (div_lt_one h_pos_den).mpr h_rem'
    have h_bnd_x : (floorPoint B).x ≤ c.x - 1 := stepX_neg_next_ge_end c.x A.x B hdx_neg h_div_lt
    have h_bbox_next : inBoundingBox ⟨c.x - 1, c.y⟩ A B = true :=
      inBoundingBox_stepX_backward c A B hdx_neg hc_bbox h_bnd_x
    have h_inter := cellIntersectionInterval_sy_zero_neg A B c hdx_neg hdy hc_y hcx_ge h_div_lt
    dsimp only []
    refine ⟨h_bbox_next, hc_y, Or.inr ⟨hdx_neg, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩


theorem rayMarch_soundness_sx_zero (A B : Point) (x : Cell)
    (hdx : B.x - A.x = 0)
    (hA_eq_B : ¬(floorPoint A = floorPoint B))
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : Int)) = 0 := by simp [hdx]
  have hdy_ne : ¬(B.y - A.y = 0) := by
    intro h_dy0
    have : A = B := by
      rcases A with ⟨Ax, Ay⟩
      rcases B with ⟨Bx, By⟩
      dsimp at hdx h_dy0
      have : Ax = Bx := by linarith
      have : Ay = By := by linarith
      congr
    rw [this] at hA_eq_B
    exact hA_eq_B rfl
  let stepY : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
  rw [hsx, hdx] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  let P : Cell → Prop := fun cell =>
    inBoundingBox cell A B = true ∧
    cell.x = (floorPoint A).x ∧
    ((0 < B.y - A.y ∧ (floorPoint A).y ≤ cell.y) ∨ (B.y - A.y < 0 ∧ cell.y ≤ (floorPoint A).y)) ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit
  have h_sound := sound_from_first_step _ _ _ 0 (B.y - A.y) 0 stepY (floorPoint B) P
    (by
      intro c hc h_not_done
      exact rayMarchStep_sound_step_sx_zero A B stepY c hdx rfl hc.1 hc.2.1 hc.2.2.1 h_not_done)
    (by
      intro h_not_done
      have hc_bbox : inBoundingBox (floorPoint A) A B = true := inBoundingBox_startCell A B
      have hc_x : (floorPoint A).x = (floorPoint A).x := rfl
      have hc_y : (0 < B.y - A.y ∧ (floorPoint A).y ≤ (floorPoint A).y) ∨ (B.y - A.y < 0 ∧ (floorPoint A).y ≤ (floorPoint A).y) := by
        by_cases hdy_pos : 0 < B.y - A.y
        · exact Or.inl ⟨hdy_pos, le_rfl⟩
        · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy_pos) hdy_ne
          exact Or.inr ⟨hdy_neg, le_rfl⟩
      exact rayMarchStep_sound_step_sx_zero A B stepY (floorPoint A) hdx rfl hc_bbox hc_x hc_y h_not_done)
    x hx
  exact ⟨h_sound.1, h_sound.2.2.2⟩


theorem rayMarch_soundness_sy_zero (A B : Point) (x : Cell)
    (hdy : B.y - A.y = 0)
    (hA_eq_B : ¬(floorPoint A = floorPoint B))
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : Int)) = 0 := by simp [hdy]
  have hdx_ne : ¬(B.x - A.x = 0) := by
    intro h_dx0
    have : A = B := by
      rcases A with ⟨Ax, Ay⟩
      rcases B with ⟨Bx, By⟩
      dsimp at hdy h_dx0
      have : Ax = Bx := by linarith
      have : Ay = By := by linarith
      congr
    rw [this] at hA_eq_B
    exact hA_eq_B rfl
  let stepX : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
  have hsx_ne : (stepX == 0) = false := by
    cases h : (stepX == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      dsimp [stepX] at this
      by_cases h1 : B.x - A.x > 0
      · simp [h1] at this
      · by_cases h2 : B.x - A.x < 0
        · simp [h1, h2] at this
        · simp [h1, h2] at this
          exact hdx_ne (by linarith)
  rw [hsy, hdy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  let P : Cell → Prop := fun cell =>
    inBoundingBox cell A B = true ∧
    cell.y = (floorPoint A).y ∧
    ((0 < B.x - A.x ∧ (floorPoint A).x ≤ cell.x) ∨ (B.x - A.x < 0 ∧ cell.x ≤ (floorPoint A).x)) ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit
  have h_sound := sound_from_first_step _ _ _ (B.x - A.x) 0 stepX 0 (floorPoint B) P
    (by
      intro c hc h_not_done
      exact rayMarchStep_sound_step_sy_zero A B stepX c hdy hsx_ne rfl hc.1 hc.2.1 hc.2.2.1 h_not_done)
    (by
      intro h_not_done
      have hc_bbox : inBoundingBox (floorPoint A) A B = true := inBoundingBox_startCell A B
      have hc_y : (floorPoint A).y = (floorPoint A).y := rfl
      have hc_x : (0 < B.x - A.x ∧ (floorPoint A).x ≤ (floorPoint A).x) ∨ (B.x - A.x < 0 ∧ (floorPoint A).x ≤ (floorPoint A).x) := by
        by_cases hdx_pos : 0 < B.x - A.x
        · exact Or.inl ⟨hdx_pos, le_rfl⟩
        · have hdx_neg : B.x - A.x < 0 := lt_of_le_of_ne (not_lt.mp hdx_pos) hdx_ne
          exact Or.inr ⟨hdx_neg, le_rfl⟩
      exact rayMarchStep_sound_step_sy_zero A B stepX (floorPoint A) hdy hsx_ne rfl hc_bbox hc_y hc_x h_not_done)
    x hx
  exact ⟨h_sound.1, h_sound.2.2.2⟩


/- =========================================================================
   Top-level Soundness Theorem
   ========================================================================= -/

theorem rayMarch_soundness (A B : Point) (x : Cell)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  by_cases hA_eq_B : floorPoint A = floorPoint B
  · have := rayMarch_same_endpoints
      (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      hA_eq_B
    have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
      (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
    rw [h_fuel, this] at hx
    contradiction
  · by_cases hdx0 : B.x - A.x = 0
    · exact rayMarch_soundness_sx_zero A B x hdx0 hA_eq_B hx
    · by_cases hdy0 : B.y - A.y = 0
      · exact rayMarch_soundness_sy_zero A B x hdy0 hA_eq_B hx
      · by_cases hdx : 0 < B.x - A.x
        · by_cases hdy : 0 < B.y - A.y
          · exact rayMarch_soundness_pos_pos A B x hdx hdy hx
          · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy) hdy0
            exact rayMarch_soundness_pos_neg A B x hdx hdy_neg hx
        · have hdx_neg : B.x - A.x < 0 := lt_of_le_of_ne (not_lt.mp hdx) hdx0
          by_cases hdy : 0 < B.y - A.y
          · exact rayMarch_soundness_neg_pos A B x hdx_neg hdy hx
          · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy) hdy0
            exact rayMarch_soundness_neg_neg A B x hdx_neg hdy_neg hx



/--
Master Theorem (Exact Characterization of LineSegment Cell Intersections):
For all line segments from A to B and all discrete grid cells c:
A cell c is in `cellIntersectionsSegment A B` IF AND ONLY IF:
c is an active intersected cell of the line segment (it intersects the line segment
and is not an off-axis corner).
-/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  apply cellIntersectionsSegment_exact_iff_reduction
  intro hne hcA hcB
  have h_sound : ∀ x, x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] →
      inBoundingBox x A B = true ∧
      ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
    intro x hx
    exact rayMarch_soundness A B x hx
  apply rayMarch_iff_intermediate_of_mem_eq A B c hcA hcB
  · intro x hxA hxB
    apply rayMarchIntermediateCells_iff_intermediateCells A B x hxA hxB
    · exact h_sound x
    · intro h_bbox h_int
      exact rayMarch_completeness A B x hxA hxB h_bbox h_int
  · intro hray
    rcases h_sound c hray with ⟨h_bbox, tEnter, tExit, h_int, h_lt⟩
    exact not_off_axis_of_interval_lt c A B hcA hcB h_bbox tEnter tExit h_int h_lt

end Geometry
