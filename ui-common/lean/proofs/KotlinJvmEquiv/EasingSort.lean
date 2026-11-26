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

import JvmSemantics
import proofs.EasingPiecewiseModelProofs

/-!
# `sortedBy { it.first } == toList()` as `isSortedByKeyframe`

The `require` in `Easing(easing, vararg easings)` compares the stably sorted pair list with the original one using
`Pair.equals` (`Float.equals` on keys, `Easing.equals` on values). This module proves that this comparison is exactly
`Model.isSortedByKeyframe`, using only the structure of `Model.floatCompare` and the logical `Float32` model.
-/

namespace UiCommon.KotlinJvmVerification

open UiCommon.JvmVerification
open UiCommon.Model

/-! ### `Float32` facts -/

theorem float32_eq_of_toBits_eq {a b : Float32} (h : a.toBits = b.toBits) : a = b := by
  cases a with | ofModel am =>
  cases b with | ofModel bm =>
  congr 1; cases am; cases bm
  simp only [Float32.toBits] at h
  subst h; rfl

theorem float32_isNaN_of_toBits {a : Float32} (hb : a.toBits = 0x7fc00000) : a.isNaN = true := by
  have h : a = Float32.ofBits 0x7fc00000 := float32_eq_of_toBits_eq (by rw [hb]; decide)
  rw [h]
  decide

theorem float32_unpack_of_isNaN {a : Float32} (ha : a.isNaN = true) : a.toModel.unpack = .notANumber := by
  cases hu : a.toModel.unpack <;>
    simp [Float32.isNaN, Float32.Model.isNaN, Float.Model.UnpackedFloat.isNaN, hu] at ha ⊢

theorem float32_not_lt_of_isNaN_left {a : Float32} (ha : a.isNaN = true) (b : Float32) : ¬ a < b := by
  intro h
  have hm : a.toModel.lt b.toModel = true := of_decide_eq_true h
  have hc : a.toModel.unpack.compare b.toModel.unpack = some .lt := by
    simpa [Float32.Model.lt, Float.Model.UnpackedFloat.lt] using hm
  rw [float32_unpack_of_isNaN ha] at hc
  simp [Float.Model.UnpackedFloat.compare] at hc

theorem float32_not_lt_of_isNaN_right {a : Float32} (ha : a.isNaN = true) (b : Float32) : ¬ b < a := by
  intro h
  have hm : b.toModel.lt a.toModel = true := of_decide_eq_true h
  have hc : b.toModel.unpack.compare a.toModel.unpack = some .lt := by
    simpa [Float32.Model.lt, Float.Model.UnpackedFloat.lt] using hm
  rw [float32_unpack_of_isNaN ha] at hc
  cases hb : b.toModel.unpack <;> simp [hb, Float.Model.UnpackedFloat.compare] at hc

/-- `Float.equals` keys are either the same `Float32` or both `NaN`. -/
theorem floatKeyEq_cases {a b : Float32} (h : floatKeyEq a b = true) :
    a = b ∨ (a.isNaN = true ∧ b.isNaN = true) := by
  unfold floatKeyEq at h
  have hbits := beq_iff_eq.mp h
  by_cases ha : a.isNaN = true <;> by_cases hb : b.isNaN = true
  · exact Or.inr ⟨ha, hb⟩
  · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true] at hbits
    exact absurd (float32_isNaN_of_toBits hbits.symm) hb
  · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true] at hbits
    exact absurd (float32_isNaN_of_toBits hbits) ha
  · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true] at hbits
    exact Or.inl (float32_eq_of_toBits_eq hbits)

theorem floatCompare_congr_left {a a' : Float32} (h : floatKeyEq a a' = true) (b : Float32) :
    floatCompare a b = floatCompare a' b := by
  rcases floatKeyEq_cases h with rfl | ⟨ha, ha'⟩
  · rfl
  · unfold floatCompare
    simp [float32_not_lt_of_isNaN_left ha, float32_not_lt_of_isNaN_left ha',
      float32_not_lt_of_isNaN_right ha, float32_not_lt_of_isNaN_right ha', ha, ha']

theorem floatCompare_congr_right {b b' : Float32} (h : floatKeyEq b b' = true) (a : Float32) :
    floatCompare a b = floatCompare a b' := by
  rcases floatKeyEq_cases h with rfl | ⟨hb, hb'⟩
  · rfl
  · unfold floatCompare
    simp [float32_not_lt_of_isNaN_left hb, float32_not_lt_of_isNaN_left hb',
      float32_not_lt_of_isNaN_right hb, float32_not_lt_of_isNaN_right hb', hb, hb']

theorem floatCompare_swap_le {a b : Float32} (h : ¬ floatCompare a b ≤ 0) : floatCompare b a ≤ 0 := by
  have hgt := (floatCompare_not_le_iff_gt a b).mp h
  have hlt := (floatCompare_gt_zero_iff_flip_lt_zero a b).mp hgt
  exact Int32.le_of_lt hlt

/-! ### Insertion sort produces a sorted list -/

theorem isSortedByKeyframe_cons_cons {E : Type} (x y : Float32 × E) (rest : List (Float32 × E)) :
    isSortedByKeyframe (x :: y :: rest) = (floatCompareLe x.1 y.1 && isSortedByKeyframe (y :: rest)) := by
  rcases x with ⟨k1, e1⟩; rcases y with ⟨k2, e2⟩
  simp [isSortedByKeyframe]

theorem insertPairSorted_head (x : Float32 × UiEasing) (l : List (Float32 × UiEasing)) :
    ∃ h t, insertPairSorted x l = h :: t ∧ (h = x ∨ l.head? = some h) := by
  cases l with
  | nil => exact ⟨x, [], rfl, Or.inl rfl⟩
  | cons y ys =>
    by_cases hle : floatCompare x.1 y.1 ≤ 0
    · exact ⟨x, y :: ys, by simp [insertPairSorted, hle], Or.inl rfl⟩
    · exact ⟨y, insertPairSorted x ys, by simp [insertPairSorted, hle], Or.inr rfl⟩

theorem insertPairSorted_sorted (x : Float32 × UiEasing) :
    ∀ l : List (Float32 × UiEasing), isSortedByKeyframe l = true →
      isSortedByKeyframe (insertPairSorted x l) = true := by
  intro l
  induction l with
  | nil => intro _; simp [insertPairSorted, isSortedByKeyframe]
  | cons y ys ih =>
    intro hs
    by_cases hle : floatCompare x.1 y.1 ≤ 0
    · simp only [insertPairSorted, hle, ↓reduceIte]
      rw [isSortedByKeyframe_cons_cons, hs]
      simp [floatCompareLe, hle]
    · simp only [insertPairSorted, hle, ↓reduceIte]
      have hyx : floatCompare y.1 x.1 ≤ 0 := floatCompare_swap_le hle
      have hys : isSortedByKeyframe ys = true := by
        cases ys with
        | nil => simp [isSortedByKeyframe]
        | cons z zs =>
          rw [isSortedByKeyframe_cons_cons] at hs
          simp only [Bool.and_eq_true] at hs
          exact hs.2
      have hrec := ih hys
      obtain ⟨h, t, heq, hh⟩ := insertPairSorted_head x ys
      rw [heq] at hrec ⊢
      rw [isSortedByKeyframe_cons_cons, hrec]
      rcases hh with rfl | hh
      · simp [floatCompareLe, hyx]
      · cases ys with
        | nil => simp at hh
        | cons z zs =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          rw [isSortedByKeyframe_cons_cons] at hs
          simp only [Bool.and_eq_true] at hs
          simp [hs.1]

theorem sortPairsByKeyframe_sorted (ps : List (Float32 × UiEasing)) :
    isSortedByKeyframe (sortPairsByKeyframe ps) = true := by
  induction ps with
  | nil => simp [sortPairsByKeyframe, isSortedByKeyframe]
  | cons x xs ih => exact insertPairSorted_sorted x _ ih

/-! ### Insertion sort fixes sorted lists -/

theorem isSortedByKeyframe_tail {E : Type} (x : Float32 × E) (l : List (Float32 × E))
    (h : isSortedByKeyframe (x :: l) = true) : isSortedByKeyframe l = true := by
  cases l with
  | nil => simp [isSortedByKeyframe]
  | cons y ys =>
    rw [isSortedByKeyframe_cons_cons] at h
    simp only [Bool.and_eq_true] at h
    exact h.2

theorem sortPairsByKeyframe_of_sorted (ps : List (Float32 × UiEasing)) (h : isSortedByKeyframe ps = true) :
    sortPairsByKeyframe ps = ps := by
  induction ps with
  | nil => rfl
  | cons x xs ih =>
    simp only [sortPairsByKeyframe]
    rw [ih (isSortedByKeyframe_tail x xs h)]
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [isSortedByKeyframe_cons_cons] at h
      simp only [Bool.and_eq_true, floatCompareLe, decide_eq_true_eq] at h
      simp [insertPairSorted, h.1]

/-! ### Element-wise `Pair.equals` transports sortedness -/

/-- `Pair<Float, Easing>.equals` as `beqUiExt` compares list elements. -/
def pairEquals (pq : (Float32 × UiEasing) × (Float32 × UiEasing)) : Bool :=
  floatKeyEq pq.1.1 pq.2.1 && pq.1.2 == pq.2.2

theorem beqUiExt_pairList (xs ys : List (Float32 × UiEasing)) :
    beqUiExt (.pairList xs) (.pairList ys) = (xs.length == ys.length && (xs.zip ys).all pairEquals) := by
  simp only [beqUiExt]
  congr 2

theorem sorted_of_pairEquals :
    ∀ (s ps : List (Float32 × UiEasing)), s.length = ps.length → (s.zip ps).all pairEquals = true →
      isSortedByKeyframe s = true → isSortedByKeyframe ps = true := by
  intro s
  induction s with
  | nil => intro ps hl _ _; cases ps with
    | nil => simp [isSortedByKeyframe]
    | cons _ _ => simp at hl
  | cons a s ih =>
    intro ps hl hall hs
    cases ps with
    | nil => simp at hl
    | cons a' ps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      have htl := ih ps hl hall.2 (isSortedByKeyframe_tail a s hs)
      cases s with
      | nil =>
        cases ps with
        | nil => simp [isSortedByKeyframe]
        | cons _ _ => simp at hl
      | cons b s =>
        cases ps with
        | nil => simp at hl
        | cons b' ps =>
          rw [isSortedByKeyframe_cons_cons, htl]
          rw [isSortedByKeyframe_cons_cons] at hs
          simp only [Bool.and_eq_true] at hs
          have hab := hall.1
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          have hbb := hall.2.1
          simp only [pairEquals, Bool.and_eq_true] at hab hbb
          have h1 := floatCompare_congr_left hab.1 b.1
          have h2 := floatCompare_congr_right hbb.1 a'.1
          simp only [floatCompareLe] at hs ⊢
          rw [← h2, ← h1]
          simp [hs.1]

theorem pairEquals_refl (ps : List (Float32 × UiEasing)) : (ps.zip ps).all pairEquals = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.zip_cons_cons, List.all_cons, ih, Bool.and_true]
    simp [pairEquals, floatKeyEq]

/-- `sortedBy { it.first } == toList()` holds exactly when the pairs are sorted by keyframe. -/
theorem beqUiExt_sortPairs_eq_isSorted (ps : List (Float32 × UiEasing)) :
    beqUiExt (.pairList (sortPairsByKeyframe ps)) (.pairList ps) = isSortedByKeyframe ps := by
  rw [beqUiExt_pairList]
  cases hs : isSortedByKeyframe ps with
  | true =>
    rw [sortPairsByKeyframe_of_sorted ps hs, pairEquals_refl]
    simp
  | false =>
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := sorted_of_pairEquals _ ps h.1 h.2 (sortPairsByKeyframe_sorted ps)
    rw [hs] at this
    exact Bool.false_ne_true this

end UiCommon.KotlinJvmVerification
