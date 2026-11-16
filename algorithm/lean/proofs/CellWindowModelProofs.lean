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

import models.CellWindowModel

namespace Algorithm.KotlinModel

theorem mkCellWindowModel_some_iff_Impl (l t r b : Int32) :
    (mkCellWindowModel l t r b).isSome ↔ (t ≤ b ∧ l ≤ r) := by
  unfold mkCellWindowModel isValidCellWindow
  split <;> simp_all

theorem mkCellWindowModel_invalid_Impl (l t r b : Int32) (h : b < t ∨ r < l) :
    mkCellWindowModel l t r b = none := by
  unfold mkCellWindowModel isValidCellWindow
  rw [Int32.lt_iff_toInt_lt, Int32.lt_iff_toInt_lt] at h
  have h1 := Int32.le_iff_toInt_le (x := t) (y := b)
  have h2 := Int32.le_iff_toInt_le (x := l) (y := r)
  split
  · simp_all
    omega
  · rfl

/-- `int32RangeUntil` as one map over `List.range` (empty exactly when `stop ≤ start`). -/
private theorem int32RangeUntil_eq (start stop : Int32) :
    int32RangeUntil start stop =
      (List.range (stop.toInt - start.toInt).toNat).map fun k => Int32.ofInt (start.toInt + Int.ofNat k) := by
  unfold int32RangeUntil
  split
  · rename_i h
    rw [Int32.le_iff_toInt_le] at h
    rw [show (stop.toInt - start.toInt).toNat = 0 by omega]
    rfl
  · rfl

/-- The `k`-th element of `int32RangeUntil start stop` does not wrap. -/
private theorem toInt_rangeElem {start stop : Int32} {k : Nat} (hk : k < (stop.toInt - start.toInt).toNat) :
    (Int32.ofInt (start.toInt + Int.ofNat k)).toInt = start.toInt + k := by
  have := Int32.le_toInt start
  have := Int32.toInt_lt stop
  rw [Int.ofNat_eq_natCast]
  exact Int32.toInt_ofInt_of_le (by omega) (by omega)

private theorem int32RangeUntil_length (start stop : Int32) :
    (int32RangeUntil start stop).length =
      if start.toInt ≤ stop.toInt then (stop.toInt - start.toInt).toNat else 0 := by
  rw [int32RangeUntil_eq, List.length_map, List.length_range]
  split <;> omega

private theorem length_flatMap_const {α β : Type _} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem CellWindowModel_containedPoints_length_Impl (w : CellWindowModel) :
    w.containedPoints.length =
      (if w.left.toInt ≤ w.right.toInt then (w.right.toInt - w.left.toInt).toNat else 0) *
      (if w.top.toInt ≤ w.bottom.toInt then (w.bottom.toInt - w.top.toInt).toNat else 0) := by
  unfold CellWindowModel.containedPoints
  rw [length_flatMap_const _ _ (int32RangeUntil w.left w.right).length (fun _ _ => List.length_map ..),
    int32RangeUntil_length, int32RangeUntil_length, Nat.mul_comm]

private theorem mem_int32RangeUntil_iff (start stop x : Int32) :
    x ∈ int32RangeUntil start stop ↔ start.toInt ≤ x.toInt ∧ x.toInt < stop.toInt := by
  rw [int32RangeUntil_eq, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    rw [toInt_rangeElem hk]
    omega
  · intro hx
    refine ⟨(x.toInt - start.toInt).toNat, List.mem_range.mpr (by omega), ?_⟩
    rw [show start.toInt + Int.ofNat (x.toInt - start.toInt).toNat = x.toInt by
      rw [Int.ofNat_eq_natCast]; omega, Int32.ofInt_toInt]

theorem CellWindowModel_mem_containedPoints_iff_Impl (w : CellWindowModel) (x y : Int32) :
    (x, y) ∈ w.containedPoints ↔
      (w.left.toInt ≤ x.toInt ∧ x.toInt < w.right.toInt ∧
       w.top.toInt ≤ y.toInt ∧ y.toInt < w.bottom.toInt) := by
  unfold CellWindowModel.containedPoints
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq, mem_int32RangeUntil_iff]
  constructor
  · rintro ⟨y', hy', x', hx', rfl, rfl⟩
    exact ⟨hx'.1, hx'.2, hy'.1, hy'.2⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩
    exact ⟨y, ⟨hy1, hy2⟩, x, ⟨hx1, hx2⟩, rfl, rfl⟩

private theorem int32RangeUntil_nodup (start stop : Int32) :
    (int32RangeUntil start stop).Nodup := by
  rw [int32RangeUntil_eq]
  unfold List.Nodup
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem fun ha hb hab heq => ?_
  rw [List.mem_range] at ha hb
  have h := congrArg Int32.toInt heq
  rw [toInt_rangeElem ha, toInt_rangeElem hb] at h
  omega

theorem CellWindowModel_containedPoints_nodup_Impl (w : CellWindowModel) :
    w.containedPoints.Nodup := by
  unfold CellWindowModel.containedPoints List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun y _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (int32RangeUntil_nodup w.left w.right).imp fun hne heq => hne (Prod.mk.inj heq).1
  · refine (int32RangeUntil_nodup w.top w.bottom).imp fun hne => ?_
    intro p hp q hq heq
    rw [List.mem_map] at hp hq
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, rfl⟩ := hq
    exact hne (Prod.mk.inj heq).2

private theorem getElem?_flatMap_mul_add {α β : Type _} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ a ∈ l, (f a).length = n) (j i : Nat) (hi : i < n) :
    (l.flatMap f)[j * n + i]? = l[j]?.bind fun a => (f a)[i]? := by
  induction l generalizing j with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ j =>
      rw [List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ha,
        show (j + 1) * n + i - n = j * n + i by rw [Nat.succ_mul]; omega,
        ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
      rfl

theorem CellWindowModel_containedPoints_getElem?_Impl (w : CellWindowModel) (i j : Nat)
    (hi : i < (w.right.toInt - w.left.toInt).toNat) (hj : j < (w.bottom.toInt - w.top.toInt).toNat) :
    w.containedPoints[j * (w.right.toInt - w.left.toInt).toNat + i]? =
      some (Int32.ofInt (w.left.toInt + i), Int32.ofInt (w.top.toInt + j)) := by
  unfold CellWindowModel.containedPoints
  rw [getElem?_flatMap_mul_add _ _ _ (fun _ _ => by rw [List.length_map, int32RangeUntil_eq,
      List.length_map, List.length_range]) j i hi]
  rw [int32RangeUntil_eq w.top, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.bind_some]
  rw [List.getElem?_map, int32RangeUntil_eq, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem toInt_add_of_bounds {a b : Int32} (h1 : -2 ^ 31 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2 ^ 31) : (a + b).toInt = a.toInt + b.toInt := by
  have : a + b = Int32.ofInt (a.toInt + b.toInt) := by
    rw [Int32.ofInt_add, Int32.ofInt_toInt, Int32.ofInt_toInt]
  rw [this, Int32.toInt_ofInt_of_le h1 h2]

private theorem int32RangeUntil_translate (start stop delta : Int32)
    (hmin : Int32.minValue.toInt ≤ start.toInt + delta.toInt)
    (hmax : stop.toInt + delta.toInt ≤ Int32.maxValue.toInt)
    (hle : start.toInt ≤ stop.toInt) :
    int32RangeUntil (start + delta) (stop + delta) =
      (int32RangeUntil start stop).map (· + delta) := by
  have hm : Int32.minValue.toInt = -2147483648 := by decide
  have hM : Int32.maxValue.toInt = 2147483647 := by decide
  have h1 : (start + delta).toInt = start.toInt + delta.toInt := toInt_add_of_bounds (by omega) (by omega)
  have h2 : (stop + delta).toInt = stop.toInt + delta.toInt := toInt_add_of_bounds (by omega) (by omega)
  rw [int32RangeUntil_eq, int32RangeUntil_eq, List.map_map, h1, h2,
    show stop.toInt + delta.toInt - (start.toInt + delta.toInt) = stop.toInt - start.toInt by omega]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, Int32.ofInt_add, Int32.ofInt_toInt]
  rw [Int32.add_assoc, Int32.add_comm delta, ← Int32.add_assoc, Int32.add_assoc]

theorem CellWindowModel_translate_containedPoints_Impl (w w' : CellWindowModel) (dx dy : Int32)
    (ht : w.translate dx dy = some w')
    (hvx : w.left.toInt ≤ w.right.toInt) (hvy : w.top.toInt ≤ w.bottom.toInt)
    (hminX : Int32.minValue.toInt ≤ w.left.toInt + dx.toInt)
    (hmaxX : w.right.toInt + dx.toInt ≤ Int32.maxValue.toInt)
    (hminY : Int32.minValue.toInt ≤ w.top.toInt + dy.toInt)
    (hmaxY : w.bottom.toInt + dy.toInt ≤ Int32.maxValue.toInt) :
    w'.containedPoints = w.containedPoints.map (fun p => (p.1 + dx, p.2 + dy)) := by
  unfold CellWindowModel.translate mkCellWindowModel at ht
  split at ht
  · cases ht
    unfold CellWindowModel.containedPoints
    rw [int32RangeUntil_translate w.top w.bottom dy hminY hmaxY hvy,
      int32RangeUntil_translate w.left w.right dx hminX hmaxX hvx, List.flatMap_map, List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
  · cases ht

private theorem toInt_sub_of_fits {a b : Int32} (h : a.toInt ≤ b.toInt)
    (hfit : b.toInt - a.toInt ≤ Int32.maxValue.toInt) : (b - a).toInt = b.toInt - a.toInt := by
  have hM : Int32.maxValue.toInt = 2147483647 := by decide
  have := Int32.le_toInt a
  have := Int32.toInt_lt b
  rw [Int32.toInt_sub, Int.bmod_eq_of_le] <;> simp <;> omega

theorem CellWindowModel_width_toInt_Impl (w : CellWindowModel) (h : w.left.toInt ≤ w.right.toInt)
    (hfit : w.right.toInt - w.left.toInt ≤ Int32.maxValue.toInt) :
    w.width.toInt = w.right.toInt - w.left.toInt :=
  toInt_sub_of_fits h hfit

theorem CellWindowModel_height_toInt_Impl (w : CellWindowModel) (h : w.top.toInt ≤ w.bottom.toInt)
    (hfit : w.bottom.toInt - w.top.toInt ≤ Int32.maxValue.toInt) :
    w.height.toInt = w.bottom.toInt - w.top.toInt :=
  toInt_sub_of_fits h hfit

end Algorithm.KotlinModel
