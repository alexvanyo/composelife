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

import models.HashLifeCacheModel

namespace Algorithm.KotlinModel

private theorem map_fst_assocPut_of_mem {K V : Type} [BEq K] [LawfulBEq K]
    (xs : List (K × V)) (k : K) (v : V)
    (h : xs.any (fun p => p.1 == k) = true) :
    (assocPut xs k v).map Prod.fst = xs.map Prod.fst := by
  unfold assocPut
  simp only [h, ↓reduceIte, List.map_map]
  clear h
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, Function.comp_apply]
    rw [ih]
    congr 1
    by_cases hp : p.1 == k
    · simp [beq_iff_eq.mp hp]
    · simp [hp]

private theorem map_fst_assocPut_of_not_mem {K V : Type} [BEq K]
    (xs : List (K × V)) (k : K) (v : V)
    (h : xs.any (fun p => p.1 == k) = false) :
    (assocPut xs k v).map Prod.fst = xs.map Prod.fst ++ [k] := by
  unfold assocPut
  simp [h]

theorem cacheModel_put_preserves_keysSynced_Impl {K V : Type} [BEq K] [LawfulBEq K]
    (c : CacheModel K V) (k : K) (v : V) (gen : Int64)
    (hsync : c.keysSynced) :
    (c.put k v gen).keysSynced := by
  unfold CacheModel.keysSynced CacheModel.put at *
  have hany : c.entries.any (fun p => p.1 == k) = c.lastAccessed.any (fun p => p.1 == k) := by
    have h1 : ∀ {W : Type} (l : List (K × W)), l.any (fun p => p.1 == k) = (l.map Prod.fst).any (· == k) := by
      intro W l; induction l with | nil => rfl | cons x xs ih => simp [ih]
    rw [h1, h1, hsync]
  cases ha : c.entries.any (fun p => p.1 == k)
  · have hb : c.lastAccessed.any (fun p => p.1 == k) = false := by rw [← hany, ha]
    rw [map_fst_assocPut_of_not_mem _ _ _ ha, map_fst_assocPut_of_not_mem _ _ _ hb, hsync]
  · have hb : c.lastAccessed.any (fun p => p.1 == k) = true := by rw [← hany, ha]
    rw [map_fst_assocPut_of_mem _ _ _ ha, map_fst_assocPut_of_mem _ _ _ hb, hsync]

theorem cacheModel_prune_retains_recent_Impl {K V : Type} [BEq K]
    (c : CacheModel K V) (oldestGen : Int64) :
    ∀ p ∈ (c.prune oldestGen).lastAccessed, ¬ (p.2 < oldestGen) := by
  intro p hp
  unfold CacheModel.prune at hp
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  exact hp.2

theorem wrapperEqualsModel_refl_Impl {T : Type} (eqId : Nat) (isEq : T → T → Bool)
    (hrefl : ∀ x, isEq x x = true) (v : T) :
    wrapperEqualsModel eqId eqId isEq v v = true := by
  unfold wrapperEqualsModel
  simp [hrefl v]

theorem wrapperEqualsModel_symm_Impl {T : Type} (eqId1 eqId2 : Nat) (isEq : T → T → Bool)
    (hsymm : ∀ x y, isEq x y = isEq y x) (v1 v2 : T) :
    wrapperEqualsModel eqId1 eqId2 isEq v1 v2 = wrapperEqualsModel eqId2 eqId1 isEq v2 v1 := by
  unfold wrapperEqualsModel
  by_cases h : eqId1 = eqId2
  · subst h; simp [hsymm]
  · simp [beq_false_of_ne h, beq_false_of_ne (Ne.symm h), hsymm]

end Algorithm.KotlinModel
