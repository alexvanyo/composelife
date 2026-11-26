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

import models.DeserializationResultModel

namespace Algorithm.KotlinModel

theorem reduceToSuccessfulStep_preserves_successful_Impl (a b : DeserResultModel)
    (h : a.isSuccessful = true ∨ b.isSuccessful = true) :
    (reduceToSuccessfulStep a b).isSuccessful = true := by
  cases a with
  | unsuccessful _ =>
    cases b <;> simp [reduceToSuccessfulStep, reduceToSuccessfulPicksFirst, DeserResultModel.isSuccessful] at h ⊢
  | successful clean _ =>
    cases b with
    | unsuccessful _ => rfl
    | successful _ _ => cases clean <;> rfl

theorem reduceToSuccessfulStep_warningFree_dominates_Impl (id : Nat) (b : DeserResultModel) :
    reduceToSuccessfulStep (.successful true id) b = .successful true id := by
  cases b <;> rfl

private theorem foldl_reduce_preserves_successful (xs : List DeserResultModel) (acc : DeserResultModel)
    (h : acc.isSuccessful = true ∨ ∃ x ∈ xs, x.isSuccessful = true) :
    (xs.foldl reduceToSuccessfulStep acc).isSuccessful = true := by
  induction xs generalizing acc with
  | nil =>
    rcases h with ha | ⟨x, hx, _⟩
    · exact ha
    · cases hx
  | cons y ys ih =>
    apply ih
    rcases h with ha | ⟨x, hx, hxs⟩
    · exact Or.inl (reduceToSuccessfulStep_preserves_successful_Impl acc y (Or.inl ha))
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hmem
      · exact Or.inl (reduceToSuccessfulStep_preserves_successful_Impl acc x (Or.inr hxs))
      · exact Or.inr ⟨x, hmem, hxs⟩

theorem reduceToSuccessful_finds_successful_Impl (xs : List DeserResultModel)
    (h : ∃ x ∈ xs, x.isSuccessful = true) :
    ∃ r, reduceToSuccessfulModel xs = some r ∧ r.isSuccessful = true := by
  cases xs with
  | nil =>
    rcases h with ⟨_, hx, _⟩
    cases hx
  | cons y ys =>
    refine ⟨ys.foldl reduceToSuccessfulStep y, rfl, ?_⟩
    apply foldl_reduce_preserves_successful
    rcases h with ⟨x, hx, hxs⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact Or.inl hxs
    · exact Or.inr ⟨x, hmem, hxs⟩

theorem fromFileExtension_known_Impl :
    fromFileExtensionModel (some "cells") = .plaintext ∧
    fromFileExtensionModel (some "lif") = .life ∧
    fromFileExtensionModel (some "life") = .life ∧
    fromFileExtensionModel (some "rle") = .runLengthEncoding ∧
    fromFileExtensionModel (some "mc") = .macrocell ∧
    fromFileExtensionModel none = .unknown :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Algorithm.KotlinModel
