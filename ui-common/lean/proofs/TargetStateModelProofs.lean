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

import models.TargetStateModel

namespace UiCommon.Model

theorem mkInProgress?_eq_none_iff_Impl {α μ : Type} [BEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) :
    TargetState.mkInProgress? current provisional progress metadata = none ↔
      (current == provisional) = true := by
  unfold TargetState.mkInProgress?
  cases h : (current == provisional) <;> simp

theorem mkInProgress?_eq_some_iff_Impl {α μ : Type} [BEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) :
    TargetState.mkInProgress? current provisional progress metadata =
        some (.inProgress current provisional progress metadata) ↔
      (current == provisional) = false := by
  unfold TargetState.mkInProgress?
  cases h : (current == provisional) <;> simp

theorem mkInProgress?_isValid_Impl {α μ : Type} [BEq α] [LawfulBEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) (s : TargetState α μ)
    (hs : TargetState.mkInProgress? current provisional progress metadata = some s) :
    s.IsValid := by
  unfold TargetState.mkInProgress? at hs
  cases h : (current == provisional)
  · simp [h] at hs
    subst hs
    intro heq
    subst heq
    simp at h
  · simp [h] at hs

theorem isInProgress_dichotomy_Impl {α μ : Type} (s : TargetState α μ) :
    (s.isInProgress = false → ∃ c, s = .single c) ∧
      (s.isInProgress = true → ∃ c p pr m, s = .inProgress c p pr m) := by
  cases s with
  | single c =>
    refine ⟨fun _ => ⟨c, rfl⟩, fun h => ?_⟩
    simp [TargetState.isInProgress] at h
  | inProgress c p pr m =>
    refine ⟨fun h => ?_, fun _ => ⟨c, p, pr, m, rfl⟩⟩
    simp [TargetState.isInProgress] at h

theorem and_false_Impl {μ : Type} (s : TargetState Bool μ) :
    s.and false = .single false := rfl

theorem and_true_Impl {μ : Type} (s : TargetState Bool μ) :
    s.and true = s := rfl

theorem or_true_Impl {μ : Type} (s : TargetState Bool μ) :
    s.or true = .single true := rfl

theorem or_false_Impl {μ : Type} (s : TargetState Bool μ) :
    s.or false = s := rfl

theorem not_not_Impl {μ : Type} (s : TargetState Bool μ) :
    s.not.not = s := by
  cases s with
  | single c => simp [TargetState.not, TargetState.map]
  | inProgress c p pr m => simp [TargetState.not, TargetState.map]

theorem not_current_Impl {μ : Type} (s : TargetState Bool μ) :
    s.not.current = !s.current := by
  cases s <;> rfl

theorem progressToTrue_not_single_Impl {μ : Type} (b : Bool) :
    (TargetState.single (μ := μ) b).not.progressToTrue =
      (1.0 : Float32) - (TargetState.single (μ := μ) b).progressToTrue := by
  have h0 : (1.0 : Float32) - (0.0 : Float32) = (1.0 : Float32) := by decide
  have h1 : (1.0 : Float32) - (1.0 : Float32) = (0.0 : Float32) := by decide
  cases b <;> simp [TargetState.not, TargetState.map, TargetState.progressToTrue, h0, h1]

theorem progressToTrue_not_inProgress_provisionalTrue_Impl {μ : Type}
    (c : Bool) (pr : Float32) (m : μ) :
    (TargetState.inProgress c true pr m).not.progressToTrue =
      (1.0 : Float32) - (TargetState.inProgress c true pr m).progressToTrue := by
  rfl

theorem progressToTrue_not_inProgress_provisionalFalse_Impl {μ : Type}
    (c : Bool) (pr : Float32) (m : μ) :
    (TargetState.inProgress c false pr m).progressToTrue =
      (1.0 : Float32) - (TargetState.inProgress c false pr m).not.progressToTrue := by
  rfl

theorem progressToTrue_not_exact_when_involution_Impl {μ : Type} (s : TargetState Bool μ)
    (hInv : ∀ c pr m, s = .inProgress c false pr m →
      (1.0 : Float32) - ((1.0 : Float32) - pr) = pr) :
    s.not.progressToTrue = (1.0 : Float32) - s.progressToTrue := by
  cases s with
  | single b => exact progressToTrue_not_single_Impl b
  | inProgress c p pr m =>
    cases p
    · exact (hInv c pr m rfl).symm
    · exact progressToTrue_not_inProgress_provisionalTrue_Impl c pr m

theorem map_id_Impl {α μ : Type} (s : TargetState α μ) :
    s.map id = s := by
  cases s <;> rfl

theorem map_comp_Impl {α β γ μ : Type} (s : TargetState α μ) (f : α → β) (g : β → γ) :
    (s.map f).map g = s.map (g ∘ f) := by
  cases s <;> rfl

theorem map_current_Impl {α β μ : Type} (s : TargetState α μ) (f : α → β) :
    (s.map f).current = f s.current := by
  cases s <;> rfl

theorem map_isInProgress_Impl {α β μ : Type} (s : TargetState α μ) (f : α → β) :
    (s.map f).isInProgress = s.isInProgress := by
  cases s <;> rfl

theorem mapChecked?_preserves_valid_Impl {α β μ : Type} [BEq β] [LawfulBEq β]
    (s : TargetState α μ) (f : α → β)
    (hValid : ∀ c p pr m, s = .inProgress c p pr m → f c ≠ f p) :
    s.mapChecked? f = some (s.map f) := by
  cases s with
  | single c => rfl
  | inProgress c p pr m =>
    have hne : f c ≠ f p := hValid c p pr m rfl
    have hbeq : (f c == f p) = false := beq_false_of_ne hne
    simp [TargetState.mapChecked?, TargetState.mkInProgress?, TargetState.map, hbeq]

end UiCommon.Model
