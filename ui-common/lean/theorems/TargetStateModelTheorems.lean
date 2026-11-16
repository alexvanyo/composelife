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

import proofs.TargetStateModelProofs

namespace UiCommon.Model

theorem mkInProgress?_eq_none_iff {α μ : Type} [BEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) :
    TargetState.mkInProgress? current provisional progress metadata = none ↔
      (current == provisional) = true :=
  mkInProgress?_eq_none_iff_Impl current provisional progress metadata

theorem mkInProgress?_eq_some_iff {α μ : Type} [BEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) :
    TargetState.mkInProgress? current provisional progress metadata =
        some (.inProgress current provisional progress metadata) ↔
      (current == provisional) = false :=
  mkInProgress?_eq_some_iff_Impl current provisional progress metadata

theorem mkInProgress?_isValid {α μ : Type} [BEq α] [LawfulBEq α]
    (current provisional : α) (progress : Float32) (metadata : μ) (s : TargetState α μ)
    (hs : TargetState.mkInProgress? current provisional progress metadata = some s) :
    s.IsValid :=
  mkInProgress?_isValid_Impl current provisional progress metadata s hs

theorem isInProgress_dichotomy {α μ : Type} (s : TargetState α μ) :
    (s.isInProgress = false → ∃ c, s = .single c) ∧
      (s.isInProgress = true → ∃ c p pr m, s = .inProgress c p pr m) :=
  isInProgress_dichotomy_Impl s

theorem and_false {μ : Type} (s : TargetState Bool μ) :
    s.and false = .single false :=
  and_false_Impl s

theorem and_true {μ : Type} (s : TargetState Bool μ) :
    s.and true = s :=
  and_true_Impl s

theorem or_true {μ : Type} (s : TargetState Bool μ) :
    s.or true = .single true :=
  or_true_Impl s

theorem or_false {μ : Type} (s : TargetState Bool μ) :
    s.or false = s :=
  or_false_Impl s

theorem not_not {μ : Type} (s : TargetState Bool μ) :
    s.not.not = s :=
  not_not_Impl s

theorem not_current {μ : Type} (s : TargetState Bool μ) :
    s.not.current = !s.current :=
  not_current_Impl s

theorem progressToTrue_not_single {μ : Type} (b : Bool) :
    (TargetState.single (μ := μ) b).not.progressToTrue =
      (1.0 : Float32) - (TargetState.single (μ := μ) b).progressToTrue :=
  progressToTrue_not_single_Impl b

theorem progressToTrue_not_inProgress_provisionalTrue {μ : Type}
    (c : Bool) (pr : Float32) (m : μ) :
    (TargetState.inProgress c true pr m).not.progressToTrue =
      (1.0 : Float32) - (TargetState.inProgress c true pr m).progressToTrue :=
  progressToTrue_not_inProgress_provisionalTrue_Impl c pr m

theorem progressToTrue_not_inProgress_provisionalFalse {μ : Type}
    (c : Bool) (pr : Float32) (m : μ) :
    (TargetState.inProgress c false pr m).progressToTrue =
      (1.0 : Float32) - (TargetState.inProgress c false pr m).not.progressToTrue :=
  progressToTrue_not_inProgress_provisionalFalse_Impl c pr m

theorem progressToTrue_not_exact_when_involution {μ : Type} (s : TargetState Bool μ)
    (hInv : ∀ c pr m, s = .inProgress c false pr m →
      (1.0 : Float32) - ((1.0 : Float32) - pr) = pr) :
    s.not.progressToTrue = (1.0 : Float32) - s.progressToTrue :=
  progressToTrue_not_exact_when_involution_Impl s hInv

theorem map_id {α μ : Type} (s : TargetState α μ) :
    s.map id = s :=
  map_id_Impl s

theorem map_comp {α β γ μ : Type} (s : TargetState α μ) (f : α → β) (g : β → γ) :
    (s.map f).map g = s.map (g ∘ f) :=
  map_comp_Impl s f g

theorem map_current {α β μ : Type} (s : TargetState α μ) (f : α → β) :
    (s.map f).current = f s.current :=
  map_current_Impl s f

theorem map_isInProgress {α β μ : Type} (s : TargetState α μ) (f : α → β) :
    (s.map f).isInProgress = s.isInProgress :=
  map_isInProgress_Impl s f

theorem mapChecked?_preserves_valid {α β μ : Type} [BEq β] [LawfulBEq β]
    (s : TargetState α μ) (f : α → β)
    (hValid : ∀ c p pr m, s = .inProgress c p pr m → f c ≠ f p) :
    s.mapChecked? f = some (s.map f) :=
  mapChecked?_preserves_valid_Impl s f hValid

end UiCommon.Model
