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

import models.ResourceStateModel

namespace ResourceState.Model

theorem resourceState_partition_exclusive_Impl {α : Type} (r : ResourceState α) :
    (r.isLoading = true ∧ r.isSuccess = false ∧ r.isFailure = false) ∨
    (r.isLoading = false ∧ r.isSuccess = true ∧ r.isFailure = false) ∨
    (r.isLoading = false ∧ r.isSuccess = false ∧ r.isFailure = true) := by
  cases r with
  | loading => exact Or.inl ⟨rfl, rfl, rfl⟩
  | success _ => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  | failure _ => exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

theorem resourceState_isLoading_iff_Impl {α : Type} (r : ResourceState α) :
    r.isLoading = true ↔ r = .loading := by
  cases r <;> simp [ResourceState.isLoading]

theorem resourceState_isSuccess_iff_Impl {α : Type} (r : ResourceState α) :
    r.isSuccess = true ↔ ∃ v, r = .success v := by
  cases r <;> simp [ResourceState.isSuccess]

theorem resourceState_isFailure_iff_Impl {α : Type} (r : ResourceState α) :
    r.isFailure = true ↔ ∃ t, r = .failure t := by
  cases r <;> simp [ResourceState.isFailure]

theorem resourceState_map_id_Impl {α : Type} (r : ResourceState α) :
    ResourceState.map id r = r := by
  cases r <;> rfl

theorem resourceState_map_comp_Impl {α β γ : Type} (f : α → β) (g : β → γ)
    (r : ResourceState α) :
    ResourceState.map g (ResourceState.map f r) = ResourceState.map (fun x => g (f x)) r := by
  cases r <;> rfl

theorem resourceState_flatMap_left_id_Impl {α β : Type} (x : α) (f : α → ResourceState β) :
    ResourceState.flatMap f (.success x) = f x := rfl

theorem resourceState_flatMap_right_id_Impl {α : Type} (r : ResourceState α) :
    ResourceState.flatMap ResourceState.success r = r := by
  cases r <;> rfl

theorem resourceState_flatMap_assoc_Impl {α β γ : Type} (r : ResourceState α)
    (f : α → ResourceState β) (g : β → ResourceState γ) :
    ResourceState.flatMap g (ResourceState.flatMap f r) =
      ResourceState.flatMap (fun x => ResourceState.flatMap g (f x)) r := by
  cases r <;> rfl

theorem resourceState_flatMap_loading_Impl {α β : Type} (f : α → ResourceState β) :
    ResourceState.flatMap f .loading = .loading := rfl

theorem resourceState_flatMap_failure_Impl {α β : Type} (t : ThrowableModel)
    (f : α → ResourceState β) :
    ResourceState.flatMap f (.failure t) = .failure t := rfl

theorem combineMany_single_failure_unwrapped_Impl {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β) (t : ThrowableModel)
    (hfail : extractFailures states = [t]) :
    combineMany states transform = .failure t := by
  simp [combineMany, hfail]

theorem combineMany_multi_failure_composite_Impl {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hlen : 2 ≤ (extractFailures states).length) :
    combineMany states transform = .failure (.composite (extractFailures states)) := by
  unfold combineMany
  cases hf : extractFailures states with
  | nil => simp [hf] at hlen
  | cons t1 rest =>
    cases rest with
    | nil => simp [hf] at hlen
    | cons t2 tail => rfl

theorem combineMany_loading_when_no_failure_Impl {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hnofail : extractFailures states = []) (hload : hasLoading states = true) :
    combineMany states transform = .loading := by
  simp [combineMany, hnofail, hload]

private theorem extractFailures_map_success {α : Type} (vals : List α) :
    extractFailures (vals.map ResourceState.success) = [] := by
  induction vals with
  | nil => rfl
  | cons _ _ ih => simp [extractFailures]

private theorem hasLoading_map_success {α : Type} (vals : List α) :
    hasLoading (vals.map ResourceState.success) = false := by
  induction vals with
  | nil => rfl
  | cons _ _ ih => simp [hasLoading]

private theorem extractSuccesses_map_success {α : Type} (vals : List α) :
    extractSuccesses (vals.map ResourceState.success) = vals := by
  induction vals with
  | nil => rfl
  | cons v vs ih =>
    change v :: extractSuccesses (vs.map ResourceState.success) = v :: vs
    rw [ih]

theorem combineMany_all_success_Impl {α β : Type} (vals : List α) (transform : List α → β) :
    combineMany (vals.map ResourceState.success) transform = .success (transform vals) := by
  simp [combineMany, extractFailures_map_success, hasLoading_map_success,
    extractSuccesses_map_success]

theorem combineMany_no_failure_no_loading_Impl {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hnofail : extractFailures states = []) (hnoload : hasLoading states = false) :
    (extractSuccesses states).length = states.length ∧
      combineMany states transform = .success (transform (extractSuccesses states)) := by
  constructor
  · induction states with
    | nil => rfl
    | cons s ss ih =>
      cases s with
      | loading => simp [hasLoading] at hnoload
      | success v =>
        simp only [extractFailures] at hnofail
        simp only [hasLoading, List.any_cons, Bool.false_or] at hnoload
        simp only [extractSuccesses, List.filterMap_cons, List.length_cons]
        have hih := ih hnofail hnoload
        simp only [extractSuccesses] at hih
        omega
      | failure t => simp [extractFailures] at hnofail
  · simp [combineMany, hnofail, hnoload]

theorem combineMany_nil_Impl {α β : Type} (transform : List α → β) :
    combineMany ([] : List (ResourceState α)) transform = .success (transform []) := rfl

theorem combine2_matches_combineMany_Impl {α β : Type}
    (r1 r2 : ResourceState α) (transform : List α → β) :
    combine2 r1 r2 (fun a b => transform [a, b]) = combineMany [r1, r2] transform := by
  cases r1 <;> cases r2 <;> rfl

theorem combine3_matches_combineMany_Impl {α β : Type}
    (r1 r2 r3 : ResourceState α) (transform : List α → β) :
    combine3 r1 r2 r3 (fun a b c => transform [a, b, c]) = combineMany [r1, r2, r3] transform := by
  cases r1 <;> cases r2 <;> cases r3 <;> rfl

theorem combine2_both_failure_composite_Impl {α β γ : Type}
    (t1 t2 : ThrowableModel) (transform : α → β → γ) :
    combine2 (.failure t1 : ResourceState α) (.failure t2 : ResourceState β) transform =
      .failure (.composite [t1, t2]) := rfl

theorem combine2_left_failure_unwrapped_Impl {α β γ : Type}
    (t1 : ThrowableModel) (r2 : ResourceState β) (h2 : r2.isFailure = false)
    (transform : α → β → γ) :
    combine2 (.failure t1 : ResourceState α) r2 transform = .failure t1 := by
  cases r2 <;> simp_all [combine2, ResourceState.isFailure]

theorem combine2_right_failure_unwrapped_Impl {α β γ : Type}
    (r1 : ResourceState α) (t2 : ThrowableModel) (h1 : r1.isFailure = false)
    (transform : α → β → γ) :
    combine2 r1 (.failure t2 : ResourceState β) transform = .failure t2 := by
  cases r1 <;> simp_all [combine2, ResourceState.isFailure]

theorem combine2_all_success_Impl {α β γ : Type}
    (a : α) (b : β) (transform : α → β → γ) :
    combine2 (.success a) (.success b) transform = .success (transform a b) := rfl

theorem combine3_all_success_Impl {α β γ δ : Type}
    (a : α) (b : β) (c : γ) (transform : α → β → γ → δ) :
    combine3 (.success a) (.success b) (.success c) transform = .success (transform a b c) := rfl

theorem asResourceStateFlow_success_only_Impl {α : Type} (elems : List α) :
    asResourceStateFlow { emissions := elems, terminalFailure? := none } =
      { emissions := elems.map ResourceState.success, terminalFailure? := none } := rfl

theorem asResourceStateFlow_catches_failure_Impl {α : Type} (elems : List α) (t : ThrowableModel) :
    asResourceStateFlow { emissions := elems, terminalFailure? := some t } =
      { emissions := elems.map ResourceState.success ++ [.failure t], terminalFailure? := none } := rfl

theorem collectAsStateModel_empty_is_loading_Impl {α : Type} (err? : Option ThrowableModel) :
    collectAsStateModel ({ emissions := [], terminalFailure? := err? } : FlowTrace (ResourceState α)) =
      .loading := rfl

theorem firstSuccessModel_skips_loading_and_failure_Impl {α : Type}
    (v : α) (rest : List (ResourceState α)) (err? : Option ThrowableModel) :
    firstSuccessModel
        ({ emissions := .loading :: .failure (.named "err") :: .success v :: rest,
           terminalFailure? := err? }) =
      some (.success v) := rfl

end ResourceState.Model
