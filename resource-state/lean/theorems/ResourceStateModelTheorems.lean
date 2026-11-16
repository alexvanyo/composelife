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

import proofs.ResourceStateModelProofs

namespace ResourceState.Model

theorem resourceState_partition_exclusive {α : Type} (r : ResourceState α) :
    (r.isLoading = true ∧ r.isSuccess = false ∧ r.isFailure = false) ∨
    (r.isLoading = false ∧ r.isSuccess = true ∧ r.isFailure = false) ∨
    (r.isLoading = false ∧ r.isSuccess = false ∧ r.isFailure = true) :=
  resourceState_partition_exclusive_Impl r

theorem resourceState_isLoading_iff {α : Type} (r : ResourceState α) :
    r.isLoading = true ↔ r = .loading :=
  resourceState_isLoading_iff_Impl r

theorem resourceState_isSuccess_iff {α : Type} (r : ResourceState α) :
    r.isSuccess = true ↔ ∃ v, r = .success v :=
  resourceState_isSuccess_iff_Impl r

theorem resourceState_isFailure_iff {α : Type} (r : ResourceState α) :
    r.isFailure = true ↔ ∃ t, r = .failure t :=
  resourceState_isFailure_iff_Impl r

theorem resourceState_map_id {α : Type} (r : ResourceState α) :
    ResourceState.map id r = r :=
  resourceState_map_id_Impl r

theorem resourceState_map_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (r : ResourceState α) :
    ResourceState.map g (ResourceState.map f r) = ResourceState.map (fun x => g (f x)) r :=
  resourceState_map_comp_Impl f g r

theorem resourceState_flatMap_left_id {α β : Type} (x : α) (f : α → ResourceState β) :
    ResourceState.flatMap f (.success x) = f x :=
  resourceState_flatMap_left_id_Impl x f

theorem resourceState_flatMap_right_id {α : Type} (r : ResourceState α) :
    ResourceState.flatMap ResourceState.success r = r :=
  resourceState_flatMap_right_id_Impl r

theorem resourceState_flatMap_assoc {α β γ : Type} (r : ResourceState α)
    (f : α → ResourceState β) (g : β → ResourceState γ) :
    ResourceState.flatMap g (ResourceState.flatMap f r) =
      ResourceState.flatMap (fun x => ResourceState.flatMap g (f x)) r :=
  resourceState_flatMap_assoc_Impl r f g

theorem resourceState_flatMap_loading {α β : Type} (f : α → ResourceState β) :
    ResourceState.flatMap f .loading = .loading :=
  resourceState_flatMap_loading_Impl f

theorem resourceState_flatMap_failure {α β : Type} (t : ThrowableModel)
    (f : α → ResourceState β) :
    ResourceState.flatMap f (.failure t) = .failure t :=
  resourceState_flatMap_failure_Impl t f

theorem combineMany_single_failure_unwrapped {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β) (t : ThrowableModel)
    (hfail : extractFailures states = [t]) :
    combineMany states transform = .failure t :=
  combineMany_single_failure_unwrapped_Impl states transform t hfail

theorem combineMany_multi_failure_composite {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hlen : 2 ≤ (extractFailures states).length) :
    combineMany states transform = .failure (.composite (extractFailures states)) :=
  combineMany_multi_failure_composite_Impl states transform hlen

theorem combineMany_loading_when_no_failure {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hnofail : extractFailures states = []) (hload : hasLoading states = true) :
    combineMany states transform = .loading :=
  combineMany_loading_when_no_failure_Impl states transform hnofail hload

theorem combineMany_all_success {α β : Type} (vals : List α) (transform : List α → β) :
    combineMany (vals.map ResourceState.success) transform = .success (transform vals) :=
  combineMany_all_success_Impl vals transform

theorem combineMany_no_failure_no_loading {α β : Type}
    (states : List (ResourceState α)) (transform : List α → β)
    (hnofail : extractFailures states = []) (hnoload : hasLoading states = false) :
    (extractSuccesses states).length = states.length ∧
      combineMany states transform = .success (transform (extractSuccesses states)) :=
  combineMany_no_failure_no_loading_Impl states transform hnofail hnoload

theorem combineMany_nil {α β : Type} (transform : List α → β) :
    combineMany ([] : List (ResourceState α)) transform = .success (transform []) :=
  combineMany_nil_Impl transform

theorem combine2_matches_combineMany {α β : Type}
    (r1 r2 : ResourceState α) (transform : List α → β) :
    combine2 r1 r2 (fun a b => transform [a, b]) = combineMany [r1, r2] transform :=
  combine2_matches_combineMany_Impl r1 r2 transform

theorem combine3_matches_combineMany {α β : Type}
    (r1 r2 r3 : ResourceState α) (transform : List α → β) :
    combine3 r1 r2 r3 (fun a b c => transform [a, b, c]) = combineMany [r1, r2, r3] transform :=
  combine3_matches_combineMany_Impl r1 r2 r3 transform

theorem combine2_both_failure_composite {α β γ : Type}
    (t1 t2 : ThrowableModel) (transform : α → β → γ) :
    combine2 (.failure t1 : ResourceState α) (.failure t2 : ResourceState β) transform =
      .failure (.composite [t1, t2]) :=
  combine2_both_failure_composite_Impl t1 t2 transform

theorem combine2_left_failure_unwrapped {α β γ : Type}
    (t1 : ThrowableModel) (r2 : ResourceState β) (h2 : r2.isFailure = false)
    (transform : α → β → γ) :
    combine2 (.failure t1 : ResourceState α) r2 transform = .failure t1 :=
  combine2_left_failure_unwrapped_Impl t1 r2 h2 transform

theorem combine2_right_failure_unwrapped {α β γ : Type}
    (r1 : ResourceState α) (t2 : ThrowableModel) (h1 : r1.isFailure = false)
    (transform : α → β → γ) :
    combine2 r1 (.failure t2 : ResourceState β) transform = .failure t2 :=
  combine2_right_failure_unwrapped_Impl r1 t2 h1 transform

theorem combine2_all_success {α β γ : Type}
    (a : α) (b : β) (transform : α → β → γ) :
    combine2 (.success a) (.success b) transform = .success (transform a b) :=
  combine2_all_success_Impl a b transform

theorem combine3_all_success {α β γ δ : Type}
    (a : α) (b : β) (c : γ) (transform : α → β → γ → δ) :
    combine3 (.success a) (.success b) (.success c) transform = .success (transform a b c) :=
  combine3_all_success_Impl a b c transform

theorem asResourceStateFlow_success_only {α : Type} (elems : List α) :
    asResourceStateFlow { emissions := elems, terminalFailure? := none } =
      { emissions := elems.map ResourceState.success, terminalFailure? := none } :=
  asResourceStateFlow_success_only_Impl elems

theorem asResourceStateFlow_catches_failure {α : Type} (elems : List α) (t : ThrowableModel) :
    asResourceStateFlow { emissions := elems, terminalFailure? := some t } =
      { emissions := elems.map ResourceState.success ++ [.failure t], terminalFailure? := none } :=
  asResourceStateFlow_catches_failure_Impl elems t

theorem collectAsStateModel_empty_is_loading {α : Type} (err? : Option ThrowableModel) :
    collectAsStateModel ({ emissions := [], terminalFailure? := err? } : FlowTrace (ResourceState α)) =
      .loading :=
  collectAsStateModel_empty_is_loading_Impl err?

theorem firstSuccessModel_skips_loading_and_failure {α : Type}
    (v : α) (rest : List (ResourceState α)) (err? : Option ThrowableModel) :
    firstSuccessModel
        ({ emissions := .loading :: .failure (.named "err") :: .success v :: rest,
           terminalFailure? := err? }) =
      some (.success v) :=
  firstSuccessModel_skips_loading_and_failure_Impl v rest err?

end ResourceState.Model
