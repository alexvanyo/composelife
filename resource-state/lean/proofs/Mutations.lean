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

namespace ResourceState.Mutations

open ResourceState.Model

/-- Non-vacuity witness: a single failure among loading and success inputs is returned unwrapped. -/
theorem combineMany_single_failure_nonvacuous :
    ∃ states : List (ResourceState Nat),
      extractFailures states = [.named "io"] ∧
      combineMany states List.sum = .failure (.named "io") := by
  refine ⟨[.loading, .failure (.named "io"), .success 7], rfl, rfl⟩

/-- Non-vacuity witness: two failures produce `CompositeException` preserving order. -/
theorem combineMany_multi_failure_nonvacuous :
    ∃ states : List (ResourceState Nat),
      2 ≤ (extractFailures states).length ∧
      combineMany states List.sum =
        .failure (.composite [.named "first", .named "second"]) := by
  refine ⟨[.failure (.named "first"), .loading, .failure (.named "second")], by decide, rfl⟩

/-- Non-vacuity witness: loading with no failures yields `.loading`. -/
theorem combineMany_loading_nonvacuous :
    ∃ states : List (ResourceState Nat),
      extractFailures states = [] ∧
      hasLoading states = true ∧
      combineMany states List.sum = .loading := by
  refine ⟨[.success 1, .loading], rfl, rfl, rfl⟩

/-- Mutant 1: checking loading before failure violates failure-over-loading precedence. -/
def mutantCombineLoadingFirst {α β : Type} (states : List (ResourceState α))
    (transform : List α → β) : ResourceState β :=
  if hasLoading states then .loading
  else match extractFailures states with
    | [t] => .failure t
    | ts@(_ :: _ :: _) => .failure (.composite ts)
    | [] => .success (transform (extractSuccesses states))

theorem mutantCombineLoadingFirst_violates_failure_precedence :
    mutantCombineLoadingFirst [.loading, .failure (.named "boom")]
        (fun (_ : List Nat) => (0 : Nat)) ≠
      combineMany [.loading, .failure (.named "boom")]
        (fun (_ : List Nat) => (0 : Nat)) := by
  decide

/-- Mutant 2: wrapping a single failure in `CompositeException` violates single-failure unwrapping. -/
def mutantCombineAlwaysComposite {α β : Type} (states : List (ResourceState α))
    (transform : List α → β) : ResourceState β :=
  match extractFailures states with
  | [] =>
    if hasLoading states then .loading
    else .success (transform (extractSuccesses states))
  | ts => .failure (.composite ts)

theorem mutantCombineAlwaysComposite_violates_single_unwrapped :
    mutantCombineAlwaysComposite
        ([.failure (.named "err"), .success 1] : List (ResourceState Nat)) List.sum ≠
      combineMany
        ([.failure (.named "err"), .success 1] : List (ResourceState Nat)) List.sum := by
  decide

/-- Mutant 3: reversing failures in `CompositeException` violates failure order preservation. -/
def mutantCombineReverseFailures {α β : Type} (states : List (ResourceState α))
    (transform : List α → β) : ResourceState β :=
  match extractFailures states with
  | [t] => .failure t
  | ts@(_ :: _ :: _) => .failure (.composite ts.reverse)
  | [] =>
    if hasLoading states then .loading
    else .success (transform (extractSuccesses states))

theorem mutantCombineReverseFailures_violates_order :
    mutantCombineReverseFailures
        ([.failure (.named "a"), .failure (.named "b")] : List (ResourceState Nat)) List.sum ≠
      combineMany
        ([.failure (.named "a"), .failure (.named "b")] : List (ResourceState Nat)) List.sum := by
  decide

end ResourceState.Mutations
