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

import AlgorithmDefs
import models.GameOfLifeStepModel
import proofs.GameOfLifeStepModelProofs

namespace Algorithm.KotlinModel

/-!
# Formal Theorems About Hand-Written `GameOfLifeStep.kt` Model

Candidate soundness, the exact Conway B3/S23 rule (both as a neighbor-count
biconditional and as the shared specification `Algorithm.nextGenAt` on the
wrapping `Int` plane), empty fixpoint, 2×2 block still life, period-2 blinker
oscillator, and the non-positive/tailrec laws of `stepGenerations`.
-/

theorem stepGenerationModel_candidate_sound (alive : List (Int32 × Int32)) (c : Int32 × Int32)
    (hc : c ∈ stepGenerationModel alive) :
    c ∈ alive ∨ ∃ p ∈ alive, c ∈ mooreNeighbors32 p :=
  stepGenerationModel_candidate_sound_Impl alive c hc

theorem stepGenerationModel_conway_iff (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    c ∈ stepGenerationModel alive ↔
      neighborCountCoords alive c = 3 ∨
      (neighborCountCoords alive c = 2 ∧ c ∈ alive) :=
  stepGenerationModel_conway_iff_Impl alive c

/-- `stepGeneration` is Conway's B3/S23 rule `Algorithm.nextGenAt` on the plane of cells that `alive` covers,
where Kotlin's `Int` coordinates wrap: cell `(x, y)` of the plane is the `IntOffset` `(x.toInt(), y.toInt())`. -/
theorem mem_stepGenerationModel_iff_nextGenAt (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    c ∈ stepGenerationModel alive ↔
      Algorithm.nextGenAt (fun x y => decide ((Int32.ofInt x, Int32.ofInt y) ∈ alive)) c.1.toInt c.2.toInt = true :=
  mem_stepGenerationModel_iff_nextGenAt_Impl alive c

theorem stepGenerationModel_empty :
    stepGenerationModel [] = [] :=
  stepGenerationModel_empty_Impl

theorem stepGenerationsModel_nonpositive (alive : List (Int32 × Int32)) (step : Int32)
    (hs : step.toInt ≤ 0) :
    stepGenerationsModel alive step = alive :=
  stepGenerationsModel_nonpositive_Impl alive step hs

/-- The `tailrec` step of `stepGenerations`: a positive count runs one generation and recurses on `step - 1`. -/
theorem stepGenerationsModel_pos (alive : List (Int32 × Int32)) (step : Int32) (hs : 0 < step.toInt) :
    stepGenerationsModel alive step = stepGenerationsModel (stepGenerationModel alive) (step - 1) :=
  stepGenerationsModel_pos_Impl alive step hs

theorem stepGenerationsModel_succ (alive : List (Int32 × Int32)) (n : Nat) :
    stepGenerationsLoop (n + 1) alive = stepGenerationsLoop n (stepGenerationModel alive) :=
  stepGenerationsModel_succ_Impl alive n

theorem stepGenerationsModel_add (alive : List (Int32 × Int32)) (a b : Nat) :
    stepGenerationsLoop (a + b) alive = stepGenerationsLoop b (stepGenerationsLoop a alive) :=
  stepGenerationsModel_add_Impl alive a b

theorem stepGenerationModel_block :
    ∀ p, p ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] ↔
      p ∈ ([(0, 0), (1, 0), (0, 1), (1, 1)] : List (Int32 × Int32)) :=
  stepGenerationModel_block_Impl

theorem stepGenerationModel_blinker_period2 :
    ∀ p, p ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)] ↔
      p ∈ ([(0, 1), (1, 1), (2, 1)] : List (Int32 × Int32)) :=
  stepGenerationModel_blinker_period2_Impl

end Algorithm.KotlinModel
