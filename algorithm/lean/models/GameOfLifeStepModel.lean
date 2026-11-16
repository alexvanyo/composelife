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

namespace Algorithm.KotlinModel

/-!
# Standalone Mathematical Model of Hand-Written `GameOfLifeStep.kt`

Pure Lean 4 specification modeling `stepGeneration` and `stepGenerations`
over packed `(Int32 × Int32)` (`IntOffset`) coordinate lists and B3/S23 rules.
-/

def mooreDeltas32 : List (Int32 × Int32) :=
  [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]

def addOffset32 (a b : Int32 × Int32) : Int32 × Int32 :=
  (a.1 + b.1, a.2 + b.2)

def mooreNeighbors32 (p : Int32 × Int32) : List (Int32 × Int32) :=
  mooreDeltas32.map (addOffset32 p)

def dedupCoords (xs : List (Int32 × Int32)) : List (Int32 × Int32) :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def neighborCountCoords (alive : List (Int32 × Int32)) (p : Int32 × Int32) : Nat :=
  let a := dedupCoords alive
  ((mooreNeighbors32 p).filter fun n => a.contains n).length

def stepGenerationModel (alive : List (Int32 × Int32)) : List (Int32 × Int32) :=
  let a := dedupCoords alive
  let candidates := dedupCoords ((a.flatMap mooreNeighbors32) ++ a)
  candidates.filter fun c =>
    let count := ((mooreNeighbors32 c).filter fun n => a.contains n).length
    count == 3 || (count == 2 && a.contains c)

def stepGenerationsLoop (n : Nat) (alive : List (Int32 × Int32)) : List (Int32 × Int32) :=
  match n with
  | 0 => alive
  | k + 1 => stepGenerationsLoop k (stepGenerationModel alive)

def stepGenerationsModel (alive : List (Int32 × Int32)) (step : Int32) : List (Int32 × Int32) :=
  if step.toInt ≤ 0 then alive
  else stepGenerationsLoop step.toInt.toNat alive

end Algorithm.KotlinModel
