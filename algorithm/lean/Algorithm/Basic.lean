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

namespace Algorithm

abbrev Coord := Int × Int

def mooreOffsets : List (Int × Int) :=
  [ (-1, -1), (0, -1), (1, -1),
    (-1,  0),          (1,  0),
    (-1,  1), (0,  1), (1,  1) ]

def mooreNeighbors (c : Coord) : List Coord :=
  let (x, y) := c
  mooreOffsets.map (fun (dx, dy) => (x + dx, y + dy))

def countAliveNeighbors (c : Coord) (alive : List Coord) : Nat :=
  (mooreNeighbors c).filter (fun n => alive.contains n) |>.length

def lifeRule (isAlive : Bool) (neighborCount : Nat) : Bool :=
  neighborCount == 3 || (neighborCount == 2 && isAlive)

def deduplicate [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.concat x) []

def candidateCells (alive : List Coord) : List Coord :=
  let neighborCandidates := alive.flatMap mooreNeighbors
  deduplicate (alive ++ neighborCandidates)

def stepGrid (alive : List Coord) : List Coord :=
  let distinctAlive := deduplicate alive
  let candidates := candidateCells distinctAlive
  candidates.filter fun c =>
    let isAlive := distinctAlive.contains c
    let n := countAliveNeighbors c distinctAlive
    lifeRule isAlive n

def stepN : Nat → List Coord → List Coord
  | 0, s => deduplicate s
  | n + 1, s => stepGrid (stepN n s)

theorem stepN_zero (s : List Coord) : stepN 0 s = deduplicate s := rfl

theorem stepN_succ (n : Nat) (s : List Coord) : stepN (n + 1) s = stepGrid (stepN n s) := rfl

theorem stepGrid_empty : stepGrid [] = [] := by
  rfl

theorem stepN_empty (n : Nat) : stepN n [] = [] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [stepN, ih, stepGrid_empty]

end Algorithm
