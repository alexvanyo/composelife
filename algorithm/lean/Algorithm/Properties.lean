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

import Algorithm.Basic

namespace Algorithm

def translateGrid (dx dy : Int) (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (x + dx, y + dy))

def flipXGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (x, -y))

def flipYGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (-x, y))

def flipDiagGrid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (y, x))

def rotate90Grid (s : List Coord) : List Coord :=
  s.map (fun (x, y) => (-y, x))

def chebyshevDist (c1 c2 : Coord) : Nat :=
  max (c1.1 - c2.1).natAbs (c1.2 - c2.2).natAbs

def manhattanDist (c1 c2 : Coord) : Nat :=
  (c1.1 - c2.1).natAbs + (c1.2 - c2.2).natAbs

def cellsEqual (a b : List Coord) : Bool :=
  let da := deduplicate a
  let db := deduplicate b
  da.all (db.contains ·) && db.all (da.contains ·)

theorem stepN_composition_step (n : Nat) (s : List Coord) :
  stepN (n + 1) s = stepGrid (stepN n s) := rfl

theorem extinction_stability (n : Nat) :
  stepN n [] = [] := stepN_empty n

theorem blinker_translation_commutes :
  let b := [(0, 1), (1, 1), (2, 1)]
  let tb := translateGrid 157 72 b
  cellsEqual (stepGrid tb) (translateGrid 157 72 (stepGrid b)) = true := by
  decide

theorem blinker_flipX_commutes :
  let b := [(0, 1), (1, 1), (2, 1)]
  cellsEqual (stepGrid (flipXGrid b)) (flipXGrid (stepGrid b)) = true := by
  decide

theorem blinker_flipY_commutes :
  let b := [(0, 1), (1, 1), (2, 1)]
  cellsEqual (stepGrid (flipYGrid b)) (flipYGrid (stepGrid b)) = true := by
  decide

theorem blinker_flipDiag_commutes :
  let b := [(0, 1), (1, 1), (2, 1)]
  cellsEqual (stepGrid (flipDiagGrid b)) (flipDiagGrid (stepGrid b)) = true := by
  decide

theorem glider_translation_commutes :
  let g := [(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]
  let tg := translateGrid 157 72 g
  cellsEqual (stepGrid tg) (translateGrid 157 72 (stepGrid g)) = true := by
  decide

end Algorithm
