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

namespace Geometry

/--
A continuous 2D point with 64-bit floating point coordinates.
-/
structure Point where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/--
A discrete 2D integer cell coordinate representing the unit cell [x, x+1] x [y, y+1].
-/
structure Cell where
  x : Int
  y : Int
  deriving Repr, Inhabited, DecidableEq, BEq, Hashable

theorem cell_beq_def (a b : Cell) : (a == b) = (a.x == b.x && a.y == b.y) := rfl

instance : LawfulBEq Cell where
  eq_of_beq {a b} h := by
    rw [cell_beq_def] at h
    have h1 : (a.x == b.x) = true := by
      revert h
      cases a.x == b.x <;> simp
    have h2 : (a.y == b.y) = true := by
      revert h
      cases a.x == b.x <;> cases a.y == b.y <;> simp
    have hx : a.x = b.x := eq_of_beq h1
    have hy : a.y = b.y := eq_of_beq h2
    cases a; cases b
    simp only at hx hy
    rw [hx, hy]
  rfl {a} := by
    rw [cell_beq_def]
    simp

/--
Converts a Float to an Int by taking the floor and casting.
-/
def toInt (f : Float) : Int :=
  let fl := f.floor
  if fl >= 0.0 then
    Int.ofNat fl.toUInt64.toNat
  else
    -Int.ofNat (-fl).toUInt64.toNat

/--
Rounds a Float to the nearest Int (ties round up), matching Kotlin's roundToInt().
-/
def roundToInt (f : Float) : Int :=
  toInt (f + 0.5)

/--
Floors a continuous Point into discrete Cell coordinates.
-/
def floorPoint (p : Point) : Cell :=
  ⟨toInt p.x, toInt p.y⟩

/--
Returns 1.0 if positive, -1.0 if negative, and 0.0 otherwise.
-/
def sign (f : Float) : Float :=
  if f > 0.0 then 1.0
  else if f < 0.0 then -1.0
  else 0.0

/--
Determines which side of the directed line from `start` to `ptEnd` the point `p` lies on.
Returns 1.0 for right, -1.0 for left, and 0.0 for collinear.
-/
def sideOfLine (p start ptEnd : Point) : Float :=
  sign ((ptEnd.x - start.x) * (p.y - start.y) - (ptEnd.y - start.y) * (p.x - start.x))

/--
Calculates the Chebyshev (L_infinity) distance between two cells.
-/
def chebyshevDistance (a b : Cell) : Nat :=
  max (a.x - b.x).natAbs (a.y - b.y).natAbs

/--
Calculates the Manhattan (L_1) distance between two cells.
-/
def manhattanDistance (a b : Cell) : Nat :=
  (a.x - b.x).natAbs + (a.y - b.y).natAbs

end Geometry
