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

import Geometry.Basic
import Geometry.LineSegment

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Geometry

def float32ToRat (f : Float32) : ℚ :=
  let n := f.toBits.toNat
  let sign : ℚ := if n / (2^31) != 0 then -1 else 1
  let exp : ℕ := (n / (2^23)) % (2^8)
  let frac : ℕ := n % (2^23)
  if exp == 0 then
    if frac == 0 then 0
    else sign * (Rat.ofInt frac) / (Rat.ofInt (2^149))
  else if exp == 255 then
    0
  else
    let mantissa : ℚ := Rat.ofInt (frac + 2^23)
    let shift : ℤ := (exp : ℤ) - 127 - 23
    if shift >= 0 then
      sign * mantissa * (Rat.ofInt (2^(shift.toNat)))
    else
      sign * mantissa / (Rat.ofInt (2^((-shift).toNat)))

@[export geometry_cell_intersections_segment]
def oracleCellIntersectionsSegment (x1 y1 x2 y2 : Float32) : Array (ℤ × ℤ) :=
  let p1 : Point := ⟨float32ToRat x1, float32ToRat y1⟩
  let p2 : Point := ⟨float32ToRat x2, float32ToRat y2⟩
  let cells := cellIntersectionsSegment p1 p2
  (cells.map (fun c => (c.x, c.y))).toArray

def pointsFromFloatArray (coords : Array Float32) : List Point :=
  let n := coords.size / 2
  let rec loop (i : ℕ) (acc : List Point) : List Point :=
    if i >= n then acc.reverse
    else
      let p : Point := ⟨float32ToRat coords[2 * i]!, float32ToRat coords[2 * i + 1]!⟩
      loop (i + 1) (p :: acc)
  loop 0 []

@[export geometry_cell_intersections_path]
def oracleCellIntersectionsPath (coords : Array Float32) : Array (ℤ × ℤ) :=
  let points := pointsFromFloatArray coords
  let cells := cellIntersectionsPath points
  (cells.map (fun c => (c.x, c.y))).toArray

end Geometry
