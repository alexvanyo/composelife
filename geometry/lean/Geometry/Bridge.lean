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

namespace Geometry

@[export geometry_cell_intersections_segment]
def oracleCellIntersectionsSegment (x1 y1 x2 y2 : Float) : Array (Int × Int) :=
  let cells := cellIntersectionsSegment ⟨x1, y1⟩ ⟨x2, y2⟩
  (cells.map (fun c => (c.x, c.y))).toArray

def pointsFromFloatArray (coords : Array Float) : List Point :=
  let n := coords.size / 2
  let rec loop (i : Nat) (acc : List Point) : List Point :=
    if i >= n then acc.reverse
    else
      let p : Point := ⟨coords[2 * i]!, coords[2 * i + 1]!⟩
      loop (i + 1) (p :: acc)
  loop 0 []

@[export geometry_cell_intersections_path]
def oracleCellIntersectionsPath (coords : Array Float) : Array (Int × Int) :=
  let points := pointsFromFloatArray coords
  let cells := cellIntersectionsPath points
  (cells.map (fun c => (c.x, c.y))).toArray

end Geometry
