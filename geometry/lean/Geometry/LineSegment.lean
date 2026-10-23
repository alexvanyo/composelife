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

import Init.Data.UInt

namespace Geometry

def absFloat (x : Float) : Float :=
  if x < 0.0 then -x else x

def absInt (x : Int32) : UInt32 :=
  if x < 0 then (-x).toUInt32 else x.toUInt32

def rayMarchLoop (fuel : UInt32) (startX startY : Float) (dx dy absDx absDy : Float)
    (stepX stepY : Int32) (endX endY : Int32) (curX curY : Int32) (acc : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
  if fuel == 0 then acc
  else if curX == endX && curY == endY then acc
  else
    let xb : Float := if stepX > 0 then (curX + 1).toFloat else curX.toFloat
    let yb : Float := if stepY > 0 then (curY + 1).toFloat else curY.toFloat
    if stepX == 0 then
      let remY := absFloat (yb - startY)
      if remY >= absDy then acc
      else
        let nextY := curY + stepY
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY (acc.push (curX, nextY))
    else if stepY == 0 then
      let remX := absFloat (xb - startX)
      if remX >= absDx then acc
      else
        let nextX := curX + stepX
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY (acc.push (nextX, curY))
    else
      let remX := absFloat (xb - startX)
      let remY := absFloat (yb - startY)
      let crossX := remX * absDy
      let crossY := remY * absDx
      let limitCross := absDx * absDy
      let minCross := if crossX < crossY then crossX else crossY
      if minCross >= limitCross then acc
      else
        let nextX := if crossX <= crossY then curX + stepX else curX
        let nextY := if crossY <= crossX then curY + stepY else curY
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY (acc.push (nextX, nextY))
termination_by fuel.toNat
decreasing_by
  all_goals
    have h_sub := UInt32.toNat_sub fuel 1
    have h1 : (1 : UInt32).toNat = 1 := rfl
    rw [h1] at h_sub
    have h_lt := UInt32.toNat_lt fuel
    have h_ne : fuel.toNat ≠ 0 := by
      intro hz
      have : fuel = 0 := by
        have : fuel.toNat = (0 : UInt32).toNat := by rw [hz]; rfl
        exact UInt32.toNat.inj this
      subst this
      contradiction
    have h_pos : 0 < fuel.toNat := Nat.pos_of_ne_zero h_ne
    rw [h_sub]
    have : (2 ^ 32 - 1 + fuel.toNat) = 2 ^ 32 + (fuel.toNat - 1) := by omega
    rw [this, Nat.add_mod_left]
    have : (fuel.toNat - 1) % 2 ^ 32 = fuel.toNat - 1 := by
      apply Nat.mod_eq_of_lt
      omega
    rw [this]
    omega

@[export geometry_ray_march_segment]
def rayMarchSegmentCoords (startX startY endX endY : Float) (startCellX startCellY endCellX endCellY : Int32) : Array (Int32 × Int32) :=
  if startCellX == endCellX && startCellY == endCellY then
    #[(startCellX, startCellY)]
  else
    let dx := endX - startX
    let dy := endY - startY
    let stepX : Int32 := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY : Int32 := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    let absDx := absFloat dx
    let absDy := absFloat dy
    let maxSteps := absInt (endCellX - startCellX) + absInt (endCellY - startCellY) + 2
    let acc := #[(startCellX, startCellY), (endCellX, endCellY)]
    rayMarchLoop maxSteps startX startY dx dy absDx absDy stepX stepY endCellX endCellY startCellX startCellY acc

end Geometry
