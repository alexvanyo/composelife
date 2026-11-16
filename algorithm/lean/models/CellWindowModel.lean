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
# Standalone Mathematical Model of Hand-Written `CellWindow.kt`

Models the value class `CellWindow(intRect : IntRect)` with constructor
invariant `top ≤ bottom ∧ left ≤ right`, dimension getters, translation, and
row-major `containedPoints`.
-/

structure CellWindowModel where
  left : Int32
  top : Int32
  right : Int32
  bottom : Int32
  deriving DecidableEq, Repr

def isValidCellWindow (left top right bottom : Int32) : Bool :=
  top ≤ bottom && left ≤ right

def mkCellWindowModel (left top right bottom : Int32) : Option CellWindowModel :=
  if isValidCellWindow left top right bottom then
    some ⟨left, top, right, bottom⟩
  else
    none

def CellWindowModel.width (w : CellWindowModel) : Int32 :=
  w.right - w.left

def CellWindowModel.height (w : CellWindowModel) : Int32 :=
  w.bottom - w.top

def CellWindowModel.translate (w : CellWindowModel) (dx dy : Int32) : Option CellWindowModel :=
  mkCellWindowModel (w.left + dx) (w.top + dy) (w.right + dx) (w.bottom + dy)

def int32RangeUntil (start stop : Int32) : List Int32 :=
  if stop ≤ start then []
  else
    let n := (stop.toInt - start.toInt).toNat
    (List.range n).map fun k => Int32.ofInt (start.toInt + Int.ofNat k)

def CellWindowModel.containedPoints (w : CellWindowModel) : List (Int32 × Int32) :=
  (int32RangeUntil w.top w.bottom).flatMap fun y =>
    (int32RangeUntil w.left w.right).map fun x => (x, y)

end Algorithm.KotlinModel
