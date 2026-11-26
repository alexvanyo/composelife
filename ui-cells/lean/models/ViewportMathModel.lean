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

namespace UiCells.Model

/-- Model of a closed range `[lo, hi]` over an ordered domain (`ClosedRange<Float>`). -/
structure FloatRangeModel where
  lo : Float32
  hi : Float32
  deriving DecidableEq, Repr

/-- `ClosedRange.isEmpty()` returns `true` iff `lo > hi` (or `!(lo ≤ hi)`). -/
def FloatRangeModel.isEmpty (r : FloatRangeModel) : Bool :=
  !(r.lo <= r.hi)

/-- Clamp `x` into `[r.lo, r.hi]` (`coerceIn` on a non-empty range). -/
def coerceInFloatRange (x : Float32) (r : FloatRangeModel) : Float32 :=
  if x < r.lo then r.lo
  else if r.hi < x then r.hi
  else x

/-- Exact integer affine grid anchor map `anchor ↦ (anchor - origin) * scale` (`GridDraggableAnchors2d`). -/
def gridAnchorPos (origin scale anchor : Int) : Int :=
  (anchor - origin) * scale

/-- Exact inverse `pos ↦ pos / scale + origin` (`GridDraggableAnchors2d.closestAnchor`). -/
def gridAnchorClosest (origin scale pos : Int) : Int :=
  pos / scale + origin

/-- Model of `MutableCellWindowViewportStateImpl.setScaleRange(value)`: rejects empty `value`. -/
def setScaleRangeModel (curScale : Float32) (newRange : FloatRangeModel) : Option (FloatRangeModel × Float32) :=
  if newRange.isEmpty then none
  else some (newRange, coerceInFloatRange curScale newRange)

end UiCells.Model
