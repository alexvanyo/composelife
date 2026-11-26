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

namespace Geometry.KotlinModel

/-- Model of Compose `LayoutDirection` (`Ltr` / `Rtl`). -/
inductive LayoutDirectionModel where
  | ltr
  | rtl
  deriving DecidableEq, Repr

/-- Flip `Ltr ↔ Rtl`. -/
def LayoutDirectionModel.flip : LayoutDirectionModel → LayoutDirectionModel
  | .ltr => .rtl
  | .rtl => .ltr

/-- Six anchor points of a Compose `Rect` (packed `Offset`s) or `IntRect` (packed `IntOffset`s). -/
structure RectCorners where
  topLeft : UInt64
  topRight : UInt64
  centerLeft : UInt64
  centerRight : UInt64
  bottomLeft : UInt64
  bottomRight : UInt64
  deriving DecidableEq, Repr

def RectCorners.topStart (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.topLeft
  | .rtl => r.topRight

def RectCorners.topEnd (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.topRight
  | .rtl => r.topLeft

def RectCorners.centerStart (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.centerLeft
  | .rtl => r.centerRight

def RectCorners.centerEnd (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.centerRight
  | .rtl => r.centerLeft

def RectCorners.bottomStart (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.bottomLeft
  | .rtl => r.bottomRight

def RectCorners.bottomEnd (r : RectCorners) : LayoutDirectionModel → UInt64
  | .ltr => r.bottomRight
  | .rtl => r.bottomLeft

/-- Pack signed 32-bit `(width, height)` into Compose `IntSize` (`Long`). -/
def packIntSize (w h : Int32) : UInt64 :=
  (w.toUInt32.toUInt64 <<< 32) ||| h.toUInt32.toUInt64

/-- Unpack `width` from Compose `IntSize` (`Long`). -/
def intSizeWidth (packed : UInt64) : Int32 :=
  (packed >>> 32).toUInt32.toInt32

/-- Unpack `height` from Compose `IntSize` (`Long`). -/
def intSizeHeight (packed : UInt64) : Int32 :=
  packed.toUInt32.toInt32

/-- Standalone model of `lerp(IntSize, IntSize, Float)` in `IntSizeLerp.kt`. -/
def lerpIntSizeModel (lerpInt : Int32 → Int32 → Float32 → Int32)
    (start stop : UInt64) (fraction : Float32) : UInt64 :=
  packIntSize
    (lerpInt (intSizeWidth start) (intSizeWidth stop) fraction)
    (lerpInt (intSizeHeight start) (intSizeHeight stop) fraction)

end Geometry.KotlinModel
