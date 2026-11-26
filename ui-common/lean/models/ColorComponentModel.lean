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

namespace UiCommon.KotlinModel

/-- RGB integer color channel (`ColorComponent.RgbIntComponent`). -/
inductive RgbComponent where
  | red
  | green
  | blue
  deriving DecidableEq, Repr

/-- Extract 8-bit alpha channel from packed 32-bit ARGB integer. -/
def argbAlpha (argb : UInt32) : UInt32 :=
  (UInt32.ofBitVec (argb.toBitVec.sshiftRight 24)) &&& 255

/-- Extract 8-bit red channel from packed 32-bit ARGB integer. -/
def argbRed (argb : UInt32) : UInt32 :=
  (UInt32.ofBitVec (argb.toBitVec.sshiftRight 16)) &&& 255

/-- Extract 8-bit green channel from packed 32-bit ARGB integer. -/
def argbGreen (argb : UInt32) : UInt32 :=
  (UInt32.ofBitVec (argb.toBitVec.sshiftRight 8)) &&& 255

/-- Extract 8-bit blue channel from packed 32-bit ARGB integer. -/
def argbBlue (argb : UInt32) : UInt32 :=
  argb &&& 255

/-- Pack 8-bit `(r, g, b, a)` channels into a 32-bit ARGB integer (`Color(r, g, b, a).toArgb()`). -/
def packArgb (r g b a : UInt32) : UInt32 :=
  ((a &&& 255) <<< 24) ||| ((r &&& 255) <<< 16) ||| ((g &&& 255) <<< 8) ||| (b &&& 255)

/-- Model of `Color.get(RgbIntComponent)` in `ColorComponent.kt`. -/
def getColorComponent (argb : UInt32) : RgbComponent → UInt32
  | .red => argbRed argb
  | .green => argbGreen argb
  | .blue => argbBlue argb

/-- Model of `Color.withComponent(RgbIntComponent, Int)` in `ColorComponent.kt`. -/
def withColorComponent (argb : UInt32) (c : RgbComponent) (v : UInt32) : UInt32 :=
  packArgb
    (if c == .red then v else getColorComponent argb .red)
    (if c == .green then v else getColorComponent argb .green)
    (if c == .blue then v else getColorComponent argb .blue)
    (argbAlpha argb)

end UiCommon.KotlinModel
