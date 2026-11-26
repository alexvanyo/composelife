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

import models.ColorComponentModel
import proofs.ColorComponentModelProofs

namespace UiCommon.KotlinModel

theorem argbAlpha_packArgb (r g b a : UInt32) :
    argbAlpha (packArgb r g b a) = a &&& 255 :=
  argbAlpha_packArgb_Impl r g b a

theorem argbRed_packArgb (r g b a : UInt32) :
    argbRed (packArgb r g b a) = r &&& 255 :=
  argbRed_packArgb_Impl r g b a

theorem argbGreen_packArgb (r g b a : UInt32) :
    argbGreen (packArgb r g b a) = g &&& 255 :=
  argbGreen_packArgb_Impl r g b a

theorem argbBlue_packArgb (r g b a : UInt32) :
    argbBlue (packArgb r g b a) = b &&& 255 :=
  argbBlue_packArgb_Impl r g b a

theorem packArgb_unpack (argb : UInt32) :
    packArgb (argbRed argb) (argbGreen argb) (argbBlue argb) (argbAlpha argb) = argb :=
  packArgb_unpack_Impl argb

theorem withColorComponent_get_same (argb : UInt32) (c : RgbComponent) (v : UInt32) :
    getColorComponent (withColorComponent argb c v) c = v &&& 255 :=
  withColorComponent_get_same_Impl argb c v

theorem withColorComponent_preserves_alpha (argb : UInt32) (c : RgbComponent) (v : UInt32) :
    argbAlpha (withColorComponent argb c v) = argbAlpha argb :=
  withColorComponent_preserves_alpha_Impl argb c v

theorem withColorComponent_get_self (argb : UInt32) (c : RgbComponent) :
    withColorComponent argb c (getColorComponent argb c) = argb :=
  withColorComponent_get_self_Impl argb c

end UiCommon.KotlinModel
