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

import models.RectAndLerpModel
import proofs.RectAndLerpModelProofs

namespace Geometry.KotlinModel

theorem rectCorners_flip_involutive (d : LayoutDirectionModel) :
    d.flip.flip = d :=
  rectCorners_flip_involutive_Impl d

theorem rectCorners_topStart_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.topStart d.flip = r.topEnd d :=
  rectCorners_topStart_flip_Impl r d

theorem rectCorners_topEnd_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.topEnd d.flip = r.topStart d :=
  rectCorners_topEnd_flip_Impl r d

theorem rectCorners_centerStart_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.centerStart d.flip = r.centerEnd d :=
  rectCorners_centerStart_flip_Impl r d

theorem rectCorners_centerEnd_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.centerEnd d.flip = r.centerStart d :=
  rectCorners_centerEnd_flip_Impl r d

theorem rectCorners_bottomStart_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.bottomStart d.flip = r.bottomEnd d :=
  rectCorners_bottomStart_flip_Impl r d

theorem rectCorners_bottomEnd_flip (r : RectCorners) (d : LayoutDirectionModel) :
    r.bottomEnd d.flip = r.bottomStart d :=
  rectCorners_bottomEnd_flip_Impl r d

theorem intSizeWidth_pack (w h : Int32) :
    intSizeWidth (packIntSize w h) = w :=
  intSizeWidth_pack_Impl w h

theorem intSizeHeight_pack (w h : Int32) :
    intSizeHeight (packIntSize w h) = h :=
  intSizeHeight_pack_Impl w h

theorem packIntSize_unpack (p : UInt64) :
    packIntSize (intSizeWidth p) (intSizeHeight p) = p :=
  packIntSize_unpack_Impl p

theorem lerpIntSize_endpoints (lerpInt : Int32 → Int32 → Float32 → Int32)
    (h0 : ∀ a b, lerpInt a b (0.0 : Float32) = a)
    (h1 : ∀ a b, lerpInt a b (1.0 : Float32) = b)
    (start stop : UInt64) :
    lerpIntSizeModel lerpInt start stop (0.0 : Float32) = start ∧
    lerpIntSizeModel lerpInt start stop (1.0 : Float32) = stop :=
  lerpIntSize_endpoints_Impl lerpInt h0 h1 start stop

theorem lerpIntSize_const (lerpInt : Int32 → Int32 → Float32 → Int32)
    (hconst : ∀ x f, lerpInt x x f = x)
    (s : UInt64) (f : Float32) :
    lerpIntSizeModel lerpInt s s f = s :=
  lerpIntSize_const_Impl lerpInt hconst s f

end Geometry.KotlinModel
