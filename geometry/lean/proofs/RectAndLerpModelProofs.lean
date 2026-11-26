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
import proofs.GeometryExtensionsModelProofs

namespace Geometry.KotlinModel

theorem rectCorners_flip_involutive_Impl (d : LayoutDirectionModel) :
    d.flip.flip = d := by
  cases d <;> rfl

theorem rectCorners_topStart_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.topStart d.flip = r.topEnd d := by
  cases d <;> rfl

theorem rectCorners_topEnd_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.topEnd d.flip = r.topStart d := by
  cases d <;> rfl

theorem rectCorners_centerStart_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.centerStart d.flip = r.centerEnd d := by
  cases d <;> rfl

theorem rectCorners_centerEnd_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.centerEnd d.flip = r.centerStart d := by
  cases d <;> rfl

theorem rectCorners_bottomStart_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.bottomStart d.flip = r.bottomEnd d := by
  cases d <;> rfl

theorem rectCorners_bottomEnd_flip_Impl (r : RectCorners) (d : LayoutDirectionModel) :
    r.bottomEnd d.flip = r.bottomStart d := by
  cases d <;> rfl

theorem intSizeWidth_pack_Impl (w h : Int32) :
    intSizeWidth (packIntSize w h) = w :=
  offsetX_pack w h

theorem intSizeHeight_pack_Impl (w h : Int32) :
    intSizeHeight (packIntSize w h) = h :=
  offsetY_pack w h

theorem packIntSize_unpack_Impl (p : UInt64) :
    packIntSize (intSizeWidth p) (intSizeHeight p) = p :=
  packOffset_unpack p

theorem lerpIntSize_endpoints_Impl (lerpInt : Int32 → Int32 → Float32 → Int32)
    (h0 : ∀ a b, lerpInt a b (0.0 : Float32) = a)
    (h1 : ∀ a b, lerpInt a b (1.0 : Float32) = b)
    (start stop : UInt64) :
    lerpIntSizeModel lerpInt start stop (0.0 : Float32) = start ∧
    lerpIntSizeModel lerpInt start stop (1.0 : Float32) = stop := by
  unfold lerpIntSizeModel
  rw [h0, h0, h1, h1, packIntSize_unpack_Impl, packIntSize_unpack_Impl]
  exact ⟨rfl, rfl⟩

theorem lerpIntSize_const_Impl (lerpInt : Int32 → Int32 → Float32 → Int32)
    (hconst : ∀ x f, lerpInt x x f = x)
    (s : UInt64) (f : Float32) :
    lerpIntSizeModel lerpInt s s f = s := by
  unfold lerpIntSizeModel
  rw [hconst, hconst, packIntSize_unpack_Impl]

end Geometry.KotlinModel
