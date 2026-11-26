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

import models.SerializersModel
import proofs.SerializersModelProofs

namespace Serialization.Model

theorem packInts_unpack_roundtrip (x y : Int32) :
    unpackInt1 (packInts x y) = x ∧ unpackInt2 (packInts x y) = y :=
  packInts_unpack_roundtrip_Impl x y

theorem unpack_packInts_roundtrip (v : UInt64) :
    packInts (unpackInt1 v) (unpackInt2 v) = v :=
  unpack_packInts_roundtrip_Impl v

theorem packFloats_unpack_roundtrip (x y : Float32) :
    unpackFloat1 (packFloats x y) = x ∧ unpackFloat2 (packFloats x y) = y :=
  packFloats_unpack_roundtrip_Impl x y

theorem closedFloatRange_roundtrip (r : ClosedFloatRangeModel) :
    deserializeClosedFloatRange (serializeClosedFloatRange r) = r :=
  closedFloatRange_roundtrip_Impl r

theorem rect_roundtrip (r : RectModel) :
    deserializeRect (serializeRect r) = some r :=
  rect_roundtrip_Impl r

theorem surrogating_roundtrip {T S E : Type}
    (encodeS : S → E) (decodeS : E → S) (toSurr : T → S) (fromSurr : S → T)
    (hS : ∀ s, decodeS (encodeS s) = s)
    (hT : ∀ x, fromSurr (toSurr x) = x) (x : T) :
    deserializeSurrogate decodeS fromSurr (serializeSurrogate encodeS toSurr x) = x :=
  surrogating_roundtrip_Impl encodeS decodeS toSurr fromSurr hS hT x

end Serialization.Model
