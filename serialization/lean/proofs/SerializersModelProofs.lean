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

import Std.Tactic.BVDecide
import models.SerializersModel

namespace Serialization.Model

private theorem sign_toBitVec_ofBitVec (s : BitVec 1) :
    (Float.Model.UnpackedFloat.Sign.ofBitVec s).toBitVec = s := by
  decide +revert

private theorem bv32_reconstruct (b : BitVec 32) :
    b.extractLsb' 31 1 ++ b.extractLsb' 23 8 ++ b.extractLsb' 0 23 = b := by
  bv_normalize

private theorem nat_log2_lt_23 {n : Nat} (hn : n < 2 ^ 23) : n.log2 < 23 := by
  by_cases h0 : n = 0
  · subst h0; decide
  · have hle : 2 ^ n.log2 ≤ n := Nat.log2_self_le h0
    have hlt : 2 ^ n.log2 < 2 ^ 23 := Nat.lt_of_le_of_lt hle hn
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt

private theorem nat_log2_normal_23 {n : Nat} (hlo : 2 ^ 23 ≤ n) (hhi : n < 2 ^ 24) : n.log2 = 23 := by
  have h1 : 23 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr hlo
  have h2 : n.log2 < 24 := by
    have hle : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
    have hlt : 2 ^ n.log2 < 2 ^ 24 := Nat.lt_of_le_of_lt hle hhi
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  omega

theorem append_one_toNat (m : BitVec 23) : (1#1 ++ m).toNat = 2 ^ 23 + m.toNat := by
  have h : (1#1 ++ m) = BitVec.ofNat 24 8388608 + m.setWidth 24 := by
    bv_check "lrat/SerializersModelProofs.Serialization.Proofs.append_one_toNat.lrat"
  rw [h, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have hlt : m.toNat < 8388608 := m.isLt
  have hmod : m.toNat % 16777216 = m.toNat := Nat.mod_eq_of_lt (by omega)
  have hpow : (2 ^ 23 : Nat) = 8388608 := by decide
  have hpow24 : (2 ^ 24 : Nat) = 16777216 := by decide
  rw [hpow, hpow24] at *
  omega

private theorem float32_ofBits_toBits (x : Float32) : Float32.ofBits x.toBits = x := by
  cases x with
  | ofModel m =>
    cases m with
    | mk bits hvalid =>
      cases bits with
      | ofBitVec b =>
        dsimp [Float32.ofBits, Float32.toBits, Float32.Model.ofBits, Float32.Model.pack]
        congr 1
        simp only [Float32.Model.mk.injEq, UInt32.ofBitVec.injEq]
        unfold Float.Model.UnpackedFloat.unpack
        by_cases hexp : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary32) b = -1#8
        · simp only [hexp, ↓reduceIte]
          by_cases hman : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary32) b = 0#23
          · simp only [hman, ↓reduceIte, Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packedInfinity,
              Float.Model.UnpackedFloat.packComponents, sign_toBitVec_ofBitVec]
            simp only [Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
              Float.Model.UnpackedFloat.unpackSign, Float.Model.Format.binary32] at hexp hman ⊢
            change b.extractLsb' 31 1 ++ -1#8 ++ 0#23 = b
            rw [← hexp, ← hman]
            exact bv32_reconstruct b
          · simp only [hman, ↓reduceIte, Float.Model.UnpackedFloat.pack]
            exact (hvalid.eq_packedNaN hexp hman).symm
        · simp only [hexp, ↓reduceIte]
          by_cases hexp0 : Float.Model.UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary32) b = 0#8
          · simp only [hexp0, ↓reduceIte]
            by_cases hman0 : Float.Model.UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary32) b = 0#23
            · simp only [hman0, ↓reduceDIte, Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packedZero,
                Float.Model.UnpackedFloat.packComponents, sign_toBitVec_ofBitVec]
              simp only [Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
                Float.Model.UnpackedFloat.unpackSign, Float.Model.Format.binary32] at hexp0 hman0 ⊢
              change b.extractLsb' 31 1 ++ 0#8 ++ 0#23 = b
              rw [← hexp0, ← hman0]
              exact bv32_reconstruct b
            · simp only [hman0, ↓reduceDIte, Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packComponents,
                sign_toBitVec_ofBitVec]
              have hbias : Float.Model.Format.binary32.exponentBias = 127 := by decide
              have hmb : Float.Model.Format.binary32.mantissaBits = 24 := by decide
              have hlog : (b.extractLsb' 0 23).toNat.log2 < 23 := nat_log2_lt_23 (b.extractLsb' 0 23).isLt
              have h2 : ¬ ((b.extractLsb' 0 23).toNat.log2 + 1 = 24) := by omega
              simp only [hbias, hmb, Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
                Float.Model.UnpackedFloat.unpackSign, Float.Model.Format.binary32] at hexp0 ⊢
              simp only [h2, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              change b.extractLsb' 31 1 ++ 0#8 ++ b.extractLsb' 0 23 = b
              rw [← hexp0]
              exact bv32_reconstruct b
          · simp only [hexp0, ↓reduceIte, Float.Model.UnpackedFloat.pack, Float.Model.UnpackedFloat.packComponents,
              sign_toBitVec_ofBitVec]
            have hbias : Float.Model.Format.binary32.exponentBias = 127 := by decide
            have hmb : Float.Model.Format.binary32.mantissaBits = 24 := by decide
            simp only [hbias, hmb, Float.Model.UnpackedFloat.unpackExponent, Float.Model.UnpackedFloat.unpackMantissa,
              Float.Model.UnpackedFloat.unpackSign, Float.Model.Format.binary32] at hexp hexp0 ⊢
            have hbe : (((b.extractLsb' 23 8).toNat : Int) - ((127 : Nat) + (23 : Nat)) + (127 : Nat) + (23 : Nat)).toNat =
                (b.extractLsb' 23 8).toNat := by omega
            have hexp_lt : (b.extractLsb' 23 8).toNat < 255 := by
              have hlt := (b.extractLsb' 23 8).isLt
              have hne : (b.extractLsb' 23 8).toNat ≠ 255 := by
                intro heq
                apply hexp
                apply BitVec.eq_of_toNat_eq
                simpa using heq
              omega
            have hcat : (1#1 ++ b.extractLsb' 0 23).toNat = 2 ^ 23 + (b.extractLsb' 0 23).toNat :=
              append_one_toNat (b.extractLsb' 0 23)
            have hlog : (1#1 ++ b.extractLsb' 0 23).toNat.log2 = 23 := by
              rw [hcat]
              have hlt := (b.extractLsb' 0 23).isLt
              exact nat_log2_normal_23 (by omega) (by omega)
            have h1 : ¬ (2 ^ 8 ≤ (b.extractLsb' 23 8).toNat + 1) := by omega
            have h2 : (1#1 ++ b.extractLsb' 0 23).toNat.log2 + 1 = 24 := by omega
            rw [hbe]
            simp only [h1, h2, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            have hman_eq : BitVec.setWidth 23 (1#1 ++ b.extractLsb' 0 23) = b.extractLsb' 0 23 := by bv_normalize
            rw [hman_eq]
            exact bv32_reconstruct b

theorem packInts_unpack_roundtrip_Impl (x y : Int32) :
    unpackInt1 (packInts x y) = x ∧ unpackInt2 (packInts x y) = y := by
  unfold packInts unpackInt1 unpackInt2
  bv_check "lrat/SerializersModelProofs.Serialization.Proofs.packInts_unpack_roundtrip_Impl.lrat"

theorem unpack_packInts_roundtrip_Impl (v : UInt64) :
    packInts (unpackInt1 v) (unpackInt2 v) = v := by
  unfold packInts unpackInt1 unpackInt2
  bv_check "lrat/SerializersModelProofs.Serialization.Proofs.unpack_packInts_roundtrip_Impl.lrat"

theorem packFloats_bits_roundtrip (bx by_ : UInt32) :
    ((bx.toInt32.toInt64.toUInt64 <<< 32 |||
      by_.toInt32.toInt64.toUInt64 &&& (0xFFFFFFFF : UInt64)).toInt64 >>> 32).toInt32.toUInt32 = bx ∧
    ((bx.toInt32.toInt64.toUInt64 <<< 32 |||
      by_.toInt32.toInt64.toUInt64 &&& (0xFFFFFFFF : UInt64)) &&& (0xFFFFFFFF : UInt64)).toUInt32 = by_ := by
  bv_check "lrat/SerializersModelProofs.Serialization.Proofs.packFloats_bits_roundtrip.lrat"

theorem packFloats_unpack_roundtrip_Impl (x y : Float32) :
    unpackFloat1 (packFloats x y) = x ∧ unpackFloat2 (packFloats x y) = y := by
  unfold packFloats unpackFloat1 unpackFloat2
  have h := packFloats_bits_roundtrip x.toBits y.toBits
  rw [h.1, h.2, float32_ofBits_toBits, float32_ofBits_toBits]
  exact ⟨rfl, rfl⟩

theorem closedFloatRange_roundtrip_Impl (r : ClosedFloatRangeModel) :
    deserializeClosedFloatRange (serializeClosedFloatRange r) = r := by
  rcases r with ⟨s, e⟩
  unfold deserializeClosedFloatRange serializeClosedFloatRange
  have h := packFloats_unpack_roundtrip_Impl s e
  simp [h.1, h.2]

theorem rect_roundtrip_Impl (r : RectModel) :
    deserializeRect (serializeRect r) = some r := by
  cases r
  rfl

theorem surrogating_roundtrip_Impl {T S E : Type}
    (encodeS : S → E) (decodeS : E → S) (toSurr : T → S) (fromSurr : S → T)
    (hS : ∀ s, decodeS (encodeS s) = s)
    (hT : ∀ x, fromSurr (toSurr x) = x) (x : T) :
    deserializeSurrogate decodeS fromSurr (serializeSurrogate encodeS toSurr x) = x := by
  unfold deserializeSurrogate serializeSurrogate
  rw [hS, hT]

end Serialization.Model
