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

namespace UiCommon.KotlinModel

private theorem u32_eq_of_getLsbD {a b : UInt32}
    (h : ∀ i < 32, a.toBitVec.getLsbD i = b.toBitVec.getLsbD i) : a = b := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h i hi

private theorem mask255_getLsbD (i : Nat) (hi : i < 32) :
    (255#32).getLsbD i = decide (i < 8) := by
  rw [BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem argbAlpha_packArgb_Impl (r g b a : UInt32) :
    argbAlpha (packArgb r g b a) = a &&& 255 := by
  unfold argbAlpha packArgb
  apply u32_eq_of_getLsbD; intro i hi
  change ((((a.toBitVec &&& 255#32) <<< 24 ||| (r.toBitVec &&& 255#32) <<< 16 |||
      (g.toBitVec &&& 255#32) <<< 8 ||| (b.toBitVec &&& 255#32)).sshiftRight 24) &&& 255#32).getLsbD i =
    (a.toBitVec &&& 255#32).getLsbD i
  by_cases h8 : i < 8
  · have hle : ¬ (32 ≤ i) := by omega
    have h24 : 24 + i < 32 := by omega
    have hlt24 : ¬ (24 + i < 24) := by omega
    have hlt16 : ¬ (24 + i < 16) := by omega
    have hlt8 : ¬ (24 + i < 8) := by omega
    have hm : (255#32).getLsbD i = true := by rw [mask255_getLsbD i hi]; exact decide_eq_true h8
    have hm16 : (255#32).getLsbD (24 + i - 16) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
    have hm8 : (255#32).getLsbD (24 + i - 8) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
    have hm0 : (255#32).getLsbD (24 + i) = false := by rw [mask255_getLsbD _ h24]; exact decide_eq_false (by omega)
    have hsub : 24 + i - 24 = i := by omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, hle, h24, hlt24, hlt16, hlt8, hm, hm16, hm8, hm0, hsub,
      decide_true, decide_false, ↓reduceIte, Bool.not_false, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.or_false]
  · have hm : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
    simp only [BitVec.getLsbD_and, hm, Bool.and_false]

theorem argbRed_packArgb_Impl (r g b a : UInt32) :
    argbRed (packArgb r g b a) = r &&& 255 := by
  unfold argbRed packArgb
  apply u32_eq_of_getLsbD; intro i hi
  change ((((a.toBitVec &&& 255#32) <<< 24 ||| (r.toBitVec &&& 255#32) <<< 16 |||
      (g.toBitVec &&& 255#32) <<< 8 ||| (b.toBitVec &&& 255#32)).sshiftRight 16) &&& 255#32).getLsbD i =
    (r.toBitVec &&& 255#32).getLsbD i
  by_cases h8 : i < 8
  · have hle : ¬ (32 ≤ i) := by omega
    have h16 : 16 + i < 32 := by omega
    have hlt24 : 16 + i < 24 := by omega
    have hlt16 : ¬ (16 + i < 16) := by omega
    have hlt8 : ¬ (16 + i < 8) := by omega
    have hm : (255#32).getLsbD i = true := by rw [mask255_getLsbD i hi]; exact decide_eq_true h8
    have hm8 : (255#32).getLsbD (16 + i - 8) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
    have hm0 : (255#32).getLsbD (16 + i) = false := by rw [mask255_getLsbD _ h16]; exact decide_eq_false (by omega)
    have hsub : 16 + i - 16 = i := by omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, hle, h16, hlt24, hlt16, hlt8, hm, hm8, hm0, hsub,
      decide_true, decide_false, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.true_and,
      Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
  · have hm : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
    simp only [BitVec.getLsbD_and, hm, Bool.and_false]

theorem argbGreen_packArgb_Impl (r g b a : UInt32) :
    argbGreen (packArgb r g b a) = g &&& 255 := by
  unfold argbGreen packArgb
  apply u32_eq_of_getLsbD; intro i hi
  change ((((a.toBitVec &&& 255#32) <<< 24 ||| (r.toBitVec &&& 255#32) <<< 16 |||
      (g.toBitVec &&& 255#32) <<< 8 ||| (b.toBitVec &&& 255#32)).sshiftRight 8) &&& 255#32).getLsbD i =
    (g.toBitVec &&& 255#32).getLsbD i
  by_cases h8 : i < 8
  · have hle : ¬ (32 ≤ i) := by omega
    have h8' : 8 + i < 32 := by omega
    have hlt24 : 8 + i < 24 := by omega
    have hlt16 : 8 + i < 16 := by omega
    have hlt8 : ¬ (8 + i < 8) := by omega
    have hm : (255#32).getLsbD i = true := by rw [mask255_getLsbD i hi]; exact decide_eq_true h8
    have hm0 : (255#32).getLsbD (8 + i) = false := by rw [mask255_getLsbD _ h8']; exact decide_eq_false (by omega)
    have hsub : 8 + i - 8 = i := by omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, hle, h8', hlt24, hlt16, hlt8, hm, hm0, hsub,
      decide_true, decide_false, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.true_and,
      Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
  · have hm : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
    simp only [BitVec.getLsbD_and, hm, Bool.and_false]

theorem argbBlue_packArgb_Impl (r g b a : UInt32) :
    argbBlue (packArgb r g b a) = b &&& 255 := by
  unfold argbBlue packArgb
  apply u32_eq_of_getLsbD; intro i hi
  change (((a.toBitVec &&& 255#32) <<< 24 ||| (r.toBitVec &&& 255#32) <<< 16 |||
      (g.toBitVec &&& 255#32) <<< 8 ||| (b.toBitVec &&& 255#32)) &&& 255#32).getLsbD i =
    (b.toBitVec &&& 255#32).getLsbD i
  by_cases h8 : i < 8
  · have hlt24 : i < 24 := by omega
    have hlt16 : i < 16 := by omega
    have hm : (255#32).getLsbD i = true := by rw [mask255_getLsbD i hi]; exact decide_eq_true h8
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, h8, hlt24, hlt16, hm,
      decide_true, Bool.not_true, Bool.and_true, Bool.and_false, Bool.false_and, Bool.false_or]
  · have hm : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
    simp only [BitVec.getLsbD_and, hm, Bool.and_false]

theorem packArgb_unpack_Impl (argb : UInt32) :
    packArgb (argbRed argb) (argbGreen argb) (argbBlue argb) (argbAlpha argb) = argb := by
  unfold packArgb argbRed argbGreen argbBlue argbAlpha
  apply u32_eq_of_getLsbD; intro i hi
  change ((((argb.toBitVec.sshiftRight 24 &&& 255#32) &&& 255#32) <<< 24 |||
      ((argb.toBitVec.sshiftRight 16 &&& 255#32) &&& 255#32) <<< 16 |||
      ((argb.toBitVec.sshiftRight 8 &&& 255#32) &&& 255#32) <<< 8 |||
      ((argb.toBitVec &&& 255#32) &&& 255#32))).getLsbD i = argb.toBitVec.getLsbD i
  by_cases h8 : i < 8
  · have hm : (255#32).getLsbD i = true := by rw [mask255_getLsbD i hi]; exact decide_eq_true h8
    have hlt16 : i < 16 := by omega
    have hlt24 : i < 24 := by omega
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hi, h8,
      hlt16, hlt24, hm, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.and_true, Bool.false_or]
  · by_cases h16 : i < 16
    · have hm0 : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
      have hm8 : (255#32).getLsbD (i - 8) = true := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_true (by omega)
      have hle : ¬ (32 ≤ i - 8) := by omega
      have hadd : 8 + (i - 8) = i := by omega
      have hlt24 : i < 24 := by omega
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
        BitVec.getLsbD_sshiftRight, hi, h8, h16, hlt24, hm0, hm8, hle, hadd,
        decide_true, decide_false, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.and_true, Bool.false_or, Bool.or_false]
    · by_cases h24 : i < 24
      · have hm0 : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
        have hm8 : (255#32).getLsbD (i - 8) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
        have hm16 : (255#32).getLsbD (i - 16) = true := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_true (by omega)
        have hle : ¬ (32 ≤ i - 16) := by omega
        have hadd : 16 + (i - 16) = i := by omega
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
          BitVec.getLsbD_sshiftRight, hi, h8, h16, h24, hm0, hm8, hm16, hle, hadd,
          decide_true, decide_false, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.true_and,
          Bool.false_and, Bool.and_false, Bool.and_true, Bool.false_or, Bool.or_false]
      · have hm0 : (255#32).getLsbD i = false := by rw [mask255_getLsbD i hi]; exact decide_eq_false h8
        have hm8 : (255#32).getLsbD (i - 8) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
        have hm16 : (255#32).getLsbD (i - 16) = false := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_false (by omega)
        have hm24 : (255#32).getLsbD (i - 24) = true := by rw [mask255_getLsbD _ (by omega)]; exact decide_eq_true (by omega)
        have hle : ¬ (32 ≤ i - 24) := by omega
        have hadd : 24 + (i - 24) = i := by omega
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
          BitVec.getLsbD_sshiftRight, hi, h8, h16, h24, hm0, hm8, hm16, hm24, hle, hadd,
          decide_true, decide_false, ↓reduceIte, Bool.not_false, Bool.true_and,
          Bool.and_false, Bool.and_true, Bool.or_false]

theorem withColorComponent_get_same_Impl (argb : UInt32) (c : RgbComponent) (v : UInt32) :
    getColorComponent (withColorComponent argb c v) c = v &&& 255 := by
  cases c
  · simp [withColorComponent, getColorComponent, argbRed_packArgb_Impl]
  · simp [withColorComponent, getColorComponent, argbGreen_packArgb_Impl]
  · simp [withColorComponent, getColorComponent, argbBlue_packArgb_Impl]

theorem withColorComponent_preserves_alpha_Impl (argb : UInt32) (c : RgbComponent) (v : UInt32) :
    argbAlpha (withColorComponent argb c v) = argbAlpha argb := by
  unfold withColorComponent
  rw [argbAlpha_packArgb_Impl]
  unfold argbAlpha
  apply u32_eq_of_getLsbD; intro i hi
  simp [BitVec.getLsbD_and]

theorem withColorComponent_get_self_Impl (argb : UInt32) (c : RgbComponent) :
    withColorComponent argb c (getColorComponent argb c) = argb := by
  cases c <;> simp [withColorComponent, getColorComponent, packArgb_unpack_Impl]

end UiCommon.KotlinModel
