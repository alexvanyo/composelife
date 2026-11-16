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
import JvmBytecode
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.Batch2
import proofs.JvmEquiv.FlatInfra

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl

private theorem lvl_shift_lt (lvl : UInt32) (h : lvl < 32) :
    ((lvl &&& 63).toUInt64) = lvl.toUInt64 := by
  have h1 : lvl &&& 63 = lvl := by
    apply UInt32.eq_of_toBitVec_eq
    have hbv : lvl.toBitVec < 32#32 := h
    bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lvl_shift_lt.lrat"
  simp [h1]

private theorem ui32_add1_toNat {a b : UInt32} (h : a < b) :
    (a + 1).toNat = a.toNat + 1 := by
  have ha : a.toNat < b.toNat := h
  have hb : b.toNat < 2 ^ 32 := UInt32.toNat_lt b
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  exact Nat.mod_eq_of_lt (by omega)

theorem ui32_sub1_toNat {a : UInt32} (h : a ≠ 0) :
    (a - 1).toNat = a.toNat - 1 := by
  have hpos : 0 < a.toNat := Nat.pos_of_ne_zero fun hz =>
    h (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
  have hle : (1 : UInt32) ≤ a := by
    show 1 ≤ a.toNat; omega
  rw [UInt32.toNat_sub_of_le a 1 hle]
  rfl

private theorem levelForSpanLoop_aux (n : Nat) :
    ∀ (k : Nat) (span : UInt64) (lvl : UInt32) (_hn : 32 - lvl.toNat ≤ n) (base : Nat → JvmVal),
    runJvmValFast (k + (n + 1) * 40) f_Algorithm_levelForSpanLoop_prog 0 f_Algorithm_levelForSpanLoop_prog
      ⟨0, [], setLocal (setLocal base 0 (.i64 span)) 2 (.i32 lvl), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.levelForSpanLoop span lvl)) := by
  induction n with
  | zero =>
    intro k span lvl _hn base
    have hge : ¬ (lvl < 32) := by
      intro hlt; have : lvl.toNat < 32 := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [Algorithm.levelForSpanLoop]
    simp [hge]
  | succ n ih =>
    intro k span lvl _hn base
    rw [show k + (n + 1 + 1) * 40 = (k + (n + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : lvl < 32
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_levelForSpanLoop_prog
      rw [compareUnsigned64_slt']
      by_cases hltsp : ((1 : UInt64) <<< (lvl &&& 63).toUInt64) < span
      · simp only [hltsp, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_levelForSpanLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((n + 1) * 40), Nat.add_comm ((n + 1) * 40)]
        rw [Algorithm.levelForSpanLoop]
        have hltsp' : ((1 : UInt64) <<< lvl.toUInt64) < span := by
          rwa [lvl_shift_lt lvl hlt] at hltsp
        simp only [hlt, hltsp', and_self, ↓reduceDIte]
        have hnext : 32 - (lvl + 1).toNat ≤ n := by
          have := ui32_add1_toNat hlt; omega
        exact ih _ span (lvl + 1) hnext _
      · simp only [hltsp, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_levelForSpanLoop_prog
        rw [Algorithm.levelForSpanLoop]
        have hnot : ¬ ((1 : UInt64) <<< lvl.toUInt64 < span) := by
          rwa [lvl_shift_lt lvl hlt] at hltsp
        simp [hlt, hnot]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_levelForSpanLoop_prog
      rw [Algorithm.levelForSpanLoop]
      simp [hlt]

theorem levelForSpanLoop_equiv (span : UInt64) (lvl : UInt32) :
    runJvm 1320 f_Algorithm_levelForSpanLoop_prog
      (initJvmState [(0, .i64 span), (2, .i32 lvl)]) =
      some (.i32 (Algorithm.levelForSpanLoop span lvl)) := by
  apply runJvm_of_runJvmValFast0 1320 _ _ _ rfl
  exact levelForSpanLoop_aux 32 0 span lvl (by omega) _

private theorem countChars_aux (m : Nat) :
    ∀ (k : Nat) (bytes : ByteArray) (limit p cnt : UInt32)
      (_hn : limit.toNat - p.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 50) f_Algorithm_countChars_prog 3 (f_Algorithm_countChars_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.byteArr bytes)))) 1 (.i32 limit)) 2 (.i32 p)) 3 (.i32 cnt), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.countChars bytes limit p cnt)) := by
  induction m with
  | zero =>
    intro k bytes limit p cnt _hn base
    have hge : ¬ (p < limit) := by
      intro hlt; have : p.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_countChars_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_countChars_prog
    rw [Algorithm.countChars]
    simp [hge]
  | succ m ih =>
    intro k bytes limit p cnt _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_countChars_prog
    rw [compareUnsigned_slt']
    by_cases hlt : p < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_countChars_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
      rw [Algorithm.countChars]
      simp only [hlt, ↓reduceDIte]
      have hd := Algorithm.decodeCharAt_next bytes p limit hlt
      have hnext : limit.toNat - (Algorithm.decodeCharAt bytes p limit).2.toNat ≤ m := by omega
      exact ih _ bytes limit (Algorithm.decodeCharAt bytes p limit).2 (cnt + 1) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_countChars_prog
      rw [Algorithm.countChars]
      simp [hlt]

theorem countChars_equiv (bytes : ByteArray) (limit p n : UInt32) :
    runJvm ((limit.toNat - p.toNat + 1) * 50 + 3) f_Algorithm_countChars_prog
      (initJvmState [(0, (.ext (.byteArr bytes))), (1, .i32 limit), (2, .i32 p), (3, .i32 n)]) =
      some (.i32 (Algorithm.countChars bytes limit p n)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - p.toNat + 1) * 50)]
  exact countChars_aux (limit.toNat - p.toNat) 0 bytes limit p n (by omega) _

private theorem emptyMacroCellUInt32_loop_aux (m : Nat) :
    ∀ (k : Nat) (level curLevel : UInt32) (curNode : Algorithm.MacroCell)
      (_hn : level.toNat - curLevel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 40) f_Algorithm_emptyMacroCellUInt32_loop_prog 3
      (f_Algorithm_emptyMacroCellUInt32_loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.i32 level)) 1 (.i32 curLevel)) 2 ((.ext (.mc curNode))), {}, ⟨[], [], []⟩⟩ =
      some ((.ext (.mc (Algorithm.emptyMacroCellUInt32.loop level curLevel curNode)))) := by
  induction m with
  | zero =>
    intro k level curLevel curNode _hn base
    have hge : ¬ (curLevel < level) := by
      intro hlt; have : curLevel.toNat < level.toNat := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [Algorithm.emptyMacroCellUInt32.loop]
    simp [hge]
  | succ m ih =>
    intro k level curLevel curNode _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : curLevel < level
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.emptyMacroCellUInt32.loop]
      simp only [hlt, ↓reduceDIte]
      have hnext : level.toNat - (curLevel + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ level (curLevel + 1) (Algorithm.makeCellNode curNode curNode curNode curNode) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
      rw [Algorithm.emptyMacroCellUInt32.loop]
      simp [hlt]

theorem emptyMacroCellUInt32_loop_equiv (level curLevel : UInt32) (curNode : Algorithm.MacroCell) :
    runJvm ((level.toNat - curLevel.toNat + 1) * 40 + 3) f_Algorithm_emptyMacroCellUInt32_loop_prog
      (initJvmState [(0, .i32 level), (1, .i32 curLevel), (2, (.ext (.mc curNode)))]) =
      some ((.ext (.mc (Algorithm.emptyMacroCellUInt32.loop level curLevel curNode)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((level.toNat - curLevel.toNat + 1) * 40)]
  exact emptyMacroCellUInt32_loop_aux (level.toNat - curLevel.toNat) 0 level curLevel curNode (by omega) _

private theorem stepNGenerationsWith_aux (m : Nat) :
    ∀ (k : Nat) (step : UInt32) (st : Algorithm.HashLifeStepState)
      (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState)
      (_hn : step.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 40) f_Algorithm_stepNGenerationsWith_prog 3 (f_Algorithm_stepNGenerationsWith_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.i32 step)) 1 ((.ext (.hlState st)))) 2 ((.ext (.fnHlToHl stepOneGen))), {}, ⟨[], [], []⟩⟩ =
      some ((.ext (.hlState (Algorithm.stepNGenerationsWith step st stepOneGen)))) := by
  induction m with
  | zero =>
    intro k step st stepOneGen _hn base
    have hz : step = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    simp only [hz, beq_self_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    rw [Algorithm.stepNGenerationsWith]
    simp
  | succ m ih =>
    intro k step st stepOneGen _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    by_cases hz : step = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_stepNGenerationsWith_prog
      rw [Algorithm.stepNGenerationsWith]
      simp
    · simp only [beq_iff_eq, hz, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_stepNGenerationsWith_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.stepNGenerationsWith]
      simp only [hz]
      have hnext : (step - 1).toNat ≤ m := by
        have := ui32_sub1_toNat hz; omega
      exact ih _ (step - 1) (stepOneGen st) stepOneGen hnext _

theorem stepNGenerationsWith_equiv (step : UInt32) (st : Algorithm.HashLifeStepState)
    (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState) :
    runJvm ((step.toNat + 1) * 40 + 3) f_Algorithm_stepNGenerationsWith_prog
      (initJvmState [(0, .i32 step), (1, (.ext (.hlState st))), (2, (.ext (.fnHlToHl stepOneGen)))]) =
      some ((.ext (.hlState (Algorithm.stepNGenerationsWith step st stepOneGen)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((step.toNat + 1) * 40)]
  exact stepNGenerationsWith_aux step.toNat 0 step st stepOneGen (by omega) _

private theorem copyU64_aux (m : Nat) :
    ∀ (k : Nat) (src : Array UInt64) (n i : UInt32) (dst : Array UInt64)
      (_hn : n.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 40) f_Algorithm_copyU64_prog 0 f_Algorithm_copyU64_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.u64Ref 0)))) 1 (.i32 n)) 2 (.i32 i)) 3 ((.ext (.u64Ref 1))), {}, ⟨[], [src, dst], []⟩⟩).map (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) := by
  induction m with
  | zero =>
    intro k src n i dst _hn base
    have hge : ¬ (i < n) := by
      intro hlt; have : i.toNat < n.toNat := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_copyU64_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_copyU64_prog
    rw [Algorithm.copyU64]
    simp [hge]
  | succ m ih =>
    intro k src n i dst _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_copyU64_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < n
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_copyU64_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.copyU64]
      simp only [hlt, ↓reduceDIte]
      have hnext : n.toNat - (i + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ src n (i + 1) (dst.set! i.toNat src[i.toNat]!) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_copyU64_prog
      rw [Algorithm.copyU64]
      simp [hlt]

theorem copyU64_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 n), (2, .i32 i), (3, (.ext (.u64Ref 1)))] [] [src, dst])).map
        (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((n.toNat - i.toNat + 1) * 40)]
  exact copyU64_aux (n.toNat - i.toNat) 0 src n i dst (by omega) _

theorem copyU64_1_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_1_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 n), (2, .i32 i), (3, (.ext (.u64Ref 1)))] [] [src, dst])).map
        (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_2_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_2_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 n), (2, .i32 i), (3, (.ext (.u64Ref 1)))] [] [src, dst])).map
        (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_3_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_3_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 n), (2, .i32 i), (3, (.ext (.u64Ref 1)))] [] [src, dst])).map
        (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_4_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_4_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 n), (2, .i32 i), (3, (.ext (.u64Ref 1)))] [] [src, dst])).map
        (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

private theorem gridRows_aux (m : Nat) :
    ∀ (k : Nat) (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : height.toNat - r.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_gridRows_prog 0 f_Algorithm_gridRows_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.asciiRef 0)))) 1 (.i32 width))
        2 (.i32 height)) 3 (.i32 r)) 4 ((.ext (.strGrowBuf acc))), {}, ⟨[], [], [g]⟩⟩ =
      some ((.ext (.strGrowBuf (Algorithm.gridRows g width height r acc)))) := by
  induction m with
  | zero =>
    intro k g width height r acc _hn base
    have hge : ¬ (r < height) := by
      intro hlt; have : r.toNat < height.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_gridRows_prog
    rw [Algorithm.gridRows]
    simp [hge]
  | succ m ih =>
    intro k g width height r acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_prog
    rw [compareUnsigned_slt']
    by_cases hlt : r < height
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.gridRows]
      simp only [hlt, ↓reduceDIte]
      have hnext : height.toNat - (r + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ g width height (r + 1) (acc.push (g.toStringRange (r * width) (r * width + width))) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_prog
      rw [Algorithm.gridRows]
      simp [hlt]

theorem gridRows_equiv (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((height.toNat - r.toNat + 1) * 60) f_Algorithm_gridRows_prog
      (initJvmState [(0, (.ext (.asciiRef 0))), (1, .i32 width), (2, .i32 height), (3, .i32 r), (4, (.ext (.strGrowBuf acc)))]
        [] [] [g]) =
      some ((.ext (.strGrowBuf (Algorithm.gridRows g width height r acc)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((height.toNat - r.toNat + 1) * 60)]
  exact gridRows_aux (height.toNat - r.toNat) 0 g width height r acc (by omega) _

private theorem gridRows_1_aux (m : Nat) :
    ∀ (k : Nat) (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : height.toNat - r.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_gridRows_1_prog 0 f_Algorithm_gridRows_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.asciiRef 0)))) 1 (.i32 width))
        2 (.i32 height)) 3 (.i32 r)) 4 ((.ext (.strGrowBuf acc))), {}, ⟨[], [], [g]⟩⟩ =
      some ((.ext (.strGrowBuf (Algorithm.gridRows g width height r acc)))) := by
  induction m with
  | zero =>
    intro k g width height r acc _hn base
    have hge : ¬ (r < height) := by
      intro hlt; have : r.toNat < height.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [Algorithm.gridRows]
    simp [hge]
  | succ m ih =>
    intro k g width height r acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [compareUnsigned_slt']
    by_cases hlt : r < height
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_1_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.gridRows]
      simp only [hlt, ↓reduceDIte]
      have hnext : height.toNat - (r + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ g width height (r + 1) (acc.push (g.toStringRange (r * width) (r * width + width))) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_1_prog
      rw [Algorithm.gridRows]
      simp [hlt]

theorem gridRows_1_equiv (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((height.toNat - r.toNat + 1) * 60) f_Algorithm_gridRows_1_prog
      (initJvmState [(0, (.ext (.asciiRef 0))), (1, .i32 width), (2, .i32 height), (3, .i32 r), (4, (.ext (.strGrowBuf acc)))]
        [] [] [g]) =
      some ((.ext (.strGrowBuf (Algorithm.gridRows g width height r acc)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((height.toNat - r.toNat + 1) * 60)]
  exact gridRows_1_aux (height.toNat - r.toNat) 0 g width height r acc (by omega) _

private theorem serializeLife106_loop_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_serializeLife106_loop_prog 3
      (f_Algorithm_serializeLife106_loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.u64Ref 0)))) 1 (.i32 i)) 2 (.i32 limit)) 3 ((.ext (.strGrowBuf acc))), {}, ⟨[], [cells], []⟩⟩ =
      some ((.ext (.strGrowBuf (Algorithm.serializeLife106.loop cells i limit acc)))) := by
  induction m with
  | zero =>
    intro k cells i limit acc _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [Algorithm.serializeLife106.loop]
    simp [hge]
  | succ m ih =>
    intro k cells i limit acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_serializeLife106_loop_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.serializeLife106.loop]
      simp only [hlt, ↓reduceDIte]
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ cells (i + 1) limit
        (acc.push (Algorithm.formatCoordLine (Algorithm.cellKeyX cells[i.toNat]!) (Algorithm.cellKeyY cells[i.toNat]!)))
        hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_serializeLife106_loop_prog
      rw [Algorithm.serializeLife106.loop]
      simp [hlt]

theorem serializeLife106_loop_equiv (cells : Array UInt64) (i limit : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((limit.toNat - i.toNat + 1) * 60 + 3) f_Algorithm_serializeLife106_loop_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 i), (2, .i32 limit), (3, (.ext (.strGrowBuf acc)))] [] [cells]) =
      some ((.ext (.strGrowBuf (Algorithm.serializeLife106.loop cells i limit acc)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 60)]
  exact serializeLife106_loop_aux (limit.toNat - i.toNat) 0 cells i limit acc (by omega) _

theorem fuel_split {C : Nat} (k F r : Nat) (h : C ≤ r) :
    k + r + F = k + (r - C) + F + C := by omega

private theorem ui32_toInt32_mk (w : UInt32) : ({ toUInt32 := w } : Int32) = w.toInt32 := rfl

private theorem cellKeyX_sub_minX (k : UInt64) (minX : Int32) :
    ((Algorithm.cellKeyX k).toInt32 - minX).toUInt32 = (k >>> 32).toUInt32 - minX.toUInt32 := by
  unfold Algorithm.cellKeyX; bv_normalize

private theorem cellKeyY_sub_minY (k : UInt64) (minY : Int32) :
    ((Algorithm.cellKeyY k).toInt32 - minY).toUInt32 = k.toUInt32 - minY.toUInt32 := by
  unfold Algorithm.cellKeyY; bv_normalize

private theorem shift_32_and_63 : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl

private theorem int32_toUInt32_toInt32 (x : Int32) : x.toUInt32.toInt32 = x := by
  cases x; rfl

private theorem ui32_toInt32_x_eq (k : UInt64) : (Algorithm.cellKeyX k).toInt32 = (k >>> 32).toUInt32.toInt32 := rfl

private theorem ui32_toInt32_y_eq (k : UInt64) : (Algorithm.cellKeyY k).toInt32 = k.toUInt32.toInt32 := rfl

private theorem min_u64_eq (a b : UInt64) : min a b = if a ≤ b then a else b := rfl
private theorem max_u64_eq (a b : UInt64) : max a b = if a ≤ b then b else a := rfl
private theorem keyHi_eq (k : UInt64) : Algorithm.keyHi k = k >>> 32 := rfl
private theorem keyLo_eq (k : UInt64) : Algorithm.keyLo k = k &&& 4294967295 := rfl

private theorem u8_toUInt32_toUInt8 (b : UInt8) : b.toUInt32.toUInt8 = b := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem cellBounds_slt (a b : UInt32) :
    (a.toBitVec.slt b.toBitVec) = decide (a.toInt32 < b.toInt32) := rfl

local macro "prove_fillGrid_zero" prog:ident : tactic => `(tactic| (
  intro k cells minX minY width height alive halive i limit g _hn base
  have hge : ¬ (i < limit) := by
    intro hlt; have : i.toNat < limit.toNat := hlt; omega
  rw [show k + (0 + 1) * 90 = k + 90 by omega]
  flat_step_blk $prog
  rw [compareUnsigned_slt']
  simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
  flat_step_blk $prog
  unfold Algorithm.fillGrid
  simp [hge]))

local macro "prove_fillGrid_succ" m:ident prog:ident setThm:ident ih:ident : tactic => `(tactic| (
  intro k cells minX minY width height alive halive i limit g _hn base
  rw [show k + ($m + 1 + 1) * 90 = (k + ($m + 1) * 90) + 90 by omega]
  flat_step_blk $prog
  rw [compareUnsigned_slt']
  by_cases hlt : i < limit
  · simp only [hlt, decide_true, ↓reduceIte]
    have hltNat : i.toNat < limit.toNat := hlt
    have hnext : limit.toNat - (i + 1).toNat ≤ $m := by
      rw [ui32_add1_toNat hlt]; omega
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk $prog
    rw [shift_32_and_63, compareUnsigned_sge']
    by_cases hx : width ≤ (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32
    · simp only [hx, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk $prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      try (repeat rw [Nat.succ_eq_add_one])
      simp only [nat_add_eq, Nat.add_assoc]
      rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)]
      have hnot : ¬ ((cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width) := Nat.not_lt.mpr hx
      unfold Algorithm.fillGrid
      simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, hnot, decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      exact $ih _ cells minX minY width height alive halive (i + 1) limit g hnext _
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk $prog
      rw [compareUnsigned_sge']
      by_cases hy : height ≤ cells[i.toNat]!.toUInt32 - minY.toUInt32
      · simp only [hy, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk $prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try (repeat rw [Nat.succ_eq_add_one])
        simp only [nat_add_eq, Nat.add_assoc]
        (try rw [show ($m + 1).mul 89 + ($m + 1) = ($m + 1) * 90 from rfl])
        (try rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)])
        have hnot : ¬ (cells[i.toNat]!.toUInt32 - minY.toUInt32 < height) := Nat.not_lt.mpr hy
        have hokx : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width := Nat.lt_of_not_le hx
        unfold Algorithm.fillGrid
        simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, cellKeyY_sub_minY, hokx, hnot,
          decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact $ih _ cells minX minY width height alive halive (i + 1) limit g hnext _
      · simp only [hy, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_nonbranch_chunks
        (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step ($setThm rfl (by simpa [u8_toUInt32_toUInt8] using halive))])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk $prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try (repeat rw [Nat.succ_eq_add_one])
        simp only [nat_add_eq, Nat.add_assoc]
        (try rw [show ($m + 1).mul 89 + ($m + 1) = ($m + 1) * 90 from rfl])
        (try rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)])
        have hokx : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width := Nat.lt_of_not_le hx
        have hoky : cells[i.toNat]!.toUInt32 - minY.toUInt32 < height := Nat.lt_of_not_le hy
        unfold Algorithm.fillGrid
        simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, cellKeyY_sub_minY, hokx, hoky,
          decide_true, Bool.and_self, ↓reduceIte, u8_toUInt32_toUInt8]
        exact $ih _ cells minX minY width height alive halive (i + 1) limit _ hnext _
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk $prog
    unfold Algorithm.fillGrid
    simp [hlt]))

private theorem fillGrid_0_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_prog 0 f_Algorithm_fillGrid___redArg_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 ((.ext (.asciiRef 0))), {}, ⟨[], [cells], [g]⟩⟩).map (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_prog stepStatic_asciiSet_105 ih

private theorem fillGrid_1_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_1_prog 0 f_Algorithm_fillGrid___redArg_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 ((.ext (.asciiRef 0))), {}, ⟨[], [cells], [g]⟩⟩).map (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_1_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_1_prog stepStatic_asciiSet_plain ih

private theorem fillGrid_2_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_2_prog 0 f_Algorithm_fillGrid___redArg_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 ((.ext (.asciiRef 0))), {}, ⟨[], [cells], [g]⟩⟩).map (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_2_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_2_prog stepStatic_asciiSet_rle ih

theorem fillGrid_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, (.ext (.asciiRef 0)))] [] [cells] [g])).map
        (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_0_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

theorem fillGrid_1_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_1_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, (.ext (.asciiRef 0)))] [] [cells] [g])).map
        (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_1_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

theorem fillGrid_2_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_2_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, (.ext (.asciiRef 0)))] [] [cells] [g])).map
        (fun p => (p.1, p.2.heap.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_2_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

private theorem cellBounds_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 160) f_Algorithm_cellBounds_prog 0 f_Algorithm_cellBounds_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i32 minX.toUInt32)) 4 (.i32 maxX.toUInt32))
        5 (.i32 minY.toUInt32)) 6 (.i32 maxY.toUInt32), {}, ⟨[], [cells], []⟩⟩ =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
  induction m with
  | zero =>
    intro k cells i limit minX maxX minY maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 160 = k + 160 by omega]
    flat_step_blk f_Algorithm_cellBounds_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_cellBounds_prog
    unfold Algorithm.cellBounds
    simp [hge, boxCellBox]
  | succ m ih =>
    intro k cells i limit minX maxX minY maxY _hn base
    rw [show k + (m + 1 + 1) * 160 = (k + (m + 1) * 160) + 160 by omega]
    flat_step_blk f_Algorithm_cellBounds_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBounds_prog
      let kv := cells[i.toNat]!
      let x := (kv >>> 32).toUInt32.toInt32
      let y := kv.toUInt32.toInt32
      let minX' := if x < minX then x else minX
      let maxX' := if maxX < x then x else maxX
      let minY' := if y < minY then y else minY
      let maxY' := if maxY < y then y else maxY
      have hx_def : (cells[i.toNat]! >>> 32).toUInt32.toInt32 = x := rfl
      have hy_def : cells[i.toNat]!.toUInt32.toInt32 = y := rfl
      have hjoin3 : ∀ k3 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 6 = .i32 maxY.toUInt32 →
          locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) → locs 12 = .i32 maxX'.toUInt32 →
          locs 13 = .i32 minX'.toUInt32 → locs 14 = .i32 minY'.toUInt32 →
          (if maxY.toUInt32.toBitVec.slt y.toUInt32.toBitVec = true then
            runJvmValFast (k3 + (m + 1) * 160 + 50) f_Algorithm_cellBounds_prog 114
              (f_Algorithm_cellBounds_prog.drop 114) ⟨114, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k3 + (m + 1) * 160 + 50) f_Algorithm_cellBounds_prog 93
              (f_Algorithm_cellBounds_prog.drop 93) ⟨93, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k3 locs h0 h2 h6 h10 h11 h12 h13 h14
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        unfold Algorithm.cellBounds
        simp only [hlt, ↓reduceDIte, ui32_toInt32_x_eq, ui32_toInt32_y_eq]
        by_cases hy2 : maxY < y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h6, h10, h11, h12, h13, h14]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          have hy2' : maxY < cells[i.toNat]!.toUInt32.toInt32 := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' maxX' minY' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h6, h10, h11, h12, h13, h14]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          have hy2' : ¬ (maxY < cells[i.toNat]!.toUInt32.toInt32) := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' maxX' minY' maxY hnext _
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 5 = .i32 minY.toUInt32 →
          locs 6 = .i32 maxY.toUInt32 → locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) →
          locs 15 = .i32 minX'.toUInt32 → locs 16 = .i32 maxX'.toUInt32 →
          (if y.toUInt32.toBitVec.slt minY.toUInt32.toBitVec = true then
            runJvmValFast (k2 + (m + 1) * 160 + 80) f_Algorithm_cellBounds_prog 84
              (f_Algorithm_cellBounds_prog.drop 84) ⟨84, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k2 + (m + 1) * 160 + 80) f_Algorithm_cellBounds_prog 77
              (f_Algorithm_cellBounds_prog.drop 77) ⟨77, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k2 locs h0 h2 h5 h6 h10 h11 h15 h16
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hy1 : y < minY
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h5, h6, h10, h11, h15, h16]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 50) k2 ((m + 1) * 160) _ (by omega)]
          have hminY : minY' = y := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rfl
          · rw [hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h5, h6, h10, h11, h15, h16]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 50) k2 ((m + 1) * 160) _ (by omega)]
          have hminY : minY' = minY := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rfl
          · rw [hminY]; rfl
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 4 = .i32 maxX.toUInt32 →
          locs 5 = .i32 minY.toUInt32 → locs 6 = .i32 maxY.toUInt32 → locs 9 = .i32 x.toUInt32 →
          locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) → locs 17 = .i32 minX'.toUInt32 →
          (if maxX.toUInt32.toBitVec.slt x.toUInt32.toBitVec = true then
            runJvmValFast (k1 + (m + 1) * 160 + 100) f_Algorithm_cellBounds_prog 70
              (f_Algorithm_cellBounds_prog.drop 70) ⟨70, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k1 + (m + 1) * 160 + 100) f_Algorithm_cellBounds_prog 65
              (f_Algorithm_cellBounds_prog.drop 65) ⟨65, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k1 locs h0 h2 h4 h5 h6 h9 h10 h11 h17
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hx2 : maxX < x
        · simp only [hx2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h6, h9, h10, h11, h17]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 80) k1 ((m + 1) * 160) _ (by omega)]
          have hmaxX : maxX' = x := by simp only [maxX', hx2, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rw [hmaxX]; rfl
        · simp only [hx2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h6, h9, h10, h11, h17]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 80) k1 ((m + 1) * 160) _ (by omega)]
          have hmaxX : maxX' = maxX := by simp only [maxX', hx2, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rw [hmaxX]; rfl
      rw [cellBounds_slt, shift_32_and_63, show minX.toUInt32.toInt32 = minX from int32_toUInt32_toInt32 minX, hx_def]
      by_cases hx1 : x < minX
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
        rw [fuel_split (C := 100) k ((m + 1) * 160) _ (by omega)]
        have hminX : minX' = x := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
        rw [fuel_split (C := 100) k ((m + 1) * 160) _ (by omega)]
        have hminX : minX' = minX := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBounds_prog
      unfold Algorithm.cellBounds
      simp [hlt, boxCellBox]

theorem cellBounds_equiv (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 160) f_Algorithm_cellBounds_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 maxX.toUInt32),
        (5, .i32 minY.toUInt32), (6, .i32 maxY.toUInt32)] [] [cells]) =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 160)]
  exact cellBounds_aux (limit.toNat - i.toNat) 0 cells i limit minX maxX minY maxY (by omega) _

theorem cellBounds_1_equiv (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 160) f_Algorithm_cellBounds_1_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 maxX.toUInt32),
        (5, .i32 minY.toUInt32), (6, .i32 maxY.toUInt32)] [] [cells]) =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) :=
  cellBounds_equiv cells i limit minX maxX minY maxY

private theorem initRemapL4Loop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 50) f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog 3
      (f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 ((.ext (.arenaRef 0)))) 1 (.i32 i)) 2 (.i32 limit), {}, ⟨[arena], [], []⟩⟩).map (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initRemapL4Loop i limit]) := by
  induction m with
  | zero =>
    intro k arena i limit _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
    simp [hge]
  | succ m ih =>
    intro k arena i limit _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      by_cases hz : i = 0
      · have hzb : (i == 0) = true := beq_iff_eq.mpr hz
        simp only [hzb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
        simp only [hlt, hzb, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
      · have hzb : (i == 0) = false := beq_false_of_ne hz
        simp only [hzb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
        simp only [hlt, hzb, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
      simp [hlt]

theorem initRemapL4Loop_equiv (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 50 + 3) f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 i), (2, .i32 limit)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initRemapL4Loop i limit]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 50)]
  exact initRemapL4Loop_aux (limit.toNat - i.toNat) 0 arena i limit (by omega) _

private theorem initRemapCellLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 50) f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog 3
      (f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 ((.ext (.arenaRef 0)))) 1 (.i32 i)) 2 (.i32 limit), {}, ⟨[arena], [], []⟩⟩).map (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initRemapCellLoop i limit]) := by
  induction m with
  | zero =>
    intro k arena i limit _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
    simp [hge]
  | succ m ih =>
    intro k arena i limit _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      rw [compareUnsigned_slt']
      by_cases hi56 : i < 56
      · simp only [hi56, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
        simp only [hlt, hi56, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
      · simp only [hi56, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
        simp only [hlt, hi56, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
      simp [hlt]

theorem initRemapCellLoop_equiv (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 50 + 3) f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 i), (2, .i32 limit)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initRemapCellLoop i limit]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 50)]
  exact initRemapCellLoop_aux (limit.toNat - i.toNat) 0 arena i limit (by omega) _

private theorem life105Bounds_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY maxY : Int32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 140) f_Algorithm_life105Bounds_prog 3
      (f_Algorithm_life105Bounds_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i32 minX.toUInt32)) 4 (.i32 minY.toUInt32))
        5 (.i32 maxY.toUInt32), {}, ⟨[], [cells], []⟩⟩ =
      some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
            .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
  induction m with
  | zero =>
    intro k cells i limit minX minY maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 140 = k + 140 by omega]
    flat_step_blk f_Algorithm_life105Bounds_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_life105Bounds_prog
    unfold Algorithm.life105Bounds
    simp [hge]
  | succ m ih =>
    intro k cells i limit minX minY maxY _hn base
    rw [show k + (m + 1 + 1) * 140 = (k + (m + 1) * 140) + 140 by omega]
    flat_step_blk f_Algorithm_life105Bounds_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Bounds_prog
      let kv := cells[i.toNat]!
      let x := (kv >>> 32).toUInt32.toInt32
      let y := kv.toUInt32.toInt32
      let minX' := if x < minX then x else minX
      let minY' := if y < minY then y else minY
      have hx_def : (cells[i.toNat]! >>> 32).toUInt32.toInt32 = x := rfl
      have hy_def : cells[i.toNat]!.toUInt32.toInt32 = y := rfl
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 5 = .i32 maxY.toUInt32 →
          locs 9 = .i32 y.toUInt32 → locs 10 = .i32 (i + 1) → locs 11 = .i32 minX'.toUInt32 →
          locs 12 = .i32 minY'.toUInt32 →
          (if maxY.toUInt32.toBitVec.slt y.toUInt32.toBitVec = true then
            runJvmValFast (k2 + (m + 1) * 140 + 50) f_Algorithm_life105Bounds_prog 88
              (f_Algorithm_life105Bounds_prog.drop 88) ⟨88, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k2 + (m + 1) * 140 + 50) f_Algorithm_life105Bounds_prog 69
              (f_Algorithm_life105Bounds_prog.drop 69) ⟨69, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
                  .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
        intro k2 locs h0 h2 h5 h9 h10 h11 h12
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        unfold Algorithm.life105Bounds
        simp only [hlt, ↓reduceDIte, ui32_toInt32_x_eq, ui32_toInt32_y_eq]
        by_cases hy2 : maxY < y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h5, h9, h10, h11, h12]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          have hy2' : maxY < cells[i.toNat]!.toUInt32.toInt32 := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' minY' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h5, h9, h10, h11, h12]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          have hy2' : ¬ (maxY < cells[i.toNat]!.toUInt32.toInt32) := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' minY' maxY hnext _
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 4 = .i32 minY.toUInt32 →
          locs 5 = .i32 maxY.toUInt32 → locs 9 = .i32 y.toUInt32 → locs 10 = .i32 (i + 1) →
          locs 13 = .i32 minX'.toUInt32 →
          (if y.toUInt32.toBitVec.slt minY.toUInt32.toBitVec = true then
            runJvmValFast (k1 + (m + 1) * 140 + 80) f_Algorithm_life105Bounds_prog 62
              (f_Algorithm_life105Bounds_prog.drop 62) ⟨62, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k1 + (m + 1) * 140 + 80) f_Algorithm_life105Bounds_prog 57
              (f_Algorithm_life105Bounds_prog.drop 57) ⟨57, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
                  .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
        intro k1 locs h0 h2 h4 h5 h9 h10 h13
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hy1 : y < minY
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h9, h10, h13]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          rw [fuel_split (C := 50) k1 ((m + 1) * 140) _ (by omega)]
          have hminY : minY' = y := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h9
          · exact h10
          · rfl
          · rw [hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h9, h10, h13]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          rw [fuel_split (C := 50) k1 ((m + 1) * 140) _ (by omega)]
          have hminY : minY' = minY := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h9
          · exact h10
          · rfl
          · rw [hminY]; rfl
      rw [cellBounds_slt, shift_32_and_63, show minX.toUInt32.toInt32 = minX from int32_toUInt32_toInt32 minX, hx_def]
      by_cases hx1 : x < minX
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Bounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
        rw [fuel_split (C := 80) k ((m + 1) * 140) _ (by omega)]
        have hminX : minX' = x := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Bounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
        rw [fuel_split (C := 80) k ((m + 1) * 140) _ (by omega)]
        have hminX : minX' = minX := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Bounds_prog
      unfold Algorithm.life105Bounds
      simp [hlt]

theorem life105Bounds_equiv (cells : Array UInt64) (i limit : UInt32) (minX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 140 + 3) f_Algorithm_life105Bounds_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 minY.toUInt32), (5, .i32 maxY.toUInt32)] [] [cells]) =
      some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
            .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 140)]
  exact life105Bounds_aux (limit.toNat - i.toNat) 0 cells i limit minX minY maxY (by omega) _

private def getU64Res (p : JvmVal × JvmState) : Option (Array UInt64) :=
  match p.1 with | (.ext (.u64Ref id)) => p.2.heap.u64Arrays[id]? | _ => none

private theorem life105Rest_aux (m : Nat) :
    ∀ (k : Nat) (cells acc : Array UInt64) (minX : Int32) (i limit : UInt32)
      (u64 : List (Array UInt64)) (cellsId accId : Nat),
      u64[cellsId]? = some cells → u64[accId]? = some acc →
      (_hn : limit.toNat - i.toNat ≤ m) → ∀ (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_life105Rest_prog 6
      (f_Algorithm_life105Rest_prog.drop 6)
      ⟨6, [], setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref cellsId)))) 1 (.i32 minX.toUInt32)) 2 (.i32 i)) 3 (.i32 limit)) 4 ((.ext (.u64Ref accId))), {}, ⟨[], u64, []⟩⟩).map getU64Res =
      some (some (Algorithm.life105Rest cells minX i limit acc)) := by
  induction m with
  | zero =>
    intro k cells acc minX i limit u64 cellsId accId _hcells hacc _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 90 = k + 90 by omega]
    flat_step_blk f_Algorithm_life105Rest_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_life105Rest_prog
    unfold Algorithm.life105Rest
    simp [getU64Res, hge, hacc]
  | succ m ih =>
    intro k cells acc minX i limit u64 cellsId accId hcells hacc _hn base
    rw [show k + (m + 1 + 1) * 90 = (k + (m + 1) * 90) + 90 by omega]
    flat_step_blk f_Algorithm_life105Rest_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_nonbranch_chunks
      (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrGetU64 hcells)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Rest_prog
      rw [compareUnsigned_slt', shift_32_and_63]
      by_cases hin : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < 80
      · simp only [hin, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Rest_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 90), Nat.add_comm ((m + 1) * 90)]
        unfold Algorithm.life105Rest
        simp only [hlt, ↓reduceDIte, Algorithm.inLife105Block, cellKeyX_sub_minX, hin, decide_true, ↓reduceIte]
        exact ih _ cells acc minX (i + 1) limit u64 cellsId accId hcells hacc hnext _
      · simp only [hin, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_nonbranch_chunks
        (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step (stepStatic_u64BufPush_105 hacc)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Rest_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 90), Nat.add_comm ((m + 1) * 90)]
        unfold Algorithm.life105Rest
        simp only [hlt, ↓reduceDIte, Algorithm.inLife105Block, cellKeyX_sub_minX, hin,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        have hcells' : (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!])[cellsId]? = some cells := by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hcells).1]; exact hcells
        have hacc' : (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!])[u64.length]? =
            some (Algorithm.U64Buf.push acc cells[i.toNat]!) := by simp
        exact ih _ cells (Algorithm.U64Buf.push acc cells[i.toNat]!) minX (i + 1) limit
          (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!]) cellsId u64.length hcells' hacc' hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Rest_prog
      unfold Algorithm.life105Rest
      simp [getU64Res, hlt, hacc]

theorem life105Rest_equiv (cells acc : Array UInt64) (minX : Int32) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90 + 6) f_Algorithm_life105Rest_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 i),
        (3, .i32 limit), (4, (.ext (.u64Ref 1)))] [] [cells, acc])).map
        (fun p => match p.1 with | (.ext (.u64Ref id)) => p.2.heap.u64Arrays[id]? | _ => none) =
      some (some (Algorithm.life105Rest cells minX i limit acc)) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  change Option.map getU64Res _ = _
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact life105Rest_aux (limit.toNat - i.toNat) 0 cells acc minX i limit [cells, acc] 0 1 rfl rfl (by omega) _

private theorem cellBoundsLoop_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY maxX maxY : UInt64)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 180) f_Algorithm_cellBoundsLoop_prog 3
      (f_Algorithm_cellBoundsLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.u64Ref 0)))) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY))
        7 (.i64 maxX)) 9 (.i64 maxY), {}, ⟨[], [cells], []⟩⟩ =
      some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
            .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
  induction m with
  | zero =>
    intro k cells i limit minX minY maxX maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 180 = k + 180 by omega]
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [Algorithm.cellBoundsLoop]
    simp [hge]
  | succ m ih =>
    intro k cells i limit minX minY maxX maxY _hn base
    rw [show k + (m + 1 + 1) * 180 = (k + (m + 1) * 180) + 180 by omega]
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBoundsLoop_prog
      let kv := cells[i.toNat]!
      let x := kv >>> 32
      let y := kv &&& 4294967295
      have hx_def : cells[i.toNat]! >>> 32 = x := rfl
      have hy_def : cells[i.toNat]! &&& 4294967295 = y := rfl
      let minX' := min minX x
      let minY' := min minY y
      let maxX' := max maxX x
      have hjoin3 : ∀ k3 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 9 = .i64 maxY →
          locs 13 = .i32 (i + 1) → locs 14 = .i64 minY' → locs 16 = .i64 y →
          locs 18 = .i64 minX' → locs 20 = .i64 maxX' →
          (if (if (maxY == y) = true then (0 : UInt32) else if maxY < y then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k3 + (m + 1) * 180 + 60) f_Algorithm_cellBoundsLoop_prog 132
              (f_Algorithm_cellBoundsLoop_prog.drop 132) ⟨132, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k3 + (m + 1) * 180 + 60) f_Algorithm_cellBoundsLoop_prog 111
              (f_Algorithm_cellBoundsLoop_prog.drop 111) ⟨111, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k3 locs h0 h2 h9 h13 h14 h16 h18 h20
        rw [compareUnsigned64_sle']
        rw [Algorithm.cellBoundsLoop]
        simp only [hlt, ↓reduceDIte, keyHi_eq, keyLo_eq]
        by_cases hy2 : maxY ≤ y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h9, h13, h14, h16, h18, h20]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          have hmaxY : max maxY y = y := by rw [max_u64_eq, ite_eq_left_iff]; intro h; exact absurd hy2 h
          rw [show min minX (kv >>> 32) = minX' from rfl,
              show min minY (kv &&& 4294967295) = minY' from rfl,
              show max maxX (kv >>> 32) = maxX' from rfl,
              show max maxY (kv &&& 4294967295) = y from hmaxY]
          exact ih _ cells (i + 1) limit minX' minY' maxX' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h9, h13, h14, h16, h18, h20]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          have hmaxY : max maxY y = maxY := by rw [max_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hy2
          rw [show min minX (kv >>> 32) = minX' from rfl,
              show min minY (kv &&& 4294967295) = minY' from rfl,
              show max maxX (kv >>> 32) = maxX' from rfl,
              show max maxY (kv &&& 4294967295) = maxY from hmaxY]
          exact ih _ cells (i + 1) limit minX' minY' maxX' maxY hnext _
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 7 = .i64 maxX →
          locs 9 = .i64 maxY → locs 13 = .i32 (i + 1) → locs 22 = .i64 x →
          locs 24 = .i64 y → locs 26 = .i64 minX' → locs 28 = .i64 minY' →
          (if (if (maxX == x) = true then (0 : UInt32) else if maxX < x then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k2 + (m + 1) * 180 + 85) f_Algorithm_cellBoundsLoop_prog 99
              (f_Algorithm_cellBoundsLoop_prog.drop 99) ⟨99, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k2 + (m + 1) * 180 + 85) f_Algorithm_cellBoundsLoop_prog 90
              (f_Algorithm_cellBoundsLoop_prog.drop 90) ⟨90, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k2 locs h0 h2 h7 h9 h13 h22 h24 h26 h28
        rw [compareUnsigned64_sle']
        by_cases hx2 : maxX ≤ x
        · simp only [hx2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h7, h9, h13, h22, h24, h26, h28]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 60) k2 ((m + 1) * 180) _ (by omega)]
          have hmaxX : max maxX x = x := by rw [max_u64_eq, ite_eq_left_iff]; intro h; exact absurd hx2 h
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h9
          · exact h13
          · rfl
          · rfl
          · rfl
          · rw [show maxX' = max maxX x from rfl, hmaxX]; rfl
        · simp only [hx2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h7, h9, h13, h22, h24, h26, h28]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 60) k2 ((m + 1) * 180) _ (by omega)]
          have hmaxX : max maxX x = maxX := by rw [max_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hx2
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h9
          · exact h13
          · rfl
          · rfl
          · rfl
          · rw [show maxX' = max maxX x from rfl, hmaxX]; rfl
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = (.ext (.u64Ref 0)) → locs 2 = .i32 limit → locs 5 = .i64 minY →
          locs 7 = .i64 maxX → locs 9 = .i64 maxY → locs 13 = .i32 (i + 1) →
          locs 22 = .i64 x → locs 30 = .i64 minX' → locs 32 = .i64 y →
          (if (if (minY == y) = true then (0 : UInt32) else if minY < y then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k1 + (m + 1) * 180 + 110) f_Algorithm_cellBoundsLoop_prog 80
              (f_Algorithm_cellBoundsLoop_prog.drop 80) ⟨80, [], locs, {}, ⟨[], [cells], []⟩⟩
          else
            runJvmValFast (k1 + (m + 1) * 180 + 110) f_Algorithm_cellBoundsLoop_prog 73
              (f_Algorithm_cellBoundsLoop_prog.drop 73) ⟨73, [], locs, {}, ⟨[], [cells], []⟩⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k1 locs h0 h2 h5 h7 h9 h13 h22 h30 h32
        rw [compareUnsigned64_sle']
        by_cases hy1 : minY ≤ y
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h5, h7, h9, h13, h22, h30, h32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 85) k1 ((m + 1) * 180) _ (by omega)]
          have hminY : min minY y = minY := by rw [min_u64_eq, ite_eq_left_iff]; intro h; exact absurd hy1 h
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h7
          · exact h9
          · exact h13
          · exact h22
          · rfl
          · rfl
          · rw [show minY' = min minY y from rfl, hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h5, h7, h9, h13, h22, h30, h32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 85) k1 ((m + 1) * 180) _ (by omega)]
          have hminY : min minY y = y := by rw [min_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hy1
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h7
          · exact h9
          · exact h13
          · exact h22
          · rfl
          · rfl
          · rw [show minY' = min minY y from rfl, hminY]; rfl
      rw [compareUnsigned64_sle', shift_32_and_63, hx_def]
      by_cases hx1 : minX ≤ x
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBoundsLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
        rw [fuel_split (C := 110) k ((m + 1) * 180) _ (by omega)]
        rw [hy_def]
        have hminX : min minX x = minX := by rw [min_u64_eq, ite_eq_left_iff]; intro h; exact absurd hx1 h
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl (by rw [show minX' = min minX x from rfl, hminX]; rfl) rfl
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBoundsLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
        rw [fuel_split (C := 110) k ((m + 1) * 180) _ (by omega)]
        rw [hy_def]
        have hminX : min minX x = x := by rw [min_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hx1
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl (by rw [show minX' = min minX x from rfl, hminX]; rfl) rfl
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBoundsLoop_prog
      rw [Algorithm.cellBoundsLoop]
      simp [hlt]

theorem cellBoundsLoop_equiv (cells : Array UInt64) (i limit : UInt32) (minX minY maxX maxY : UInt64) :
    runJvm ((limit.toNat - i.toNat + 1) * 180 + 3) f_Algorithm_cellBoundsLoop_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 i), (2, .i32 limit),
        (3, .i64 minX), (5, .i64 minY), (7, .i64 maxX), (9, .i64 maxY)] [] [cells]) =
      some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
            .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 180)]
  exact cellBoundsLoop_aux (limit.toNat - i.toNat) 0 cells i limit minX minY maxX maxY (by omega) _



end Algorithm.JvmVerification
