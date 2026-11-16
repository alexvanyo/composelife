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
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.Batch3a

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

private theorem jvm_runJvmResFast_eq (f : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    Jvm.runJvmResFast algHooks f prog pc instrs st = runJvmResFast f prog pc instrs st := rfl

private theorem jvm_runJvmValFast_eq (f : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    Jvm.runJvmValFast algHooks f prog pc instrs st = runJvmValFast f prog pc instrs st := rfl

private theorem u8_sext_inj (a b : UInt8) :
    (a.toInt8.toInt32.toUInt32 = b.toInt8.toInt32.toUInt32) ↔ a = b := by
  constructor
  · intro h
    apply UInt8.eq_of_toBitVec_eq
    have hv : a.toInt8.toInt32.toUInt32.toBitVec = b.toInt8.toInt32.toUInt32.toBitVec := congrArg UInt32.toBitVec h
    bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_sext_inj.lrat"
  · intro h; subst h; rfl

private theorem initEmptyNodes_lvl_u8 (i : UInt32) :
    (UInt32.ofBitVec (BitVec.signExtend 32 (BitVec.setWidth 8 (i + 5).toBitVec))).toUInt8 = (i + 5).toUInt8 := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem u8_signExt_toUInt8 (i : UInt32) :
    (BitVec.signExtend 32 (BitVec.setWidth 8 (i + 5).toBitVec)).setWidth 8 = (i + 5).toBitVec.setWidth 8 := by
  bv_normalize

private theorem initEmptyNodesLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (fuel i : UInt32)
      (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 100) f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog 3
      (f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 ((.ext (.arenaRef 0)))) 1 (.i32 fuel)) 2 (.i32 i), {}, ⟨[arena], [], []⟩⟩).map (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initEmptyNodesLoop fuel i]) := by
  induction m with
  | zero =>
    intro k arena fuel i _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 100 = k + 100 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
    simp [hfz]
  | succ m ih =>
    intro k arena fuel i _hn base
    rw [show k + (m + 1 + 1) * 100 = (k + (m + 1) * 100) + 100 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
      simp [hfz]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      rw [compareUnsigned_sle']
      by_cases hge : (56 : UInt32) ≤ i
      · simp only [hge, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
        have hi : i ≥ 56 := hge
        rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
        simp [hfz, hi]
      · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 100), Nat.add_comm ((m + 1) * 100)]
        have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
        rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
        have hnotge : ¬ (i ≥ 56) := hge
        simp only [hfz, ↓reduceDIte, hnotge, ↓reduceIte]
        (conv => lhs; dsimp only [setArenaU32, getArenaU32, setArenaU64, getArenaU64, setArenaU8, getArenaU8])
        (try rw [initEmptyNodes_lvl_u8])
        exact ih _ _ (fuel - 1) (i + 1) hnext _

theorem initEmptyNodesLoop_equiv (arena : Algorithm.FlatHashLifeArena) (fuel i : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 100 + 3) f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 fuel), (2, .i32 i)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.initEmptyNodesLoop fuel i]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 100)]
  exact initEmptyNodesLoop_aux (fuel.toNat) 0 arena fuel i (by omega) _

private theorem slt_ite_ne_zero (c : Bool) :
    ¬ (if c = true then (4294967295 : UInt32) else 1) = 0 := by
  cases c <;> decide

private theorem probeLevel4_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64)
      (fuel : UInt32) (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 120) f_Algorithm_probeLevel4_prog 3
      (f_Algorithm_probeLevel4_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.arenaRef 0)))) 1 (.i32 head)) 2 (.i64 nw)) 4 (.i64 ne)) 6 (.i64 sw)) 8 (.i64 se))
        10 (.i32 fuel), {}, ⟨[arena], [], []⟩⟩ =
      some (.i32 (Algorithm.probeLevel4 arena head nw ne sw se fuel)) := by
  induction m with
  | zero =>
    intro k arena head nw ne sw se fuel _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 120 = k + 120 by omega]
    flat_step_blk f_Algorithm_probeLevel4_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_probeLevel4_prog
    rw [Algorithm.probeLevel4]
    simp [hfz, Algorithm.EMPTY_BUCKET]
  | succ m ih =>
    intro k arena head nw ne sw se fuel _hn base
    rw [show k + (m + 1 + 1) * 120 = (k + (m + 1) * 120) + 120 by omega]
    flat_step_blk f_Algorithm_probeLevel4_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeLevel4_prog
      rw [Algorithm.probeLevel4]
      simp [hfz, Algorithm.EMPTY_BUCKET]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeLevel4_prog
      by_cases hemp : head = 4294967295
      · have hempb : (head == 4294967295) = true := beq_iff_eq.mpr hemp
        simp only [hempb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeLevel4_prog
        rw [Algorithm.probeLevel4]
        simp [hfz, hemp, Algorithm.EMPTY_BUCKET]
      · have hempb : (head == 4294967295) = false := beq_false_of_ne hemp
        simp only [hempb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeLevel4_prog
        rw [compareUnsigned_sle']
        by_cases hoob : arena.l4Count ≤ head
        · simp only [hoob, decide_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeLevel4_prog
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hge : head ≥ arena.l4Count := hoob
          rw [Algorithm.probeLevel4]
          simp [hfz, hge, Algorithm.EMPTY_BUCKET]
        · simp only [hoob, decide_false, Bool.false_eq_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeLevel4_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hmiss : ∀ km (locs : Nat → JvmVal),
              locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 head → locs 2 = .i64 nw →
              locs 4 = .i64 ne → locs 6 = .i64 sw → locs 8 = .i64 se →
              locs 10 = .i32 fuel → locs 12 = (.ext (.arenaU32Ref 0 .l4Next)) →
              runJvmValFast (km + (m + 1) * 120 + 50) f_Algorithm_probeLevel4_prog 56
                (f_Algorithm_probeLevel4_prog.drop 56) ⟨56, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                some (.i32 (Algorithm.probeLevel4 arena arena.l4Next[head.toNat]! nw ne sw se (fuel - 1))) := by
            intro km locs h0 h1 h2 h4 h6 h8 h10 h12
            flat_step_blk f_Algorithm_probeLevel4_prog
            (conv => lhs; simp only [h0, h1, h2, h4, h6, h8, h10, h12]; dsimp only [getArenaU32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeLevel4_prog
            (conv => lhs; dsimp only [getArenaU32]; simp only [h0, h1, h2, h4, h6, h8, h10, h12])
            (conv => lhs; arg 1; jvm_whnf_blk)
            (conv => lhs; try rw [afterBlockChunk_cont]; try rw [afterBlockChunk_jump]; try rw [afterBlockChunk_done])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
            flat_step_blk f_Algorithm_probeLevel4_prog
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm km ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
            exact ih _ arena arena.l4Next[head.toNat]! nw ne sw se (fuel - 1) hnext _
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hnotge : ¬ (head ≥ arena.l4Count) := hoob
          by_cases hnw : arena.l4Nw[head.toNat]! = nw
          · have hnwb : (arena.l4Nw[head.toNat]! == nw) = true := beq_iff_eq.mpr hnw
            (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hnwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeLevel4_prog
            by_cases hne : arena.l4Ne[head.toNat]! = ne
            · have hneb : (arena.l4Ne[head.toNat]! == ne) = true := beq_iff_eq.mpr hne
              (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hneb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_probeLevel4_prog
              by_cases hsw : arena.l4Sw[head.toNat]! = sw
              · have hswb : (arena.l4Sw[head.toNat]! == sw) = true := beq_iff_eq.mpr hsw
                (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hswb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_probeLevel4_prog
                by_cases hse : arena.l4Se[head.toNat]! = se
                · have hseb : (arena.l4Se[head.toNat]! == se) = true := beq_iff_eq.mpr hse
                  (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hseb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_probeLevel4_prog
                  rw [Algorithm.probeLevel4]
                  simp [hfz, hemp', hnotge, hnwb, hneb, hswb, hseb]
                · have hseb : (arena.l4Se[head.toNat]! == se) = false := beq_false_of_ne hse
                  (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hseb, Bool.not_false, ↓reduceIte])
                  try simp only [Nat.succ_eq_add_one]
                  try simp only [nat_add_eq]
                  simp only [Nat.add_assoc]
                  rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
                  rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
                  rw [Algorithm.probeLevel4]
                  simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                    hnwb, hneb, hswb, hseb, Bool.and_false]
                  refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
              · have hswb : (arena.l4Sw[head.toNat]! == sw) = false := beq_false_of_ne hsw
                (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hswb, Bool.not_false, ↓reduceIte])
                try simp only [Nat.succ_eq_add_one]
                try simp only [nat_add_eq]
                simp only [Nat.add_assoc]
                rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
                rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
                rw [Algorithm.probeLevel4]
                simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                  hnwb, hneb, hswb, Bool.and_false, Bool.false_and]
                refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
            · have hneb : (arena.l4Ne[head.toNat]! == ne) = false := beq_false_of_ne hne
              (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hneb, Bool.not_false, ↓reduceIte])
              try simp only [Nat.succ_eq_add_one]
              try simp only [nat_add_eq]
              simp only [Nat.add_assoc]
              rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
              rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
              rw [Algorithm.probeLevel4]
              simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                hnwb, hneb, Bool.and_false, Bool.false_and]
              refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
          · have hnwb : (arena.l4Nw[head.toNat]! == nw) = false := beq_false_of_ne hnw
            (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hnwb, Bool.not_false, ↓reduceIte])
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
            rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
            rw [Algorithm.probeLevel4]
            simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
              hnwb, Bool.false_and]
            refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

theorem probeLevel4_equiv (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64) (fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 120 + 3) f_Algorithm_probeLevel4_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 head), (2, .i64 nw), (4, .i64 ne), (6, .i64 sw),
        (8, .i64 se), (10, .i32 fuel)] [arena]) =
      some (.i32 (Algorithm.probeLevel4 arena head nw ne sw se fuel)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 120)]
  exact probeLevel4_aux (fuel.toNat) 0 arena head nw ne sw se fuel (by omega) _

private theorem probeCellNode_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (lvl : UInt8)
      (nw ne sw se fuel : UInt32) (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 130) f_Algorithm_probeCellNode_prog 3
      (f_Algorithm_probeCellNode_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 ((.ext (.arenaRef 0)))) 1 (.i32 head)) 2 (.i32 lvl.toInt8.toInt32.toUInt32)) 3 (.i32 nw))
        4 (.i32 ne)) 5 (.i32 sw)) 6 (.i32 se)) 7 (.i32 fuel), {}, ⟨[arena], [], []⟩⟩ =
      some (.i32 (Algorithm.probeCellNode arena head lvl nw ne sw se fuel)) := by
  induction m with
  | zero =>
    intro k arena head lvl nw ne sw se fuel _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 130 = k + 130 by omega]
    flat_step_blk f_Algorithm_probeCellNode_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_probeCellNode_prog
    rw [Algorithm.probeCellNode]
    simp [hfz, Algorithm.EMPTY_BUCKET]
  | succ m ih =>
    intro k arena head lvl nw ne sw se fuel _hn base
    rw [show k + (m + 1 + 1) * 130 = (k + (m + 1) * 130) + 130 by omega]
    flat_step_blk f_Algorithm_probeCellNode_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeCellNode_prog
      rw [Algorithm.probeCellNode]
      simp [hfz, Algorithm.EMPTY_BUCKET]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeCellNode_prog
      by_cases hemp : head = 4294967295
      · have hempb : (head == 4294967295) = true := beq_iff_eq.mpr hemp
        simp only [hempb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeCellNode_prog
        rw [Algorithm.probeCellNode]
        simp [hfz, hemp, Algorithm.EMPTY_BUCKET]
      · have hempb : (head == 4294967295) = false := beq_false_of_ne hemp
        simp only [hempb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeCellNode_prog
        rw [compareUnsigned_sle']
        by_cases hoob : arena.cellCount ≤ head
        · simp only [hoob, decide_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeCellNode_prog
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hge : head ≥ arena.cellCount := hoob
          rw [Algorithm.probeCellNode]
          simp [hfz, hge, Algorithm.EMPTY_BUCKET]
        · simp only [hoob, decide_false, Bool.false_eq_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeCellNode_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hmiss : ∀ km (locs : Nat → JvmVal),
              locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 head → locs 2 = .i32 lvl.toInt8.toInt32.toUInt32 →
              locs 3 = .i32 nw → locs 4 = .i32 ne → locs 5 = .i32 sw → locs 6 = .i32 se →
              locs 7 = .i32 fuel → locs 9 = (.ext (.arenaU32Ref 0 .cellNext)) →
              runJvmValFast (km + (m + 1) * 130 + 50) f_Algorithm_probeCellNode_prog 60
                (f_Algorithm_probeCellNode_prog.drop 60) ⟨60, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                some (.i32 (Algorithm.probeCellNode arena arena.cellNext[head.toNat]! lvl nw ne sw se (fuel - 1))) := by
            intro km locs h0 h1 h2 h3 h4 h5 h6 h7 h9
            flat_step_blk f_Algorithm_probeCellNode_prog
            (conv => lhs; simp only [h0, h1, h2, h3, h4, h5, h6, h7, h9]; dsimp only [getArenaU32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeCellNode_prog
            (conv => lhs; dsimp only [getArenaU32]; simp only [h0, h1, h2, h3, h4, h5, h6, h7, h9])
            (conv => lhs; arg 1; jvm_whnf_blk)
            (conv => lhs; try rw [afterBlockChunk_cont]; try rw [afterBlockChunk_jump]; try rw [afterBlockChunk_done])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
            flat_step_blk f_Algorithm_probeCellNode_prog
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm km ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
            exact ih _ arena arena.cellNext[head.toNat]! lvl nw ne sw se (fuel - 1) hnext _
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hnotge : ¬ (head ≥ arena.cellCount) := hoob
          by_cases hlvl : arena.cellLevel[head.toNat]! = lvl
          · have hlvlb : (arena.cellLevel[head.toNat]! == lvl) = true := beq_iff_eq.mpr hlvl
            have hlvls : arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 = lvl.toInt8.toInt32.toUInt32 :=
              (u8_sext_inj _ _).mpr hlvl
            (conv => lhs; dsimp only [getArenaU8]; simp only [hlvls, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeCellNode_prog
            by_cases hnw : arena.cellNw[head.toNat]! = nw
            · have hnwb : (arena.cellNw[head.toNat]! == nw) = true := beq_iff_eq.mpr hnw
              (conv => lhs; dsimp only [getArenaU32]; simp only [hnwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_probeCellNode_prog
              by_cases hne : arena.cellNe[head.toNat]! = ne
              · have hneb : (arena.cellNe[head.toNat]! == ne) = true := beq_iff_eq.mpr hne
                (conv => lhs; dsimp only [getArenaU32]; simp only [hneb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_probeCellNode_prog
                by_cases hsw : arena.cellSw[head.toNat]! = sw
                · have hswb : (arena.cellSw[head.toNat]! == sw) = true := beq_iff_eq.mpr hsw
                  (conv => lhs; dsimp only [getArenaU32]; simp only [hswb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_probeCellNode_prog
                  by_cases hse : arena.cellSe[head.toNat]! = se
                  · have hseb : (arena.cellSe[head.toNat]! == se) = true := beq_iff_eq.mpr hse
                    (conv => lhs; dsimp only [getArenaU32]; simp only [hseb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_probeCellNode_prog
                    rw [Algorithm.probeCellNode]
                    simp [hfz, hemp', hnotge, hlvlb, hnwb, hneb, hswb, hseb]
                  · have hseb : (arena.cellSe[head.toNat]! == se) = false := beq_false_of_ne hse
                    (conv => lhs; dsimp only [getArenaU32]; simp only [hseb, Bool.not_false, ↓reduceIte])
                    try simp only [Nat.succ_eq_add_one]
                    try simp only [nat_add_eq]
                    simp only [Nat.add_assoc]
                    rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                    rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                    rw [Algorithm.probeCellNode]
                    simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                      hlvlb, hnwb, hneb, hswb, hseb, Bool.and_false]
                    refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
                · have hswb : (arena.cellSw[head.toNat]! == sw) = false := beq_false_of_ne hsw
                  (conv => lhs; dsimp only [getArenaU32]; simp only [hswb, Bool.not_false, ↓reduceIte])
                  try simp only [Nat.succ_eq_add_one]
                  try simp only [nat_add_eq]
                  simp only [Nat.add_assoc]
                  rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                  rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                  rw [Algorithm.probeCellNode]
                  simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                    hlvlb, hnwb, hneb, hswb, Bool.and_false, Bool.false_and]
                  refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
              · have hneb : (arena.cellNe[head.toNat]! == ne) = false := beq_false_of_ne hne
                (conv => lhs; dsimp only [getArenaU32]; simp only [hneb, Bool.not_false, ↓reduceIte])
                try simp only [Nat.succ_eq_add_one]
                try simp only [nat_add_eq]
                simp only [Nat.add_assoc]
                rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                rw [Algorithm.probeCellNode]
                simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                  hlvlb, hnwb, hneb, Bool.and_false, Bool.false_and]
                refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
            · have hnwb : (arena.cellNw[head.toNat]! == nw) = false := beq_false_of_ne hnw
              (conv => lhs; dsimp only [getArenaU32]; simp only [hnwb, Bool.not_false, ↓reduceIte])
              try simp only [Nat.succ_eq_add_one]
              try simp only [nat_add_eq]
              simp only [Nat.add_assoc]
              rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
              rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
              rw [Algorithm.probeCellNode]
              simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                hlvlb, hnwb, Bool.and_false, Bool.false_and]
              refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
          · have hlvlb : (arena.cellLevel[head.toNat]! == lvl) = false := beq_false_of_ne hlvl
            have hlvls : arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 ≠ lvl.toInt8.toInt32.toUInt32 :=
              mt (u8_sext_inj _ _).mp hlvl
            have hlvlsb : (arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 == lvl.toInt8.toInt32.toUInt32) = false :=
              beq_false_of_ne hlvls
            (conv => lhs; dsimp only [getArenaU8]; simp only [hlvlsb, Bool.not_false, ↓reduceIte])
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
            rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
            rw [Algorithm.probeCellNode]
            simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
              hlvlb, Bool.false_and]
            refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

theorem probeCellNode_equiv (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (lvl : UInt8)
    (nw ne sw se fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 130 + 3) f_Algorithm_probeCellNode_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 head), (2, .i32 lvl.toInt8.toInt32.toUInt32),
        (3, .i32 nw), (4, .i32 ne), (5, .i32 sw), (6, .i32 se), (7, .i32 fuel)] [arena]) =
      some (.i32 (Algorithm.probeCellNode arena head lvl nw ne sw se fuel)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 130)]
  exact probeCellNode_aux (fuel.toNat) 0 arena head lvl nw ne sw se fuel (by omega) _

private theorem bool_i32_ne_zero (b : Bool) :
    ((if b then (1 : UInt32) else 0) != 0) = b := by
  cases b <;> rfl

private theorem u8_sext_toUInt8_id (a : UInt8) :
    a.toInt8.toInt32.toUInt32.toUInt8 = a := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem u8_sext_band255 (a : UInt8) :
    (a.toInt8.toInt32.toUInt32 &&& 255) = a.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_sext_band255.lrat"

private theorem u8_band255_sle_5 (a : UInt8) :
    ((if (a.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
      else if (a.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) ↔
      a ≤ 5 := by
  rw [UInt8.le_iff_toBitVec_le]
  bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_band255_sle_5.lrat"

private theorem lshl_63_mask (k : UInt32) :
    ((1 : UInt64) <<< (k &&& 63).toUInt64) = (1 <<< k.toUInt64) := by
  apply UInt64.eq_of_toBitVec_eq; bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lshl_63_mask.lrat"

private theorem lcmp_slt_zero_int64 (a b : Int64) :
    ((if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.slt 0#32) ↔
      a < b := by
  rw [Int64.lt_iff_toBitVec_slt]
  change ((if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.slt 0#32) ↔ _
  bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_slt_zero_int64.lrat"

private theorem lcmp_sle_zero_int64 (a b : Int64) :
    ((if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) ↔
      a ≤ b := by
  rw [Int64.le_iff_toBitVec_sle]
  change ((if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) ↔ _
  bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_sle_zero_int64.lrat"

private theorem lcmp_sgt_zero_int64 (a b : Int64) :
    ((0#32).slt (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec) ↔
      ¬ (a ≤ b) := by
  rw [Int64.le_iff_toBitVec_sle]
  change ((0#32).slt (if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec) ↔ _
  bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_sgt_zero_int64.lrat"

private theorem int64_toUInt64_sub (a b : Int64) :
    (a - b).toUInt64 = a.toUInt64 - b.toUInt64 :=
  Int64.toUInt64_sub a b

private theorem copyCellFromLoop_aux (m : Nat) :
    ∀ (k : Nat) (dst src : Algorithm.FlatHashLifeArena) (copyMemos : Bool) (stackBase sp fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        (runJvmResFast (k + (m + 1) * 140) f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog 6
          (f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog.drop 6)
          ⟨6, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
            0 ((.ext (.arenaRef 0)))) 1 ((.ext (.arenaRef 1)))) 2 (.i32 (if copyMemos then 1 else 0)))
            3 (.i32 stackBase)) 4 (.i32 sp)) 5 (.i32 fuel), {}, ⟨[dst, src], [], []⟩⟩).map
          (fun p => (p.1, p.2.heap.arenas)) =
          some (.unit, [dst.copyCellFromLoop src copyMemos stackBase sp fuel, src]) := by
  induction m with
  | zero =>
    intro k dst src copyMemos stackBase sp fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 140 = k + 140 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
    simp only [hfz, ↓reduceDIte]
  | succ m ih =>
    intro k dst src copyMemos stackBase sp fuel hn base
    rw [show k + (m + 1 + 1) * 140 = (k + (m + 1) * 140) + 140 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
      simp only [hfz, ↓reduceDIte]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      by_cases hspz : sp = 0
      · have hspzb : (sp == 0) = true := beq_iff_eq.mpr hspz
        (conv => lhs; rw [ite_eq_left (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
        rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
        simp [hfz, hspzb]
      · have hspzb : (sp == 0) = false := beq_false_of_ne hspz
        (conv => lhs; rw [ite_eq_right (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
        by_cases hovf : dst.overflow = 0
        · have hovfb : (dst.overflow != 0) = false := by simp [hovf]
          have hovfs : (dst.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf
          (conv => lhs; rw [ite_eq_left (by simp only [hovfs])])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hcm : ((if copyMemos then (1 : UInt32) else 0) != 0) = copyMemos := by
            cases copyMemos <;> rfl
          let cellId := Algorithm.getRemapCell dst (stackBase + sp - 1)
          by_cases hoob : src.cellCount ≤ cellId
          · have hoobb : cellId ≥ src.cellCount := hoob
            (conv => lhs; rw [ite_eq_left (by simp only [compareUnsigned_sle', cellId, hoob, decide_true])])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
            rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
            rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
            change _ = some (JvmVal.unit,
              [(if src.cellCount ≤ cellId then
                  dst.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
                else _), src])
            simp only [hoobb, ↓reduceIte]
            exact ih _ dst src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
          · have hoobb : ¬ (cellId ≥ src.cellCount) := hoob
            (conv => lhs; rw [ite_eq_right (by simp only [compareUnsigned_sle', cellId, hoob, decide_false]; decide)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
            by_cases hrem : Algorithm.getRemapCell dst cellId = Algorithm.UNCOMPUTED
            · have hremb : (Algorithm.getRemapCell dst cellId != Algorithm.UNCOMPUTED) = false := by
                simp [hrem, Algorithm.UNCOMPUTED]
              have hrems : (Algorithm.getRemapCell dst cellId == 4294967295) = true := by
                simp [hrem, Algorithm.UNCOMPUTED]
              (conv => lhs; rw [ite_eq_left (by simp only [cellId, hrems])])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
              simp only [hcm]
              let resPair := Algorithm.copyCellTryStep dst src cellId copyMemos
              let missingChild := resPair.1
              let d1 := resPair.2
              by_cases hovf1 : d1.overflow = 0
              · have hovf1b : (d1.overflow != 0) = false := by simp [hovf1]
                have hovf1s : (d1.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf1
                (conv => lhs; rw [ite_eq_left (by simp only [d1, resPair, cellId, hovf1s])])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                by_cases hmiss : missingChild = Algorithm.UNCOMPUTED
                · have hmissb : (missingChild == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hmiss
                  have hmisss : (missingChild == 4294967295) = true := by simp [hmiss, Algorithm.UNCOMPUTED]
                  (conv => lhs; rw [ite_eq_left (by simp only [missingChild, resPair, cellId, hmisss])])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                  try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                    dsimp only
                    simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                    rw [show ((d1.overflow != 0) = false) from hovf1b]
                    rw [show ((missingChild == Algorithm.UNCOMPUTED) = true) from hmissb]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                  exact ih _ d1 src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
                · have hmissb : (missingChild == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hmiss
                  have hmisss : (missingChild == 4294967295) = false := by
                    simpa [Algorithm.UNCOMPUTED] using hmissb
                  (conv => lhs; rw [ite_eq_right (by simp only [missingChild, resPair, cellId, hmisss]; decide)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                  by_cases hdepth : Algorithm.copyStackDepth ≤ sp
                  · have hdepths : (256 : UInt32) ≤ sp := hdepth
                    (conv => lhs; rw [ite_eq_left (by simp only [compareUnsigned_sle', hdepths, decide_true])])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                    try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                      rw [show ((d1.overflow != 0) = false) from hovf1b]
                      rw [show ((missingChild == Algorithm.UNCOMPUTED) = false) from hmissb]
                      simp only [Bool.false_eq_true, ↓reduceIte, hdepth]
                    exact ih _ d1 src copyMemos stackBase 0 (fuel - 1) hnext _
                  · have hdepths : ¬ ((256 : UInt32) ≤ sp) := hdepth
                    (conv => lhs; rw [ite_eq_right (by simp only [compareUnsigned_sle', hdepths, decide_false]; decide)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                    try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                      rw [show ((d1.overflow != 0) = false) from hovf1b]
                      rw [show ((missingChild == Algorithm.UNCOMPUTED) = false) from hmissb]
                      simp only [Bool.false_eq_true, ↓reduceIte, hdepth]
                    exact ih _ (d1.setRemapCell (stackBase + sp) missingChild) src copyMemos
                      stackBase (sp + 1) (fuel - 1) hnext _
              · have hovf1b : (d1.overflow != 0) = true := by simp [hovf1]
                have hovf1s : (d1.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
                  rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf1
                (conv => lhs; rw [ite_eq_right (by simp only [d1, resPair, cellId, hovf1s]; decide)])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                  dsimp only
                  simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                  rw [show ((d1.overflow != 0) = true) from hovf1b]
                  simp only [↓reduceIte]
                exact ih _ d1 src copyMemos stackBase 0 (fuel - 1) hnext _
            · have hremb : (Algorithm.getRemapCell dst cellId != Algorithm.UNCOMPUTED) = true := bne_iff_ne.mpr hrem
              have hrems : (Algorithm.getRemapCell dst cellId == 4294967295) = false := by
                simpa [Algorithm.UNCOMPUTED] using beq_false_of_ne hrem
              (conv => lhs; rw [ite_eq_right (by simp only [cellId, hrems]; decide)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
              try dsimp only [cellId] at hoobb hremb
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
              exact ih _ dst src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
        · have hovfb : (dst.overflow != 0) = true := by simp [hovf]
          have hovfs : (dst.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
            rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf
          (conv => lhs; rw [ite_eq_right (by simp only [hovfs]; decide)])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
          rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
          simp [hfz, hspzb, hovfb]

theorem copyCellFromLoop_equiv (dst src : Algorithm.FlatHashLifeArena) (copyMemos : Bool)
    (stackBase sp fuel : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 140 + 6) f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, (.ext (.arenaRef 1))), (2, .i32 (if copyMemos then 1 else 0)),
        (3, .i32 stackBase), (4, .i32 sp), (5, .i32 fuel)] [dst, src])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [dst.copyCellFromLoop src copyMemos stackBase sp fuel, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; norm_jvm_locals)
  rw [← Nat.zero_add ((fuel.toNat + 1) * 140)]
  exact copyCellFromLoop_aux fuel.toNat 0 dst src copyMemos stackBase sp fuel (Nat.le_refl _) _

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
private theorem stepCellSerialLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (sp stackLimit fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        (runJvmResFast (k + (m + 1) * 250) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 3
          (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 3)
          ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.arenaRef 0)))) 1 (.i32 sp))
            2 (.i32 stackLimit)) 3 (.i32 fuel), {}, ⟨[arena], [], []⟩⟩).map
          (fun p => (p.1, p.2.heap.arenas)) =
          some (.unit, [arena.stepCellSerialLoop sp stackLimit fuel]) := by
  induction m with
  | zero =>
    intro k arena sp stackLimit fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 250 = k + 250 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
    simp only [hfz, ↓reduceDIte]
  | succ m ih =>
    intro k arena sp stackLimit fuel hn base
    rw [show k + (m + 1 + 1) * 250 = (k + (m + 1) * 250) + 250 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
      simp only [hfz, ↓reduceDIte]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      by_cases hspz : sp = 0
      · have hspzb : (sp == 0) = true := beq_iff_eq.mpr hspz
        (conv => lhs; rw [ite_eq_left (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
        rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
        simp [hfz, hspzb]
      · have hspzb : (sp == 0) = false := beq_false_of_ne hspz
        (conv => lhs; rw [ite_eq_right (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
        by_cases hovf : arena.overflow = 0
        · have hovfb : (arena.overflow != 0) = false := by simp [hovf]
          have hovfs : (arena.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf
          (conv => lhs; rw [ite_eq_left (by simp only [hovfs])])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          let fbase := (sp - 1) * Algorithm.stepFrameWidth
          let nodeId := arena.remapL4[fbase.toNat]!
          by_cases hoob : arena.cellCount ≤ nodeId
          · have hoobb : nodeId ≥ arena.cellCount := hoob
            (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hoob)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
            rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
            conv =>
              rhs
              rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
              dsimp only
              simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
            change _ = some (JvmVal.unit,
              [(if arena.cellCount ≤ nodeId then
                  arena.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
                else _)])
            rw [ite_eq_left (by dsimp only [nodeId, fbase, Algorithm.stepFrameWidth] at hoobb; exact hoobb)]
            exact ih _ arena (sp - 1) stackLimit (fuel - 1) hnext _
          · have hoobb : ¬ (nodeId ≥ arena.cellCount) := hoob
            (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false (by dsimp only [nodeId, fbase, Algorithm.stepFrameWidth] at hoob; exact hoob)]; exact Bool.false_ne_true)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
            by_cases hres : arena.cellStepRes[nodeId.toNat]! = Algorithm.UNCOMPUTED
            · have hresb : (arena.cellStepRes[nodeId.toNat]! != Algorithm.UNCOMPUTED) = false := by
                simp [hres, Algorithm.UNCOMPUTED]
              have hress : (arena.cellStepRes[nodeId.toNat]! == 4294967295) = true := by
                simp [hres, Algorithm.UNCOMPUTED]
              (conv => lhs; rw [ite_eq_left (by exact hress)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
              let lvl := arena.cellLevel[nodeId.toNat]!
              by_cases hlvl : lvl ≤ 5
              · have hlvls : ((if (lvl.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
                    else if (lvl.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (u8_band255_sle_5 lvl).mpr hlvl
                (conv => lhs; rw [ite_eq_left (by exact hlvls)])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                dsimp only [fbase, nodeId, lvl] at hoobb hresb hlvl
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                  dsimp only
                  simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl]
                exact ih _ (arena.stepLevel5 nodeId).2 (sp - 1) stackLimit (fuel - 1) hnext _
              · have hlvls : ((if (lvl.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
                    else if (lvl.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (u8_band255_sle_5 lvl).mp hlvl)
                (conv => lhs; rw [ite_eq_right (by intro h; simp only [getArenaU8, getArenaU32] at h; exact Bool.false_ne_true (hlvls.symm.trans h))])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                let a4 := arena.expandFrameIfNeeded nodeId fbase
                by_cases hov4 : a4.overflow = 0
                · have hov4b : (a4.overflow != 0) = false := by simp [hov4]
                  have hov4s : (a4.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hov4
                  (conv => lhs; rw [ite_eq_left (by exact hov4s)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                  let q_nw := a4.remapL4[(fbase + 1).toNat]!
                  let q_ne := a4.remapL4[(fbase + 2).toNat]!
                  let q_sw := a4.remapL4[(fbase + 3).toNat]!
                  let q_se := a4.remapL4[(fbase + 4).toNat]!
                  let r_nw := Algorithm.getCellStepRes a4 q_nw
                  let r_ne := Algorithm.getCellStepRes a4 q_ne
                  let r_sw := Algorithm.getCellStepRes a4 q_sw
                  let r_se := Algorithm.getCellStepRes a4 q_se
                  have hpush : ∀ km (child : UInt32) (locs : Nat → JvmVal),
                      locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 sp → locs 2 = .i32 stackLimit →
                      locs 3 = .i32 fuel → locs 15 = .i32 (sp * 5) →
                      (runJvmResFast (km + (m + 1) * 250 + 50) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 249
                        (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 249)
                        ⟨249, [.i32 child, .i32 (sp * 5), (.ext (.arenaRef 0))], locs, {}, ⟨[a4], [], []⟩⟩).map (fun p => (p.1, p.2.heap.arenas)) =
                        some (.unit, [((a4.setRemapL4 (sp * Algorithm.stepFrameWidth) child).setRemapL4
                          (sp * Algorithm.stepFrameWidth + 1) Algorithm.UNCOMPUTED).stepCellSerialLoop
                            (sp + 1) stackLimit (fuel - 1)]) := by
                    intro km child locs h0 h1 h2 h3 h15
                    have hdrop249 : f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 249 =
                        [.invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V", .iload 15, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 16, .aload 0, .iload 16, .iconst 4294967295, .invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V", .iload 1, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 17, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 18, .aload 0, .astore 19, .iload 2, .istore 20, .aload 19, .astore 0, .iload 17, .istore 1, .iload 20, .istore 2, .iload 18, .istore 3, .goto 3, .aload 0, .iload 11, .invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I", .istore 13, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 14, .aload 0, .astore 15, .iload 2, .istore 16, .aload 15, .astore 0, .iload 5, .istore 1, .iload 16, .istore 2, .iload 14, .istore 3, .goto 3, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 12, .aload 0, .astore 13, .iload 2, .istore 14, .aload 13, .astore 0, .iload 5, .istore 1, .iload 14, .istore 2, .iload 12, .istore 3, .goto 3, .vreturn, .vreturn] := by rfl
                    (conv => lhs; arg 2; rw [hdrop249])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; simp only [h0, h1, h2, h3, h15])
                    (conv => lhs; arg 2; arg 1; jvm_whnf_blk)
                    (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    iterate 3 (
                      (conv => lhs; arg 2; try simp only [h0, h1, h2, h3, h15])
                      (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                      (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog)
                    (conv => lhs; arg 2; try simp only [h0, h1, h2, h3, h15])
                    (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                    (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                    exact ih _ _ (sp + 1) stackLimit (fuel - 1) hnext _
                  have hneedchild : ∀ km (locs : Nat → JvmVal),
                      locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 sp → locs 2 = .i32 stackLimit →
                      locs 3 = .i32 fuel → locs 16 = .i32 q_nw → locs 17 = .i32 q_ne →
                      locs 18 = .i32 q_sw → locs 19 = .i32 q_se →
                      locs 21 = .i32 r_ne → locs 22 = .i32 r_sw →
                      locs 23 = .i32 (if r_nw = Algorithm.UNCOMPUTED then 1 else 0) →
                      (runJvmResFast (km + (m + 1) * 250 + 110) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 199
                        (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 199)
                        ⟨199, [], locs, {}, ⟨[a4], [], []⟩⟩).map (fun p => (p.1, p.2.heap.arenas)) =
                        some (.unit, [if sp ≥ stackLimit then a4.stepCellSerialLoop 0 stackLimit (fuel - 1)
                          else ((a4.setRemapL4 (sp * Algorithm.stepFrameWidth)
                            (if r_nw == Algorithm.UNCOMPUTED then q_nw else if r_ne == Algorithm.UNCOMPUTED then q_ne
                              else if r_sw == Algorithm.UNCOMPUTED then q_sw else q_se)).setRemapL4
                            (sp * Algorithm.stepFrameWidth + 1) Algorithm.UNCOMPUTED).stepCellSerialLoop
                            (sp + 1) stackLimit (fuel - 1)]) := by
                    intro km locs h0 h1 h2 h3 h16 h17 h18 h19 h21 h22 h23
                    (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19, h21, h22, h23]); (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; simp only [h1, h2])
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    by_cases hlim : stackLimit ≤ sp
                    · (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hlim)])
                      (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      (conv => lhs; arg 2; simp only [h0, h1, h2, h3])
                      (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                      (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      (conv => lhs; arg 2; simp only [h0, h2])
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                      have hlims : sp ≥ stackLimit := hlim
                      (conv => rhs; simp only [hlims, ↓reduceIte])
                      exact ih _ a4 0 stackLimit (fuel - 1) hnext _
                    · (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false hlim]; exact Bool.false_ne_true)])
                      (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19, h21, h22, h23])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      (conv => lhs; arg 2; simp only [h23])
                      (conv => lhs; arg 2; dsimp only [evalResBranchInstrCons])
                      (conv => lhs; rw [Jvm.evalResBranchInstrCons_ifne, jvm_runJvmResFast_eq, jvm_runJvmResFast_eq, option_map_ite])
                      have hlims : ¬ (sp ≥ stackLimit) := hlim
                      (conv => rhs; simp only [hlims, ↓reduceIte])
                      by_cases hrnw : r_nw = Algorithm.UNCOMPUTED
                      · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrnw
                        (conv => lhs; rw [ite_eq_left (by simp only [hrnw]; decide)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        (conv => lhs; arg 2; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                        (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                        (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                        rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                        rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                        (conv => rhs; simp only [hrnwb, ↓reduceIte])
                        (conv => lhs; arg 2; try simp only [h0])
                        refine hpush _ q_nw _ ?_ ?_ ?_ ?_ ?_
                        all_goals simp [setLocal, h0, h1, h2, h3]
                      · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrnw
                        (conv => lhs; rw [ite_eq_right (by simp only [hrnw]; decide)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        (conv => lhs; arg 2; simp only [h21])
                        (conv => lhs; arg 2; dsimp only [evalResBranchInstrCons])
                        (conv => lhs; rw [Jvm.evalResBranchInstrCons_if_icmpeq, jvm_runJvmResFast_eq, jvm_runJvmResFast_eq, option_map_ite])
                        by_cases hrne : r_ne = Algorithm.UNCOMPUTED
                        · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrne
                          have hrnes : (r_ne == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrneb
                          (conv => lhs; rw [ite_eq_left (by exact hrnes)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                          (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                          (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                          (conv => rhs; simp only [hrnwb, hrneb, Bool.false_eq_true, ↓reduceIte])
                          (conv => lhs; arg 2; try simp only [h0])
                          refine hpush _ q_ne _ ?_ ?_ ?_ ?_ ?_
                          all_goals simp [setLocal, h0, h1, h2, h3]
                        · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrne
                          have hrnes : (r_ne == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrneb
                          (conv => lhs; rw [ite_eq_right (by simp only [hrnes]; exact Bool.false_ne_true)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; simp only [h22])
                          (conv => lhs; arg 2; dsimp only [evalResBranchInstrCons])
                          (conv => lhs; rw [Jvm.evalResBranchInstrCons_if_icmpeq, jvm_runJvmResFast_eq, jvm_runJvmResFast_eq, option_map_ite])
                          by_cases hrsw : r_sw = Algorithm.UNCOMPUTED
                          · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrsw
                            have hrsws : (r_sw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrswb
                            (conv => lhs; rw [ite_eq_left (by exact hrsws)])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                            (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                            (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                            rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                            rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                            (conv => rhs; simp only [hrnwb, hrneb, hrswb, Bool.false_eq_true, ↓reduceIte])
                            (conv => lhs; arg 2; try simp only [h0])
                            refine hpush _ q_sw _ ?_ ?_ ?_ ?_ ?_
                            all_goals simp [setLocal, h0, h1, h2, h3]
                          · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrsw
                            have hrsws : (r_sw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrswb
                            (conv => lhs; rw [ite_eq_right (by simp only [hrsws]; exact Bool.false_ne_true)])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                            (conv => lhs; arg 2; try (arg 1; jvm_whnf_blk))
                            (conv => lhs; arg 2; try rw [afterResBlockChunk_cont]; try rw [afterResBlockChunk_jump]; try rw [afterResBlockChunk_done])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                            rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                            rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                            (conv => rhs; simp only [hrnwb, hrneb, hrswb, Bool.false_eq_true, ↓reduceIte])
                            (conv => lhs; arg 2; try simp only [h0])
                            refine hpush _ q_se _ ?_ ?_ ?_ ?_ ?_
                            all_goals simp [setLocal, h0, h1, h2, h3]
                  by_cases hrnw : r_nw = Algorithm.UNCOMPUTED
                  · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrnw
                    have hrnws : (r_nw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrnwb
                    (conv => lhs; rw [ite_eq_right (by change ¬ ((! (r_nw == 4294967295)) = true); rw [hrnws]; exact Bool.false_ne_true)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                    rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                    dsimp only [nodeId, fbase, lvl, a4, q_nw, r_nw] at hoobb hresb hlvl hov4b hrnwb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                      rw [ite_eq_left (by simp only [hrnwb, Bool.true_or])]
                    refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    all_goals try rfl
                    simp [setLocal, hrnw]
                  · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrnw
                    have hrnws : (r_nw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrnwb
                    (conv => lhs; rw [ite_eq_left (by change (! (r_nw == 4294967295)) = true; rw [hrnws]; rfl)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    by_cases hrne : r_ne = Algorithm.UNCOMPUTED
                    · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrne
                      have hrnes : (r_ne == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrneb
                      (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_ne == 4294967295) = true; exact hrnes)])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                      rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                      dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, r_nw, r_ne] at hoobb hresb hlvl hov4b hrnwb hrneb
                      conv =>
                        rhs
                        rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                        dsimp only
                        simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                        rw [ite_eq_left (by simp only [hrneb, Bool.true_or, Bool.or_true])]
                      refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      all_goals try rfl
                      simp [setLocal, hrnw]
                    · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrne
                      have hrnes : (r_ne == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrneb
                      (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_ne == 4294967295) = true); rw [hrnes]; exact Bool.false_ne_true)])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      by_cases hrsw : r_sw = Algorithm.UNCOMPUTED
                      · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrsw
                        have hrsws : (r_sw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrswb
                        (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_sw == 4294967295) = true; exact hrsws)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                        rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                        rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                        dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, r_nw, r_ne, r_sw] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb
                        conv =>
                          rhs
                          rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                          dsimp only
                          simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                          rw [ite_eq_left (by simp only [hrswb, Bool.true_or, Bool.or_true])]
                        refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                        all_goals try rfl
                        simp [setLocal, hrnw]
                      · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrsw
                        have hrsws : (r_sw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrswb
                        (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_sw == 4294967295) = true); rw [hrsws]; exact Bool.false_ne_true)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        by_cases hrse : r_se = Algorithm.UNCOMPUTED
                        · have hrseb : (r_se == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrse
                          have hrses : (r_se == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrseb
                          (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_se == 4294967295) = true; exact hrses)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                          dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, q_se, r_nw, r_ne, r_sw, r_se] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb hrseb
                          conv =>
                            rhs
                            rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                            dsimp only
                            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                            rw [ite_eq_left (by simp only [hrseb, Bool.or_true])]
                          refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                          all_goals try rfl
                          simp [setLocal, hrnw]
                        · have hrseb : (r_se == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrse
                          have hrses : (r_se == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrseb
                          (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_se == 4294967295) = true); rw [hrses]; exact Bool.false_ne_true)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, q_se, r_nw, r_ne, r_sw, r_se] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb hrseb
                          conv =>
                            rhs
                            rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                            dsimp only
                            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b, hrnwb, hrneb, hrswb, hrseb, Bool.false_or]
                          (conv => lhs; arg 2; simp only [u8_sext_toUInt8_id])
                          exact ih _ (a4.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).2
                            (sp - 1) stackLimit (fuel - 1) hnext _
                · have hov4b : (a4.overflow != 0) = true := by simp [hov4]
                  have hov4s : (a4.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
                    rw [u8_sext_beq_zero]; exact beq_false_of_ne hov4
                  (conv => lhs; rw [ite_eq_right (by dsimp only [a4, nodeId, fbase, getArenaU32, Algorithm.stepFrameWidth] at hov4s; simp only [getArenaU32]; rw [hov4s]; exact Bool.false_ne_true)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                  dsimp only [nodeId, fbase, lvl, a4] at hoobb hresb hlvl hov4b
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                    dsimp only
                    simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                  exact ih _ a4 0 stackLimit (fuel - 1) hnext _
            · have hresb : (arena.cellStepRes[nodeId.toNat]! != Algorithm.UNCOMPUTED) = true := bne_iff_ne.mpr hres
              have hress : (arena.cellStepRes[nodeId.toNat]! == 4294967295) = false := by
                simpa [Algorithm.UNCOMPUTED] using beq_false_of_ne hres
              (conv => lhs; rw [ite_eq_right (by dsimp only [nodeId, fbase, getArenaU32, Algorithm.stepFrameWidth] at hress; simp only [getArenaU32]; rw [hress]; exact Bool.false_ne_true)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
              dsimp only [nodeId, fbase] at hoobb hresb
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb]
              exact ih _ arena (sp - 1) stackLimit (fuel - 1) hnext _
        · have hovfb : (arena.overflow != 0) = true := by simp [hovf]
          have hovfs : (arena.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
            rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf
          (conv => lhs; rw [ite_eq_right (by rw [hovfs]; exact Bool.false_ne_true)])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
          rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
          simp [hfz, hspzb, hovfb]

theorem stepCellSerialLoop_equiv (arena : Algorithm.FlatHashLifeArena) (sp stackLimit fuel : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 250 + 3) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 sp), (2, .i32 stackLimit), (3, .i32 fuel)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.stepCellSerialLoop sp stackLimit fuel]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; norm_jvm_locals)
  rw [← Nat.zero_add ((fuel.toNat + 1) * 250)]
  exact stepCellSerialLoop_aux fuel.toNat 0 arena sp stackLimit fuel (Nat.le_refl _) _

elab "flat_step_to" tgtPc:num : tactic => do
  let target := tgtPc.getNat
  for _ in [:400] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs, _) := tgt.eq? | break
    let (inner, isMap) := unwrapRunLhs lhs
    if isMap || !inner.isAppOfArity ``runJvmValFast 5 then break
    let pcExpr ← Lean.Meta.whnf (inner.getArg! 2)
    let some curPc := pcExpr.rawNatLit? | break
    if curPc == target then break
    if ← tryStepFlatInvoke then
      continue
    else if ← isRunJvmAtFlatNonStop then
      let stepN := if curPc < target then min 120 (target - curPc) else 120
      let nStx := Lean.Syntax.mkNumLit (toString stepN)
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepFlatChunk $nStx]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
        let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        let (afterApp, _) := unwrapRunLhs lhs2
        let chunkRes := (afterApp.getArg! 0).consumeMData
        if let some cn := chunkRes.getAppFn.constName? then
          if cn == ``Jvm.BlockChunkRes.cont then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
          else if cn == ``Jvm.BlockChunkRes.jump then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
          else if cn == ``Jvm.BlockChunkRes.done then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
        if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))
    else if ← isRunJvmAtForwardGoto then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (
          (conv => lhs; arg 1; whnf)
          (conv => lhs; arg 3; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 6; jvm_whnf_blk))))
        let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        rwEvalBranchByInstr false (lhs2.getArg! 3)
        if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "flat_step_with" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [:8] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs, _) := tgt.eq? | break
    let lhs := lhs.consumeMData
    if !lhs.isAppOfArity ``afterBlockChunk 2 &&
       !lhs.isAppOfArity ``evalBranchInstrCons 6 &&
       !lhs.isAppOfArity ``runJvmValFast 5 then
      break
    if lhs.isAppOfArity ``afterBlockChunk 2 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 1; try simp only [$hs,*])
        (conv => lhs; arg 1; jvm_whnf_blk)
        (conv => lhs; try rw [afterBlockChunk_cont]; try rw [afterBlockChunk_jump]; try rw [afterBlockChunk_done])
        (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
    else if lhs.isAppOfArity ``evalBranchInstrCons 6 then
      let instr := lhs.getArg! 3
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 6; try simp only [$hs,*])))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; dsimp only [evalBranchInstrCons])))
      rwEvalBranchByInstr false instr
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; try simp only [jvm_runJvmValFast_eq]; norm_jvm_locals; jvm_whnf_run_args)))
    else if lhs.isAppOfArity ``runJvmValFast 5 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 5; try simp only [$hs,*])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
        flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog)))
    else
      break
    let tgt3 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    if tgt3 == tgt then break

elab "flat_step_to_with" tgtPc:num "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [:8] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs, _) := tgt.eq? | break
    let lhs := lhs.consumeMData
    if lhs.isAppOfArity ``runJvmValFast 5 then
      let pcExpr ← Lean.Meta.whnf (lhs.getArg! 2)
      if pcExpr.rawNatLit? == some tgtPc.getNat then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 5; try simp only [$hs,*])))
        break
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 5; try simp only [$hs,*])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
        flat_step_to $tgtPc)))
    let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | break
    let lhs2 := lhs2.consumeMData
    if lhs2.isAppOfArity ``afterBlockChunk 2 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 1; try simp only [$hs,*])
        (conv => lhs; arg 1; jvm_whnf_blk)
        (conv => lhs; try rw [afterBlockChunk_cont]; try rw [afterBlockChunk_jump]; try rw [afterBlockChunk_done])
        (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
    else if lhs2.isAppOfArity ``evalBranchInstrCons 6 then
      let instr := lhs2.getArg! 3
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 6; try simp only [$hs,*])))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; dsimp only [evalBranchInstrCons])))
      rwEvalBranchByInstr false instr
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; try simp only [jvm_runJvmValFast_eq]; norm_jvm_locals; jvm_whnf_run_args)))
    else if lhs2.isAppOfArity ``runJvmValFast 5 then
      let pcExpr ← Lean.Meta.whnf (lhs2.getArg! 2)
      if pcExpr.rawNatLit? == some tgtPc.getNat then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 5; try simp only [$hs,*])))
        break
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 5; try simp only [$hs,*])))
      let tgt2b := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      if tgt2b == tgt then break
    else
      break

private theorem int64_sub_toUInt32 (a b : Int64) :
    (a - b).toUInt64.toUInt32 = a.toUInt64.toUInt32 - b.toUInt64.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_check "../lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.int64_sub_toUInt32.lrat"

private theorem uint64_sub8_toUInt32 (x : Int64) :
    (x.toUInt64 - 8).toUInt32 = x.toUInt64.toUInt32 - (8 : Int64).toUInt64.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_normalize

private theorem int64_sub8_toUInt32 (x : Int64) :
    (x - 8).toUInt64.toUInt32 = x.toUInt64.toUInt32 - (8 : Int64).toUInt64.toUInt32 := by
  rw [Int64.toUInt64_sub]
  exact uint64_sub8_toUInt32 x

private theorem u32_sub1_u64_lshl (x : UInt32) :
    (1 : UInt64) <<< ((x.toUInt64 - 1) % 4294967296 &&& 63) =
      (1 : UInt64) <<< ((x.toUInt64 - 1) % 4294967296) := by
  have h1 : (x.toUInt64 - 1) % 4294967296 = (x - 1).toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    have hx := x.toNat_lt
    simp only [UInt64.toBitVec_mod, BitVec.toNat_umod, UInt64.toBitVec_sub, BitVec.toNat_sub,
      UInt32.toNat_toUInt64, UInt32.toNat_sub, UInt64.toNat_toBitVec]
    have h42 : (4294967296 : UInt64).toNat = 4294967296 := rfl
    have h1a : (1 : UInt64).toNat = 1 := rfl
    have h1b : (1 : UInt32).toNat = 1 := rfl
    rw [h42, h1a, h1b]; omega
  have h2 : (x - 1).toUInt64 &&& 63 = ((x - 1) &&& 63).toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toBitVec_and, BitVec.toNat_and, UInt32.toNat_toUInt64,
      UInt32.toNat_and, UInt64.toNat_toBitVec]
    have h63a : (63 : UInt64).toNat = 63 := rfl
    have h63b : (63 : UInt32).toNat = 63 := rfl
    rw [h63a, h63b]
  rw [h1, h2, lshl_63_mask, ← h1]

private theorem setLocal_noop {locs : Nat → JvmVal} {idx : Nat} {v : JvmVal} (h : locs idx = v) :
    setLocal locs idx v = locs := by
  funext i; simp only [setLocal]; split
  · next heq => subst heq; exact h.symm
  · rfl

private theorem fuel_split1 {C : Nat} (k r : Nat) (hr : C ≤ r) : k + r = (k + (r - C)) + C := by omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
private theorem containsCellLoop_aux :
    ∀ (m k : Nat) (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) (fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        runJvmValFast (k + (m + 1) * 330) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 3
          (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 3)
          ⟨3, [],
            setLocal (setLocal (setLocal (setLocal (setLocal base 0 ((.ext (.arenaRef 0)))) 1 (.i32 nodeId))
              2 (.i64 rx.toUInt64)) 4 (.i64 ry.toUInt64)) 6 (.i32 fuel), {}, ⟨[arena], [], []⟩⟩ =
          some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
  intro m
  induction m with
  | zero =>
    intro k arena nodeId rx ry fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 330 = k + 330 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by exact hfzb)])
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp only [hfz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte])
  | succ m ih =>
    intro k arena nodeId rx ry fuel hn base
    rw [show k + (m + 1 + 1) * 330 = (k + (m + 1) * 330) + 330 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by exact hfzb)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp only [hfz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte])
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by rw [hfzb]; exact Bool.false_ne_true)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      by_cases hoob : arena.cellCount ≤ nodeId
      · have hoobb : nodeId ≥ arena.cellCount := hoob
        (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hoob)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
        (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb])
      · have hoobb : ¬ (nodeId ≥ arena.cellCount) := hoob
        (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false hoob]; exact Bool.false_ne_true)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
        by_cases hrx0 : rx < 0
        · have hrx0s : ((if rx.toUInt64 == 0 then (0 : UInt32)
              else if rx.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = true :=
            (lcmp_slt_zero_int64 rx 0).mpr hrx0
          (conv => lhs; rw [ite_eq_left (by exact hrx0s)])
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
          (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb, hrx0])
        · have hrx0s : ((if rx.toUInt64 == 0 then (0 : UInt32)
              else if rx.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = false :=
            Bool.eq_false_iff.mpr (mt (lcmp_slt_zero_int64 rx 0).mp hrx0)
          (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrx0s.symm.trans h))])
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
          by_cases hry0 : ry < 0
          · have hry0s : ((if ry.toUInt64 == 0 then (0 : UInt32)
                else if ry.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = true :=
              (lcmp_slt_zero_int64 ry 0).mpr hry0
            (conv => lhs; rw [ite_eq_left (by exact hry0s)])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
            (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb, hrx0, hry0])
          · have hry0s : ((if ry.toUInt64 == 0 then (0 : UInt32)
                else if ry.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = false :=
              Bool.eq_false_iff.mpr (mt (lcmp_slt_zero_int64 ry 0).mp hry0)
            (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hry0s.symm.trans h))])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
            let lvl := arena.cellLevel[nodeId.toNat]!.toUInt32
            let half := Algorithm.pow2Int64 (lvl - 1)
            let east := decide (lvl ≤ 63) && decide (rx ≥ half)
            let south := decide (lvl ≤ 63) && decide (ry ≥ half)
            let rx' := if east = true then rx - half else rx
            let ry' := if south = true then ry - half else ry
            let childId :=
              if south = true then
                if east = true then arena.cellSe[nodeId.toNat]! else arena.cellSw[nodeId.toNat]!
              else if east = true then arena.cellNe[nodeId.toNat]! else arena.cellNw[nodeId.toNat]!
            have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
            have hjoin365 : ∀ km (l26 : UInt32) (l24 l27 : UInt64) (locs : Nat → JvmVal),
                locs 7 = (.ext (.arenaU64Ref 0 .l4Se)) → locs 8 = (.ext (.arenaU64Ref 0 .l4Sw)) →
                locs 9 = (.ext (.arenaU64Ref 0 .l4Ne)) → locs 10 = (.ext (.arenaU64Ref 0 .l4Nw)) →
                locs 21 = .i64 8 → locs 23 = .i32 childId →
                locs 24 = .i64 l24 → locs 26 = .i32 l26 → locs 27 = .i64 l27 →
                l24 = ry'.toUInt64 →
                l26 = (if rx' ≥ 8 then 1 else 0) →
                l27 = (if rx' ≥ 8 then rx' - 8 else rx').toUInt64 →
                runJvmValFast (km + 45) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 365
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 365)
                  ⟨365, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                  some (.i32 (if Algorithm.leafContains
                    (if ry' ≥ 8 then
                       if rx' ≥ 8 then arena.l4Se[childId.toNat]! else arena.l4Sw[childId.toNat]!
                     else if rx' ≥ 8 then arena.l4Ne[childId.toNat]! else arena.l4Nw[childId.toNat]!)
                    (if rx' ≥ 8 then rx' - 8 else rx').toUInt64.toUInt32
                    (if ry' ≥ 8 then ry' - 8 else ry').toUInt64.toUInt32 then 1 else 0)) := by
              intro km l26 l24 l27 locs h7 h8 h9 h10 h21 h23 h24 h26 h27 hl24 hl26 hl27
              have h24' := h24.trans (congrArg JvmVal.i64 hl24)
              have h26' := h26.trans (congrArg JvmVal.i32 hl26)
              have h27' := h27.trans (congrArg JvmVal.i64 hl27)
              (conv => lhs; arg 5; rw [← setLocal_noop h7, ← setLocal_noop h8, ← setLocal_noop h9, ← setLocal_noop h10, ← setLocal_noop h21, ← setLocal_noop h23, ← setLocal_noop h24', ← setLocal_noop h26', ← setLocal_noop h27'])
              flat_step_with [h7, h8, h9, h10, h21, h23, h24, h26, h27, hl24, hl26, hl27]
              by_cases hqy8 : ry' ≥ 8
              · have hqy8s : ((if (8 : Int64).toUInt64 == ry'.toUInt64 then (0 : UInt32)
                    else if (8 : Int64).toUInt64.toBitVec.slt ry'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (lcmp_sle_zero_int64 8 ry').mpr hqy8
                (conv => lhs; rw [ite_eq_left (by exact hqy8s)])
                flat_step_with [h21, h24, h26, hl24, hl26]
                by_cases hqx8 : rx' ≥ 8
                · have hqx8l : (!(if rx' ≥ 8 then (1 : UInt32) else 0) == 0) = true := by simp [hqx8]
                  (conv => lhs; rw [ite_eq_left hqx8l])
                  flat_step_with [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32]
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32, int64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte, int64_sub8_toUInt32])
                  try rfl
                · have hqx8l : ¬((!(if rx' ≥ 8 then (1 : UInt32) else 0) == 0) = true) := by simp [hqx8]
                  (conv => lhs; rw [ite_eq_right hqx8l])
                  flat_step_with [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32]
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte, int64_sub8_toUInt32])
                  try rfl
              · have hqy8s : ((if (8 : Int64).toUInt64 == ry'.toUInt64 then (0 : UInt32)
                    else if (8 : Int64).toUInt64.toBitVec.slt ry'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 8 ry').mp hqy8)
                (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hqy8s.symm.trans h))])
                flat_step_with [h21, h24, h26, hl24, hl26]
                by_cases hqx8 : rx' ≥ 8
                · have hqx8l : (!(if rx' ≥ 8 then (1 : UInt32) else 0) == 0) = true := by simp [hqx8]
                  (conv => lhs; rw [ite_eq_left hqx8l])
                  flat_step_with [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32]
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte])
                  rfl
                · have hqx8l : ¬((!(if rx' ≥ 8 then (1 : UInt32) else 0) == 0) = true) := by simp [hqx8]
                  (conv => lhs; rw [ite_eq_right hqx8l])
                  flat_step_with [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32]
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte])
                  rfl
            have hjoin293 : ∀ km (locs : Nat → JvmVal),
                locs 0 = (.ext (.arenaRef 0)) → locs 6 = .i32 fuel →
                locs 7 = (.ext (.arenaU64Ref 0 .l4Se)) → locs 8 = (.ext (.arenaU64Ref 0 .l4Sw)) →
                locs 9 = (.ext (.arenaU64Ref 0 .l4Ne)) → locs 10 = (.ext (.arenaU64Ref 0 .l4Nw)) →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 33 = .i32 0 → locs 34 = .i32 1 →
                locs 35 = .i64 rx'.toUInt64 → locs 37 = .i64 ry'.toUInt64 →
                locs 39 = .i32 childId →
                runJvmValFast (km + (m + 1) * 330 + 80) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 293
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 293)
                  ⟨293, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km locs h0 h6 h7 h8 h9 h10 h31 h32 h33 h34 h35 h37 h39
              (conv => lhs; arg 5; rw [← setLocal_noop h0, ← setLocal_noop h6, ← setLocal_noop h7, ← setLocal_noop h8, ← setLocal_noop h9, ← setLocal_noop h10, ← setLocal_noop h31, ← setLocal_noop h32, ← setLocal_noop h33, ← setLocal_noop h34, ← setLocal_noop h35, ← setLocal_noop h37, ← setLocal_noop h39])
              flat_step_with [h0, h6, h7, h8, h9, h10, h31, h32, h33, h34, h35, h37, h39]
              by_cases h5 : lvl ≤ 5
              · (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true h5)])
                flat_step_with [h39]
                (conv => rhs; rw [Algorithm.containsLevel4.eq_1])
                by_cases hcz : childId = 0
                · have hczb : (childId == 0) = true := beq_iff_eq.mpr hcz
                  (conv => lhs; rw [ite_eq_left (by exact hczb)])
                  (conv => rhs; simp only [h5, hczb, Bool.true_or, ↓reduceIte])
                  flat_step_with [h33]
                  try simp only [h33]
                  rfl
                · have hczb : (childId == 0) = false := beq_false_of_ne hcz
                  (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hczb.symm.trans h))])
                  (conv => rhs; simp only [h5, hczb, Bool.false_or, ↓reduceIte])
                  flat_step_with [h32, h39]
                  by_cases hcoob : arena.l4Count ≤ childId
                  · have hcoobs : decide (childId ≥ arena.l4Count) = true := decide_eq_true hcoob
                    (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hcoob)])
                    (conv => rhs; simp only [hcoobs, ↓reduceIte])
                    flat_step_with [h33]
                    try simp only [h33]
                    rfl
                  · have hcoobs : decide (childId ≥ arena.l4Count) = false := decide_eq_false hcoob
                    (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false hcoob]; exact Bool.false_ne_true)])
                    (conv => rhs; simp only [hcoobs, ↓reduceIte])
                    flat_step_with [h35]
                    by_cases hqx8 : rx' ≥ 8
                    · have hqx8s : ((if (8 : Int64).toUInt64 == rx'.toUInt64 then (0 : UInt32)
                          else if (8 : Int64).toUInt64.toBitVec.slt rx'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                        (lcmp_sle_zero_int64 8 rx').mpr hqx8
                      (conv => lhs; rw [ite_eq_left (by exact hqx8s)])
                      (conv => rhs; simp only [Bool.false_eq_true, ↓reduceIte])
                      flat_step_to_with 365 [h7, h8, h9, h10, h35, h37, h39]
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 45)]; rotate_left; omega
                      refine hjoin365 _ (1 : UInt32) ry'.toUInt64 (rx'.toUInt64 - 8) _
                        (by simp [setLocal]) (by simp [setLocal])
                        (by simp [setLocal]) (by simp [setLocal])
                        rfl rfl rfl rfl rfl rfl ?_ ?_
                      · simp [hqx8]
                      · simp [hqx8]; rfl
                    · have hqx8s : ((if (8 : Int64).toUInt64 == rx'.toUInt64 then (0 : UInt32)
                          else if (8 : Int64).toUInt64.toBitVec.slt rx'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                        Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 8 rx').mp hqx8)
                      (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hqx8s.symm.trans h))])
                      (conv => rhs; simp only [Bool.false_eq_true, ↓reduceIte])
                      flat_step_to_with 365 [h7, h8, h9, h10, h35, h37, h39]
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 45)]; rotate_left; omega
                      refine hjoin365 _ (0 : UInt32) ry'.toUInt64 rx'.toUInt64 _
                        (by simp [setLocal]) (by simp [setLocal])
                        (by simp [setLocal]) (by simp [setLocal])
                        rfl rfl rfl rfl rfl rfl ?_ ?_
                      · simp [hqx8]
                      · simp [hqx8]
              · (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false h5]; exact Bool.false_ne_true)])
                (conv => rhs; simp only [h5, ↓reduceIte])
                flat_step_to_with 3 [h0, h6, h7, h8, h9, h10, h31, h32, h33, h34, h35, h37, h39]
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq])
                jvm_step_branch_tail
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm km ((m + 1) * 330), Nat.add_comm ((m + 1) * 330)]
                exact ih _ arena childId rx' ry' (fuel - 1) hnext _
            have hjoin224 : ∀ km (l46 l49 : UInt32) (l50 : UInt64) (locs : Nat → JvmVal),
                locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 nodeId →
                locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = (.ext (.arenaU64Ref 0 .l4Se)) → locs 8 = (.ext (.arenaU64Ref 0 .l4Sw)) →
                locs 9 = (.ext (.arenaU64Ref 0 .l4Ne)) → locs 10 = (.ext (.arenaU64Ref 0 .l4Nw)) →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = (.ext (.arenaU32Ref 0 .cellSe)) → locs 41 = (.ext (.arenaU32Ref 0 .cellSw)) →
                locs 42 = (.ext (.arenaU32Ref 0 .cellNe)) → locs 43 = (.ext (.arenaU32Ref 0 .cellNw)) →
                locs 44 = .i32 0 → locs 45 = .i32 1 →
                locs 46 = .i32 l46 → locs 47 = .i64 half.toUInt64 →
                locs 49 = .i32 l49 → locs 50 = .i64 l50 →
                l46 = (if south then 1 else 0) →
                l49 = (if east then 1 else 0) →
                l50 = rx'.toUInt64 →
                runJvmValFast (km + (m + 1) * 330 + 115) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 224
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 224)
                  ⟨224, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km l46 l49 l50 locs h0 h1 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h44 h45 h46 h47 h49 h50
                hl46 hl49 hl50
              have h46' := h46.trans (congrArg JvmVal.i32 hl46)
              have h49' := h49.trans (congrArg JvmVal.i32 hl49)
              have h50' := h50.trans (congrArg JvmVal.i64 hl50)
              (conv => lhs; arg 5; rw [← setLocal_noop h0, ← setLocal_noop h1, ← setLocal_noop h4, ← setLocal_noop h6, ← setLocal_noop h7, ← setLocal_noop h8, ← setLocal_noop h9, ← setLocal_noop h10, ← setLocal_noop h31, ← setLocal_noop h32, ← setLocal_noop h40, ← setLocal_noop h41, ← setLocal_noop h42, ← setLocal_noop h43, ← setLocal_noop h44, ← setLocal_noop h45, ← setLocal_noop h46', ← setLocal_noop h47, ← setLocal_noop h49', ← setLocal_noop h50'])
              flat_step_with [h0, h1, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                h44, h45, h46, h47, h49, h50, hl46, hl49, hl50]
              by_cases hs : south = true
              · (conv => lhs; rw [ite_eq_left (by simp only [hs]; decide)])
                flat_step_with [h49, hl49]
                by_cases he : east = true
                · (conv => lhs; rw [ite_eq_left (by simp only [he]; decide)])
                  flat_step_to_with 293 [h40, h41, h42, h43, h4, h47, h1]
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) ?_ ?_
                  · simp [setLocal, ry', hs]
                  · simp [setLocal, getArenaU32, childId, hs, he]
                · (conv => lhs; rw [ite_eq_right (by simp only [he]; decide)])
                  flat_step_to_with 293 [h40, h41, h42, h43, h4, h47, h1]
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) ?_ ?_
                  · simp [setLocal, ry', hs]
                  · simp [setLocal, getArenaU32, childId, hs, he]
              · (conv => lhs; rw [ite_eq_right (by simp only [hs]; decide)])
                flat_step_with [h49, hl49]
                by_cases he : east = true
                · (conv => lhs; rw [ite_eq_left (by simp only [he]; decide)])
                  flat_step_to_with 293 [h40, h41, h42, h43, h4, h1]
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) ?_ ?_
                  · simp [setLocal, ry', hs]
                  · simp [setLocal, getArenaU32, childId, hs, he]
                · (conv => lhs; rw [ite_eq_right (by simp only [he]; decide)])
                  flat_step_to_with 293 [h40, h41, h42, h43, h4, h1]
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) ?_ ?_
                  · simp [setLocal, ry', hs]
                  · simp [setLocal, getArenaU32, childId, hs, he]
            have hjoin193 : ∀ km (l56 l57 : UInt32) (locs : Nat → JvmVal),
                locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 nodeId →
                locs 2 = .i64 rx.toUInt64 → locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = (.ext (.arenaU64Ref 0 .l4Se)) → locs 8 = (.ext (.arenaU64Ref 0 .l4Sw)) →
                locs 9 = (.ext (.arenaU64Ref 0 .l4Ne)) → locs 10 = (.ext (.arenaU64Ref 0 .l4Nw)) →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = (.ext (.arenaU32Ref 0 .cellSe)) → locs 41 = (.ext (.arenaU32Ref 0 .cellSw)) →
                locs 42 = (.ext (.arenaU32Ref 0 .cellNe)) → locs 43 = (.ext (.arenaU32Ref 0 .cellNw)) →
                locs 52 = .i32 1 → locs 53 = .i32 0 → locs 54 = .i64 half.toUInt64 →
                locs 56 = .i32 l56 → locs 57 = .i32 l57 →
                l56 = (if east then 1 else 0) →
                l57 = (if south then 1 else 0) →
                runJvmValFast (km + (m + 1) * 330 + 135) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 193
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 193)
                  ⟨193, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km l56 l57 locs h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43
                h52 h53 h54 h56 h57 hl56 hl57
              have h56' := h56.trans (congrArg JvmVal.i32 hl56)
              have h57' := h57.trans (congrArg JvmVal.i32 hl57)
              (conv => lhs; arg 5; rw [← setLocal_noop h0, ← setLocal_noop h1, ← setLocal_noop h2, ← setLocal_noop h4, ← setLocal_noop h6, ← setLocal_noop h7, ← setLocal_noop h8, ← setLocal_noop h9, ← setLocal_noop h10, ← setLocal_noop h31, ← setLocal_noop h32, ← setLocal_noop h40, ← setLocal_noop h41, ← setLocal_noop h42, ← setLocal_noop h43, ← setLocal_noop h52, ← setLocal_noop h53, ← setLocal_noop h54, ← setLocal_noop h56', ← setLocal_noop h57'])
              flat_step_with [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                h52, h53, h54, h56, h57, hl56, hl57]
              by_cases he : east = true
              · (conv => lhs; rw [ite_eq_left (by simp only [he]; decide)])
                flat_step_to_with 224 [h2, h54, h40, h41, h42, h43]
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 115)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin224 _ l57 (1 : UInt32) (rx.toUInt64 - half.toUInt64) _
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal, hl57]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  hl57 (by simp [he]) (by simp [rx', he])
              · (conv => lhs; rw [ite_eq_right (by simp only [he]; decide)])
                flat_step_to_with 224 [h2, h54, h40, h41, h42, h43]
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 115)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin224 _ l57 (0 : UInt32) rx.toUInt64 _
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal, hl57]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  hl57 (by simp [he]) (by simp [rx', he])
            have hjoin143 : ∀ km (locs : Nat → JvmVal),
                locs 0 = (.ext (.arenaRef 0)) → locs 1 = .i32 nodeId →
                locs 2 = .i64 rx.toUInt64 → locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = (.ext (.arenaU64Ref 0 .l4Se)) → locs 8 = (.ext (.arenaU64Ref 0 .l4Sw)) →
                locs 9 = (.ext (.arenaU64Ref 0 .l4Ne)) → locs 10 = (.ext (.arenaU64Ref 0 .l4Nw)) →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = (.ext (.arenaU32Ref 0 .cellSe)) → locs 41 = (.ext (.arenaU32Ref 0 .cellSw)) →
                locs 42 = (.ext (.arenaU32Ref 0 .cellNe)) → locs 43 = (.ext (.arenaU32Ref 0 .cellNw)) →
                locs 58 = .i32 0 →
                (lvl < 63 → ¬ (rx ≥ Algorithm.pow2Int64 lvl) ∧ ¬ (ry ≥ Algorithm.pow2Int64 lvl)) →
                runJvmValFast (km + (m + 1) * 330 + 180) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 143
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 143)
                  ⟨143, [], locs, {}, ⟨[arena], [], []⟩⟩ =
                  some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
              intro km locs h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h58 hbounds
              (conv => lhs; arg 5; rw [← setLocal_noop h0, ← setLocal_noop h1, ← setLocal_noop h2, ← setLocal_noop h4, ← setLocal_noop h6, ← setLocal_noop h7, ← setLocal_noop h8, ← setLocal_noop h9, ← setLocal_noop h10, ← setLocal_noop h31, ← setLocal_noop h32, ← setLocal_noop h40, ← setLocal_noop h41, ← setLocal_noop h42, ← setLocal_noop h43, ← setLocal_noop h58])
              have hbnd' : (decide (lvl < 63) && (decide (rx ≥ Algorithm.pow2Int64 lvl) || decide (ry ≥ Algorithm.pow2Int64 lvl))) = false := by
                by_cases h63lt : lvl < 63
                · have ⟨hx, hy⟩ := hbounds h63lt
                  simp [lvl, hx, hy]
                · simp [lvl, h63lt]
              dsimp only [lvl] at hbnd'
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hoobb, hrx0, hry0, decide_false, Bool.false_or, hbnd', Bool.false_eq_true, ↓reduceIte]
              change _ = some (JvmVal.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0))
              flat_step_with [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
              by_cases h63le : lvl ≤ 63
              · (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true h63le)])
                flat_step_with [h2, h4, h58]
                have hhalf : ((1 : UInt64) <<< ((lvl - 1) &&& 63).toUInt64) = half.toUInt64 := by
                  simp only [half, Algorithm.pow2Int64.eq_1, lshl_63_mask]; rfl
                rw [hhalf]
                by_cases hrx : rx ≥ half
                · have hrxs : ((0#32).slt (if half.toUInt64 == rx.toUInt64 then (0 : UInt32)
                      else if half.toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                    Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half rx).mp (Classical.not_not.mpr hrx))
                  (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrxs.symm.trans h))])
                  flat_step_with [h4, h58]
                  by_cases hry : ry ≥ half
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                      Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half ry).mp (Classical.not_not.mpr hry))
                    (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrys.symm.trans h))])
                    flat_step_to_with 193 [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (1 : UInt32) (1 : UInt32) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 20 (simp [setLocal])
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                      (lcmp_sgt_zero_int64 half ry).mpr hry
                    (conv => lhs; rw [ite_eq_left (by exact hrys)])
                    flat_step_to_with 193 [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (1 : UInt32) (0 : UInt32) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 20 (simp [setLocal])
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                · have hrxs : ((0#32).slt (if half.toUInt64 == rx.toUInt64 then (0 : UInt32)
                      else if half.toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                    (lcmp_sgt_zero_int64 half rx).mpr hrx
                  (conv => lhs; rw [ite_eq_left (by exact hrxs)])
                  flat_step_with [h4, h58]
                  by_cases hry : ry ≥ half
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                      Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half ry).mp (Classical.not_not.mpr hry))
                    (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrys.symm.trans h))])
                    flat_step_to_with 193 [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (0 : UInt32) (1 : UInt32) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 20 (simp [setLocal])
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                      (lcmp_sgt_zero_int64 half ry).mpr hry
                    (conv => lhs; rw [ite_eq_left (by exact hrys)])
                    flat_step_to_with 193 [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (0 : UInt32) (0 : UInt32) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 20 (simp [setLocal])
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
              · (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false h63le]; exact Bool.false_ne_true)])
                flat_step_to_with 193 [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58]
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin193 _ (0 : UInt32) (0 : UInt32) _
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
                  (by simp [setLocal])
                  (by simp [setLocal, half, Algorithm.pow2Int64.eq_1]; exact u32_sub1_u64_lshl lvl)
                  (by simp [setLocal]) (by simp [setLocal])
                  (by simp [east, h63le]) (by simp [south, h63le])
            by_cases h63lt : lvl < 63
            · (conv => lhs; rw [ite_eq_left (by simp only [getArenaU8, u8_sext_band255]; rw [compareUnsigned_slt']; exact decide_eq_true h63lt)])
              (conv => lhs; arg 5; simp only [getArenaU8, u8_sext_band255])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              have hsize : ((1 : UInt64) <<< (lvl &&& 63).toUInt64) = (Algorithm.pow2Int64 lvl).toUInt64 := by
                simp only [Algorithm.pow2Int64.eq_1, lshl_63_mask]; rfl
              rw [hsize]
              by_cases hrxs : rx ≥ Algorithm.pow2Int64 lvl
              · have hrxss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == rx.toUInt64 then (0 : UInt32)
                    else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (lcmp_sle_zero_int64 _ rx).mpr hrxs
                (conv => lhs; rw [ite_eq_left (by exact hrxss)])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                  dsimp only
                  simp [hfz, hoobb, hrx0, lvl, h63lt, hrxs]
              · have hrxss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == rx.toUInt64 then (0 : UInt32)
                    else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 _ rx).mp hrxs)
                (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrxss.symm.trans h))])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases hrys : ry ≥ Algorithm.pow2Int64 lvl
                · have hryss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == ry.toUInt64 then (0 : UInt32)
                      else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                    (lcmp_sle_zero_int64 _ ry).mpr hrys
                  (conv => lhs; rw [ite_eq_left (by exact hryss)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                    dsimp only
                    simp [hfz, hoobb, hrx0, hry0, lvl, h63lt, hrys]
                · have hryss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == ry.toUInt64 then (0 : UInt32)
                      else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                    Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 _ ry).mp hrys)
                  (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hryss.symm.trans h))])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 143
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc k ((m + 1) * 330), fuel_split1 (C := 180)]; rotate_left; omega
                  rw [Nat.add_right_comm k ((m + 1) * 330)]
                  refine hjoin143 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => ⟨hrxs, hrys⟩)
                  all_goals try rfl
            · (conv => lhs; rw [ite_eq_right (by simp only [getArenaU8, u8_sext_band255]; rw [compareUnsigned_slt', decide_eq_false h63lt]; exact Bool.false_ne_true)])
              (conv => lhs; arg 5; simp only [getArenaU8, u8_sext_band255])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_to 143
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [← Nat.add_assoc k ((m + 1) * 330), fuel_split1 (C := 180)]; rotate_left; omega
              rw [Nat.add_right_comm k ((m + 1) * 330)]
              refine hjoin143 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => absurd h h63lt)
              all_goals try rfl

theorem containsCellLoop_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) (fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 330 + 3) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId), (2, .i64 rx.toUInt64), (4, .i64 ry.toUInt64),
        (6, .i32 fuel)] [arena]) =
      some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 330)]
  exact containsCellLoop_aux fuel.toNat 0 arena nodeId rx ry fuel (Nat.le_refl _) _


end Algorithm.JvmVerification
