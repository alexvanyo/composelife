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

import JvmBytecode
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.Family1

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

local macro "step_val_n " n:num : tactic => `(tactic| (
  f1_split_val_fuel 10
  rw [runJvmValFast_stepFlatChunk $n]
  (conv => lhs; arg 1; jvm_whnf_blk)
  first | rw [afterBlockChunk_cont] | rw [afterBlockChunk_jump]
  (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))

private theorem setLocal_eq_self {locs : Nat → JvmVal} {idx : Nat} {val : JvmVal}
    (h : locs idx = val) : setLocal locs idx val = locs := by
  funext i
  dsimp [setLocal]
  split <;> simp_all

private theorem bitwise_pc309 {k : Nat} (hk : 600 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h9 : locs 9 = .i32 (w >>> 9 &&& 1))
    (h10 : locs 10 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1)))
    (h11 : locs 11 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h12 : locs 12 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount21UInt w) (w >>> 6 &&& 1))) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 309
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 309)
      ⟨309, [], locs, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  rw [← setLocal_eq_self h0, ← setLocal_eq_self h6, ← setLocal_eq_self h7, ← setLocal_eq_self h9,
    ← setLocal_eq_self h10, ← setLocal_eq_self h11, ← setLocal_eq_self h12]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc3 => ?_) (fun hc3 => ?_)
  · have hnc : Algorithm.neighborCount11UInt w = 3 := by
      simpa [Algorithm.neighborCount11UInt] using hc3
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
    simp [Algorithm.computeNextGen4x4BitwiseUInt, Algorithm.bitRuleUInt, hnc]
  · have hnc3 : Algorithm.neighborCount11UInt w ≠ 3 := by
      simpa [Algorithm.neighborCount11UInt] using hc3
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
    refine eq_of_ite_branches (fun hc2 => ?_) (fun hc2 => ?_)
    · have hnc2 : Algorithm.neighborCount11UInt w = 2 := by
        simpa [Algorithm.neighborCount11UInt] using hc2
      f1_split_val_fuel 120
      flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
      refine eq_of_ite_branches (fun hbit => ?_) (fun hbit => ?_)
      · have hb : (w >>> 3 &&& 1) = 1 := by simpa using hbit
        f1_split_val_fuel 120
        flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
        simp [Algorithm.computeNextGen4x4BitwiseUInt, Algorithm.bitRuleUInt, hnc2, hb]
      · have hb : (w >>> 3 &&& 1) ≠ 1 := by simpa using hbit
        f1_split_val_fuel 120
        flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
        simp [Algorithm.computeNextGen4x4BitwiseUInt, Algorithm.bitRuleUInt, hnc2, hb]
    · have hnc2 : Algorithm.neighborCount11UInt w ≠ 2 := by
        simpa [Algorithm.neighborCount11UInt] using hc2
      f1_split_val_fuel 120
      flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
      simp [Algorithm.computeNextGen4x4BitwiseUInt, Algorithm.bitRuleUInt, hnc3, hnc2]

private theorem bitwise_pc296 {k : Nat} (hk : 610 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h9 : locs 9 = .i32 (w >>> 9 &&& 1))
    (h15 : locs 15 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h16 : locs 16 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1)))
    (hb : (w >>> 6 &&& 1) = 1) (hnc2 : Algorithm.neighborCount21UInt w = 2) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 296
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 296)
      ⟨296, [], setLocal locs 21 (.i32 (Algorithm.neighborCount21UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 7
  apply bitwise_pc309 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h9]) (by simp [setLocal, h16])
    (by simp [setLocal, h15]) (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc289 {k : Nat} (hk : 610 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h9 : locs 9 = .i32 (w >>> 9 &&& 1))
    (h15 : locs 15 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h16 : locs 16 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1)))
    (hb : (w >>> 6 &&& 1) ≠ 1) (hnc2 : Algorithm.neighborCount21UInt w = 2) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 289
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 289)
      ⟨289, [], setLocal locs 21 (.i32 (Algorithm.neighborCount21UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 7
  apply bitwise_pc309 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h9]) (by simp [setLocal, h16])
    (by simp [setLocal, h15]) (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc279 {k : Nat} (hk : 610 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h9 : locs 9 = .i32 (w >>> 9 &&& 1))
    (h15 : locs 15 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h16 : locs 16 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1)))
    (hnc3 : Algorithm.neighborCount21UInt w ≠ 3) (hnc2 : Algorithm.neighborCount21UInt w ≠ 2) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 279
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 279)
      ⟨279, [], setLocal locs 21 (.i32 (Algorithm.neighborCount21UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 7
  apply bitwise_pc309 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h9]) (by simp [setLocal, h16])
    (by simp [setLocal, h15]) (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc3, hnc2])

private theorem bitwise_pc220_nc2 {k : Nat} (hk : 900 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h9 : locs 9 = .i32 (w >>> 9 &&& 1))
    (h15 : locs 15 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h16 : locs 16 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1)))
    (hnc3 : Algorithm.neighborCount21UInt w ≠ 3) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 276
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 276)
      ⟨276, [], setLocal locs 21 (.i32 (Algorithm.neighborCount21UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  rw [← setLocal_eq_self h7]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc2 => ?_) (fun hc2 => ?_)
  · have hnc2 : Algorithm.neighborCount21UInt w = 2 := by
      simpa [Algorithm.neighborCount21UInt] using hc2
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
    refine eq_of_ite_branches (fun hbit => ?_) (fun hbit => ?_)
    · have hb : (w >>> 6 &&& 1) = 1 := by simpa using hbit
      exact bitwise_pc296 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
        w _ (by simp [setLocal, h0]) (by simp [setLocal, h6]) (by simp [setLocal])
        (by simp [setLocal, h9]) (by simp [setLocal, h15]) (by simp [setLocal, h16]) hb hnc2
    · have hb : (w >>> 6 &&& 1) ≠ 1 := by simpa using hbit
      exact bitwise_pc289 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
        w _ (by simp [setLocal, h0]) (by simp [setLocal, h6]) (by simp [setLocal])
        (by simp [setLocal, h9]) (by simp [setLocal, h15]) (by simp [setLocal, h16]) hb hnc2
  · have hnc2 : Algorithm.neighborCount21UInt w ≠ 2 := by
      simpa [Algorithm.neighborCount21UInt] using hc2
    exact bitwise_pc279 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
      w _ (by simp [setLocal, h0]) (by simp [setLocal, h6]) (by simp [setLocal])
      (by simp [setLocal, h9]) (by simp [setLocal, h15]) (by simp [setLocal, h16]) hnc3 hnc2

private theorem bitwise_pc220 {k : Nat} (hk : 1200 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h14 : locs 14 = .i32 (w >>> 13 &&& 1))
    (h15 : locs 15 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (h16 : locs 16 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount12UInt w) (w >>> 9 &&& 1))) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 220
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 220)
      ⟨220, [], locs, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  rw [← setLocal_eq_self h0, ← setLocal_eq_self h6, ← setLocal_eq_self h8, ← setLocal_eq_self h9,
    ← setLocal_eq_self h14]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc3 => ?_) (fun hc3 => ?_)
  · have hnc : Algorithm.neighborCount21UInt w = 3 := by
      simpa [Algorithm.neighborCount21UInt] using hc3
    step_val_n 6
    apply bitwise_pc309 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
      (by simp [setLocal]) (by simp [setLocal])
      (by simp [setLocal, h7]) (by simp [setLocal]) (by simp [setLocal, h16])
      (by simp [setLocal, h15]) (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc])
  · have hnc3 : Algorithm.neighborCount21UInt w ≠ 3 := by
      simpa [Algorithm.neighborCount21UInt] using hc3
    exact bitwise_pc220_nc2 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
      w _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal, h7])
      (by simp [setLocal]) (by simp [setLocal, h15]) (by simp [setLocal, h16]) hnc3

private theorem bitwise_pc216 {k : Nat} (hk : 1210 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h14 : locs 14 = .i32 (w >>> 13 &&& 1))
    (h18 : locs 18 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (hnc : Algorithm.neighborCount12UInt w = 3) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 216
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 216)
      ⟨216, [], setLocal locs 20 (.i32 (Algorithm.neighborCount12UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 4
  apply bitwise_pc220 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h8]) (by simp [setLocal, h9])
    (by simp [setLocal, h14]) (by simp [setLocal, h18])
    (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc])

private theorem bitwise_pc211 {k : Nat} (hk : 1210 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h14 : locs 14 = .i32 (w >>> 13 &&& 1))
    (h18 : locs 18 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (hnc2 : Algorithm.neighborCount12UInt w = 2) (hb : (w >>> 9 &&& 1) = 1) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 211
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 211)
      ⟨211, [], setLocal locs 20 (.i32 (Algorithm.neighborCount12UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 5
  apply bitwise_pc220 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h8]) (by simp [setLocal, h9])
    (by simp [setLocal, h14]) (by simp [setLocal, h18])
    (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc206 {k : Nat} (hk : 1210 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h14 : locs 14 = .i32 (w >>> 13 &&& 1))
    (h18 : locs 18 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (hnc2 : Algorithm.neighborCount12UInt w = 2) (hb : (w >>> 9 &&& 1) ≠ 1) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 206
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 206)
      ⟨206, [], setLocal locs 20 (.i32 (Algorithm.neighborCount12UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 5
  apply bitwise_pc220 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h8]) (by simp [setLocal, h9])
    (by simp [setLocal, h14]) (by simp [setLocal, h18])
    (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc198 {k : Nat} (hk : 1210 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h14 : locs 14 = .i32 (w >>> 13 &&& 1))
    (h18 : locs 18 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1)))
    (hnc3 : Algorithm.neighborCount12UInt w ≠ 3) (hnc2 : Algorithm.neighborCount12UInt w ≠ 2) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 198
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 198)
      ⟨198, [], setLocal locs 20 (.i32 (Algorithm.neighborCount12UInt w)), {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 5
  apply bitwise_pc220 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    (by simp [setLocal, h0]) (by simp [setLocal, h6])
    (by simp [setLocal, h7]) (by simp [setLocal, h8]) (by simp [setLocal, h9])
    (by simp [setLocal, h14]) (by simp [setLocal, h18])
    (by dsimp [setLocal]; simp [Algorithm.bitRuleUInt, hnc3, hnc2])

private theorem bitwise_pc139 {k : Nat} (hk : 1800 ≤ k) (w : UInt32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i32 w) (h6 : locs 6 = .i32 (w >>> 3 &&& 1))
    (h7 : locs 7 = .i32 (w >>> 6 &&& 1)) (h8 : locs 8 = .i32 (w >>> 7 &&& 1))
    (h9 : locs 9 = .i32 (w >>> 9 &&& 1)) (h13 : locs 13 = .i32 (w >>> 11 &&& 1))
    (h14 : locs 14 = .i32 (w >>> 13 &&& 1)) (h17 : locs 17 = .i32 (w >>> 14 &&& 1))
    (h18 : locs 18 = .i32 (Algorithm.bitRuleUInt (Algorithm.neighborCount22UInt w) (w >>> 12 &&& 1))) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 139
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 139)
      ⟨139, [], locs, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  rw [← setLocal_eq_self h0, ← setLocal_eq_self h6, ← setLocal_eq_self h7, ← setLocal_eq_self h9,
    ← setLocal_eq_self h13, ← setLocal_eq_self h17]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc3 => ?_) (fun hc3 => ?_)
  · have hnc : Algorithm.neighborCount12UInt w = 3 := by
      simpa [Algorithm.neighborCount12UInt] using hc3
    exact bitwise_pc216 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
      w _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
      (by simp [setLocal, h8]) (by simp [setLocal]) (by simp [setLocal, h14])
      (by simp [setLocal, h18]) hnc
  · have hnc3 : Algorithm.neighborCount12UInt w ≠ 3 := by
      simpa [Algorithm.neighborCount12UInt] using hc3
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
    refine eq_of_ite_branches (fun hc2 => ?_) (fun hc2 => ?_)
    · have hnc2 : Algorithm.neighborCount12UInt w = 2 := by
        simpa [Algorithm.neighborCount12UInt] using hc2
      f1_split_val_fuel 120
      flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
      refine eq_of_ite_branches (fun hbit => ?_) (fun hbit => ?_)
      · have hb : (w >>> 9 &&& 1) = 1 := by simpa using hbit
        exact bitwise_pc211 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
          w _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
          (by simp [setLocal, h8]) (by simp [setLocal]) (by simp [setLocal, h14])
          (by simp [setLocal, h18]) hnc2 hb
      · have hb : (w >>> 9 &&& 1) ≠ 1 := by simpa using hbit
        exact bitwise_pc206 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
          w _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
          (by simp [setLocal, h8]) (by simp [setLocal]) (by simp [setLocal, h14])
          (by simp [setLocal, h18]) hnc2 hb
    · have hnc2 : Algorithm.neighborCount12UInt w ≠ 2 := by
        simpa [Algorithm.neighborCount12UInt] using hc2
      exact bitwise_pc198 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega)
        w _ (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
        (by simp [setLocal, h8]) (by simp [setLocal]) (by simp [setLocal, h14])
        (by simp [setLocal, h18]) hnc3 hnc2

private def bitwiseInitLocals (w : UInt32) : Nat → JvmVal :=
  setLocal
    (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (fun _ => .i32 0) 0 (.i32 w))
        1 (.i32 0)) 2 (.i32 0)) 3 (.i32 0))
        4 (.i32 0)) 5 (.i32 0)) 6 (.i32 (w >>> 3 &&& 1)))
        7 (.i32 (w >>> 6 &&& 1))) 8 (.i32 (w >>> 7 &&& 1))) 9 (.i32 (w >>> 9 &&& 1)))
        10 (.i32 0)) 11 (.i32 0)) 12 (.i32 0))
        13 (.i32 (w >>> 11 &&& 1))) 14 (.i32 (w >>> 13 &&& 1))) 15 (.i32 0))
        16 (.i32 0)) 17 (.i32 (w >>> 14 &&& 1))) 18 (.i32 0))
    19 (.i32 (Algorithm.neighborCount22UInt w))

private theorem bitwise_pc131 {k : Nat} (hk : 1810 ≤ k) (w : UInt32)
    (hnc2 : Algorithm.neighborCount22UInt w = 2) (hb : (w >>> 12 &&& 1) ≠ 1) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 131
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 131)
      ⟨131, [], bitwiseInitLocals w, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 3
  apply bitwise_pc139 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [setLocal, Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc134 {k : Nat} (hk : 1810 ≤ k) (w : UInt32)
    (hnc2 : Algorithm.neighborCount22UInt w = 2) (hb : (w >>> 12 &&& 1) = 1) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 134
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 134)
      ⟨134, [], bitwiseInitLocals w, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 3
  apply bitwise_pc139 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [setLocal, Algorithm.bitRuleUInt, hnc2, hb])

private theorem bitwise_pc119 {k : Nat} (hk : 1810 ≤ k) (w : UInt32)
    (hnc3 : Algorithm.neighborCount22UInt w ≠ 3) (hnc2 : Algorithm.neighborCount22UInt w ≠ 2) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 119
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 119)
      ⟨119, [], bitwiseInitLocals w, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  step_val_n 3
  apply bitwise_pc139 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w _
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [setLocal, Algorithm.bitRuleUInt, hnc3, hnc2])

private theorem bitwise_pc0_nc2 {k : Nat} (hk : 2000 ≤ k) (w : UInt32)
    (hnc3 : Algorithm.neighborCount22UInt w ≠ 3) :
    runJvmValFast k f_Algorithm_computeNextGen4x4BitwiseUInt_prog 116
      (f_Algorithm_computeNextGen4x4BitwiseUInt_prog.drop 116)
      ⟨116, [], bitwiseInitLocals w, {}, ⟨[], [], []⟩⟩ =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc2 => ?_) (fun hc2 => ?_)
  · have hnc2 : Algorithm.neighborCount22UInt w = 2 := by
      simpa [Algorithm.neighborCount22UInt] using hc2
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
    refine eq_of_ite_branches (fun hbit => ?_) (fun hbit => ?_)
    · have hb : (w >>> 12 &&& 1) = 1 := by simpa [bitwiseInitLocals, setLocal] using hbit
      exact bitwise_pc134 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w hnc2 hb
    · have hb : (w >>> 12 &&& 1) ≠ 1 := by simpa [bitwiseInitLocals, setLocal] using hbit
      exact bitwise_pc131 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w hnc2 hb
  · have hnc2 : Algorithm.neighborCount22UInt w ≠ 2 := by
      simpa [Algorithm.neighborCount22UInt] using hc2
    exact bitwise_pc119 (by (try simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]); omega) w hnc3 hnc2

theorem computeNextGen4x4BitwiseUInt_equiv (w : UInt32) :
    runJvm 2400 f_Algorithm_computeNextGen4x4BitwiseUInt_prog (initJvmState [(0, .i32 w)]) =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_computeNextGen4x4BitwiseUInt_prog
  refine eq_of_ite_branches (fun hc3 => ?_) (fun hc3 => ?_)
  · have hnc : Algorithm.neighborCount22UInt w = 3 := by
      simpa [Algorithm.neighborCount22UInt] using hc3
    step_val_n 2
    apply bitwise_pc139 (by decide) w _
      rfl rfl rfl rfl rfl rfl rfl rfl
      (by simp [setLocal, Algorithm.bitRuleUInt, hnc])
  · have hnc3 : Algorithm.neighborCount22UInt w ≠ 3 := by
      simpa [Algorithm.neighborCount22UInt] using hc3
    exact bitwise_pc0_nc2 (by decide) w hnc3


end Algorithm.JvmVerification
