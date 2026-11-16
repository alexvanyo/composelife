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

import proofs.KotlinJvmEquiv.CalculatorUiBase

namespace MosaicCalculator.KotlinJvmVerification

open MosaicCalculator.JvmVerification
open MosaicCalculator.KotlinJvmBytecode
open MosaicCalculator.Model

private instance instHasDefaultIsZeroCalc (r : String → Option (List JvmInstr)) (d f : Nat) :
    Jvm.HasDefaultIsZero (mkCalcHooks r d f) where
  isZero?_eq := by cases d <;> rfl

private theorem i64ToDecimalString_eq_int64ToString (v : Int64) :
    Jvm.i64ToDecimalString v.toUInt64 = int64ToString v := by
  unfold Jvm.i64ToDecimalString int64ToString
  have h1 := v.toInt_lt
  have h2 := v.le_toInt
  have hbv := BitVec.toInt_eq_toNat_cond v.toBitVec
  have hbvNat : v.toUInt64.toNat = v.toBitVec.toNat := rfl
  have htoInt : v.toInt = v.toBitVec.toInt := rfl
  by_cases hnonneg : (0 : Int) ≤ v.toInt
  · have hcond : 2 * v.toBitVec.toNat < 18446744073709551616 := by omega
    have hu : v.toUInt64.toNat = v.toInt.toNat := by omega
    have hult : v.toUInt64 < 0x8000000000000000 := by
      change v.toUInt64.toNat < 9223372036854775808
      omega
    simp only [hult, ↓reduceIte, hu]
    have hEq : v.toInt = (v.toInt.toNat : Int) := by omega
    rw [hEq]
    rfl
  · have hcond : ¬ (2 * v.toBitVec.toNat < 18446744073709551616) := by omega
    have hu : v.toUInt64.toNat = 18446744073709551616 - (-v.toInt).toNat := by omega
    have huge : ¬ (v.toUInt64 < 0x8000000000000000) := by
      change ¬ (v.toUInt64.toNat < 9223372036854775808)
      omega
    simp only [huge, ↓reduceIte, hu]
    have hdiff : 18446744073709551616 - (18446744073709551616 - (-v.toInt).toNat) =
        (-v.toInt).toNat := by
      omega
    rw [hdiff]
    have hnat : (-v.toInt).toNat = ((-v.toInt).toNat - 1) + 1 := by omega
    have hEq : v.toInt = -((-v.toInt).toNat : Int) := by omega
    rw [hEq, hnat]
    rfl

/-! ### Common Fast Step Helpers -/

private theorem runFast_areturn {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .areturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runFast_goto {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 target : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.goto target :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  rfl

private theorem runFast_ifne_branch [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (h : v ≠ 0) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks), h]

private theorem runFast_ifne_fallthrough [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest)
        ⟨pc0, .i32 0 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks)]

private theorem runFast_ifnull_branch {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnull target :: rest) ⟨pc0, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.isNull]

private theorem runFast_ifnull_fallthrough {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnn : v.isNull = false) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnull target :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hnn]

private theorem runFast_ifnonnull_branch' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnn : v.isNull = false) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hnn]

private theorem runFast_ifnonnull_fallthrough' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc0, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.isNull]

private theorem runFast_tableswitch {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 : Nat} {low : Int32} {targets : List Nat} {defTarget : Nat}
    {prog rest : List JvmInstr} {key : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.tableswitch low targets defTarget :: rest)
        ⟨pc0, .i32 key :: stk, locs, jh, hp⟩ =
      let target := Jvm.tableswitchTarget key low targets defTarget
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]

private theorem runFast_lookupswitch {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 : Nat} {cases : List (Int32 × Nat)} {defTarget : Nat}
    {prog rest : List JvmInstr} {key : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.lookupswitch cases defTarget :: rest)
        ⟨pc0, .i32 key :: stk, locs, jh, hp⟩ =
      let target := Jvm.lookupswitchTarget key cases defTarget
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]

/-! ### `formatDisplayLine` Proof -/

private theorem runFast_getError (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {cSt : CalculatorState} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getError"
          "()Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorError;" :: rest)
        ⟨pc0, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, (match cSt.error with | some e => .ext (.calcErr e) | none => .null) :: stk,
          locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getError"
        "()Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorError;")
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        (match cSt.error with | some e => .ext (.calcErr e) | none => .null) :: stk,
        locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getPendingOp (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {cSt : CalculatorState} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getPendingOp"
          "()Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;" :: rest)
        ⟨pc0, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, (match cSt.pendingOp with | some o => .ext (.calcOp o) | none => .null) :: stk,
          locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getPendingOp"
        "()Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;")
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        (match cSt.pendingOp with | some o => .ext (.calcOp o) | none => .null) :: stk,
        locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getPendingOperand (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {cSt : CalculatorState}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getPendingOperand"
          "()Ljava/lang/Long;" :: rest)
        ⟨pc0, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, (match cSt.pendingOperand with | some v => .boxedLong v.toUInt64 | none => .null) :: stk,
          locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getPendingOperand"
        "()Ljava/lang/Long;")
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        (match cSt.pendingOperand with | some v => .boxedLong v.toUInt64 | none => .null) :: stk,
        locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getDisplayValue (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {cSt : CalculatorState}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getDisplayValue"
          "()J" :: rest)
        ⟨pc0, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 cSt.displayValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "getDisplayValue"
        "()J")
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 cSt.displayValue.toUInt64 :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getSymbol (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {op : CalculatorOp} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" "getSymbol"
          "()Ljava/lang/String;" :: rest)
        ⟨pc0, .ext (.calcOp op) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str op.symbol :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" "getSymbol"
        "()Ljava/lang/String;")
      ⟨pc, .ext (.calcOp op) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str op.symbol :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_errOrdinal (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {err : CalculatorError} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorError" "ordinal"
          "()I" :: rest)
        ⟨pc0, .ext (.calcErr err) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (match err with | .divideByZero => 0 | .overflow => 1) :: stk,
          locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorError" "ordinal"
        "()I")
      ⟨pc, .ext (.calcErr err) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (match err with | .divideByZero => 0 | .overflow => 1) :: stk,
        locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getStatic_when1 (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 errAddr : Nat) {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hs1 : jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr)) :
    Jvm.runJvmResFast (mkCalcHooks r d subFuel) (f + 1) prog pc
        (.getstatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
          "$EnumSwitchMapping$1" "[I" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef errAddr :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r d subFuel)
      (.getstatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" "[I")
      ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef errAddr :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hs1]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r d subFuel) rfl (by simp) hs rfl

private theorem runFast_stringValueOfJ (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {x : Int64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "java/lang/String" "valueOf" "(J)Ljava/lang/String;" :: rest)
        ⟨pc0, .i64 x.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str (int64ToString x) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokestatic "java/lang/String" "valueOf" "(J)Ljava/lang/String;")
      ⟨pc, .i64 x.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str (int64ToString x) :: stk, locs, jh, hp⟩) := by
    rw [← i64ToDecimalString_eq_int64ToString x]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_makeConcat_fmt (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {lhs rhs : Int64} {op : CalculatorOp}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "makeConcatWithConstants" "\x01 \x01 \x01"
          "(Ljava/lang/Long;Ljava/lang/String;J)Ljava/lang/String;" :: rest)
        ⟨pc0, .i64 rhs.toUInt64 :: .str op.symbol :: .boxedLong lhs.toUInt64 :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str s!"{int64ToString lhs} {op.symbol} {int64ToString rhs}" :: stk,
          locs, jh, hp⟩ := by
  have hcat : Jvm.evalMakeConcatWithConstants "\x01 \x01 \x01"
      "(Ljava/lang/Long;Ljava/lang/String;J)Ljava/lang/String;"
      (.i64 rhs.toUInt64 :: .str op.symbol :: .boxedLong lhs.toUInt64 :: stk) =
      some (Jvm.i64ToDecimalString lhs.toUInt64 ++
        (" " ++ (op.symbol ++ (" " ++ (Jvm.i64ToDecimalString rhs.toUInt64 ++ "")))), stk) := by
    dsimp only [Jvm.evalMakeConcatWithConstants]
    have hm1 : Jvm.parseMethodParamTags
        "(Ljava/lang/Long;Ljava/lang/String;J)Ljava/lang/String;" = ['L', 'L', 'J'] := by decide
    have hm2 : String.toList "\x01 \x01 \x01" = ['\x01', ' ', '\x01', ' ', '\x01'] := by decide
    rw [hm1, hm2]
    dsimp only [List.length]
    split
    · omega
    · rfl
  have hstr : Jvm.i64ToDecimalString lhs.toUInt64 ++
      (" " ++ (op.symbol ++ (" " ++ (Jvm.i64ToDecimalString rhs.toUInt64 ++ "")))) =
      s!"{int64ToString lhs} {op.symbol} {int64ToString rhs}" := by
    rw [i64ToDecimalString_eq_int64ToString lhs, i64ToDecimalString_eq_int64ToString rhs]
    simp only [String.append_empty, ← String.append_assoc]
    rfl
  rw [hstr] at hcat
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokedynamic "makeConcatWithConstants" "\x01 \x01 \x01"
        "(Ljava/lang/Long;Ljava/lang/String;J)Ljava/lang/String;")
      ⟨pc, .i64 rhs.toUInt64 :: .str op.symbol :: .boxedLong lhs.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .str s!"{int64ToString lhs} {op.symbol} {int64ToString rhs}" :: stk,
        locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hm : ("makeConcatWithConstants" == "makeConcatWithConstants") = true := rfl
    change (if ("makeConcatWithConstants" == "makeConcatWithConstants") = true then
      match Jvm.evalMakeConcatWithConstants "\x01 \x01 \x01"
          "(Ljava/lang/Long;Ljava/lang/String;J)Ljava/lang/String;"
          (.i64 rhs.toUInt64 :: .str op.symbol :: .boxedLong lhs.toUInt64 :: stk) with
      | some (s, rest) =>
        Sum.inl (some (Jvm.JvmState.mk (pc + 1) (.str s :: rest) locs jh hp : JvmState))
      | none => Sum.inr none
      else _) = _
    rw [hm, hcat]
    simp only [↓reduceIte]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_checkNotNullParam' (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {param : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnn : v.isNull = false) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str param :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    simp [hnn]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem exists_run_done' {f : Option (JvmVal × JvmState)}
    {v : JvmVal} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (h : f = some (v, ⟨pc, stk, locs, jh, hp⟩)) :
    ∃ endSt, f = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp :=
  ⟨_, h, rfl, rfl⟩

/-- Bytecode equivalence theorem for `CalculatorEngineKt.formatDisplayLine`. -/
theorem formatDisplayLine_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 35 ≤ fuel) (cSt : CalculatorState) (hp : CalcHeap)
    (jh : Jvm.JvmHeap CalcExt)
    (herrSwitch : ∃ errAddr,
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
      jh.get? errAddr = some (.intArray #[1, 2])) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel formatDisplayLine_prog
          (initCalcJvmState [(0, .ext (.calcState cSt))] hp jh) =
        some (.str (formatDisplayLineModel cSt), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d' + 1) subFuel) (k + 35)
          formatDisplayLine_prog 0 formatDisplayLine_prog
          (initCalcJvmState [(0, .ext (.calcState cSt))] hp jh) =
        some (.str (formatDisplayLineModel cSt), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal := @setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt))
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d' + 1) subFuel) (k + 35)
          formatDisplayLine_prog 0 formatDisplayLine_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.str (formatDisplayLineModel cSt), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp
  dsimp only [formatDisplayLine_prog]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam' resolveProg d' subFuel _ _ _ rfl]
  rw [runFast_aload, hl0, runFast_getError, runFast_dup]
  cases hcErr : cSt.error with
  | some err =>
    rw [runFast_ifnonnull_branch' (by cases err <;> rfl)]
    dsimp only [formatDisplayLine_prog, List.drop]
    obtain ⟨errAddr, hStat, hArr⟩ := herrSwitch
    rw [runFast_getStatic_when1 resolveProg (d' + 1) subFuel _ 10 10 errAddr hStat]
    rw [runFast_swap, runFast_errOrdinal]
    cases err with
    | divideByZero =>
      rw [Jvm.runJvmResFast_iaload (hooks := mkCalcHooks resolveProg (d' + 1) subFuel)
        hArr (by decide) (by decide)]
      have hi0 : (#[1, 2] : Array UInt32)[UInt32.toNat 0] = 1 := rfl
      rw [hi0, runFast_tableswitch]
      have ht : Jvm.tableswitchTarget 1 (-1) [19, 40, 15, 17] 40 = 15 := rfl
      dsimp only; rw [ht]
      dsimp only [formatDisplayLine_prog, List.drop, formatDisplayLineModel]
      rw [hcErr]
      dsimp only
      rw [runFast_ldcStr, runFast_goto]
      dsimp only [formatDisplayLine_prog, List.drop]
      rw [runFast_areturn]
      exact exists_run_done' rfl
    | overflow =>
      rw [Jvm.runJvmResFast_iaload (hooks := mkCalcHooks resolveProg (d' + 1) subFuel)
        hArr (by decide) (by decide)]
      have hi1 : (#[1, 2] : Array UInt32)[UInt32.toNat 1] = 2 := rfl
      rw [hi1, runFast_tableswitch]
      have ht : Jvm.tableswitchTarget 2 (-1) [19, 40, 15, 17] 40 = 17 := rfl
      dsimp only; rw [ht]
      dsimp only [formatDisplayLine_prog, List.drop, formatDisplayLineModel]
      rw [hcErr]
      dsimp only
      rw [runFast_ldcStr, runFast_goto]
      dsimp only [formatDisplayLine_prog, List.drop]
      rw [runFast_areturn]
      exact exists_run_done' rfl
  | none =>
    rw [runFast_ifnonnull_fallthrough', runFast_pop, runFast_iconst, runFast_goto]
    dsimp only [formatDisplayLine_prog, List.drop]
    rw [runFast_tableswitch]
    have ht : Jvm.tableswitchTarget 4294967295 (-1) [19, 40, 15, 17] 40 = 19 := by decide
    dsimp only; rw [ht]
    dsimp only [formatDisplayLine_prog, List.drop]
    rw [runFast_aload, hl0, runFast_getPendingOp, runFast_astore]
    have hl0' : (@setLocal CalcExt locs0 1
        (match cSt.pendingOp with | some o => .ext (.calcOp o) | none => .null)) 0 =
        .ext (.calcState cSt) := rfl
    rw [runFast_aload, hl0', runFast_getPendingOperand, runFast_astore]
    dsimp only [formatDisplayLineModel]
    rw [hcErr]
    dsimp only
    cases hOp : cSt.pendingOp with
    | none =>
      have hl1 : (@setLocal CalcExt (@setLocal CalcExt locs0 1 .null) 2
          (match cSt.pendingOperand with | some v => .boxedLong v.toUInt64 | none => .null)) 1 =
          .null := rfl
      have hl0'' : (@setLocal CalcExt (@setLocal CalcExt locs0 1 .null) 2
          (match cSt.pendingOperand with | some v => .boxedLong v.toUInt64 | none => .null)) 0 =
          .ext (.calcState cSt) := rfl
      rw [runFast_aload, hl1, runFast_ifnull_branch]
      dsimp only [formatDisplayLine_prog, List.drop]
      rw [runFast_aload, hl0'', runFast_getDisplayValue, runFast_stringValueOfJ, runFast_goto]
      dsimp only [formatDisplayLine_prog, List.drop]
      rw [runFast_areturn]
      cases cSt.pendingOperand <;> exact exists_run_done' rfl
    | some op =>
      have hl1 : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2
          (match cSt.pendingOperand with | some v => .boxedLong v.toUInt64 | none => .null)) 1 =
          .ext (.calcOp op) := rfl
      rw [runFast_aload, hl1, runFast_ifnull_fallthrough (by rfl), runFast_aload]
      cases hOpnd : cSt.pendingOperand with
      | none =>
        have hl2 : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2 .null) 2 =
            .null := rfl
        have hl0'' : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2 .null) 0 =
            .ext (.calcState cSt) := rfl
        rw [hl2]
        dsimp only
        rw [runFast_ifnull_branch]
        dsimp only [formatDisplayLine_prog, List.drop]
        rw [runFast_aload, hl0'', runFast_getDisplayValue, runFast_stringValueOfJ, runFast_goto]
        dsimp only [formatDisplayLine_prog, List.drop]
        rw [runFast_areturn]
        exact exists_run_done' rfl
      | some lhs =>
        have hl2 : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2
            (.boxedLong lhs.toUInt64)) 2 = .boxedLong lhs.toUInt64 := rfl
        have hl1' : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2
            (.boxedLong lhs.toUInt64)) 1 = .ext (.calcOp op) := rfl
        have hl0'' : (@setLocal CalcExt (@setLocal CalcExt locs0 1 (.ext (.calcOp op))) 2
            (.boxedLong lhs.toUInt64)) 0 = .ext (.calcState cSt) := rfl
        rw [hl2]
        dsimp only
        rw [runFast_ifnull_fallthrough (by rfl)]
        rw [runFast_aload, hl2, runFast_aload, hl1', runFast_getSymbol,
          runFast_aload, hl0'', runFast_getDisplayValue, runFast_makeConcat_fmt, runFast_goto]
        dsimp only [formatDisplayLine_prog, List.drop]
        rw [runFast_areturn]
        exact exists_run_done' rfl

/-! ### `mapTerminalKey` Proof -/

private theorem runFast_stringHashCode (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {s : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "java/lang/String" "hashCode" "()I" :: rest)
        ⟨pc0, .str s :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (javaStringHashCode s) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "java/lang/String" "hashCode" "()I")
      ⟨pc, .str s :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (javaStringHashCode s) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_stringEquals (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {s1 s2 : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, .str s2 :: .str s1 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if s1 == s2 then 1 else 0) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z")
      ⟨pc, .str s2 :: .str s1 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if s1 == s2 then 1 else 0) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_newClass (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {cls : String} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnsb : cls ≠ "java/lang/StringBuilder") :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc (.newClass cls :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel) (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, mkCalcHooks]
    rw [Jvm.ite_bool_eq_true_right (beq_false_of_ne hnsb)]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_digitInit (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {n : UInt32} {c1 c2 : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Digit" "<init>" "(I)V" :: rest)
        ⟨pc0, .i32 n :: .allocRef c1 :: .allocRef c2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcKey (.digit n)) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Digit" "<init>" "(I)V")
      ⟨pc, .i32 n :: .allocRef c1 :: .allocRef c2 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.calcKey (.digit n)) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_opInit (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {op : CalculatorOp} {c1 c2 : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Op" "<init>"
          "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;)V" :: rest)
        ⟨pc0, .ext (.calcOp op) :: .allocRef c1 :: .allocRef c2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcKey (.op op)) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Op" "<init>"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;)V")
      ⟨pc, .ext (.calcOp op) :: .allocRef c1 :: .allocRef c2 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.calcKey (.op op)) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getStatic_cleanCalc (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {cls fld desc : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnone : jh.getStatic? cls fld = none)
    (hres : (mkCalcHooks r (d + 1) subFuel).resolveStatic ⟨pc, stk, locs, jh, hp⟩ cls fld desc = some v) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.getstatic cls fld desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel) (.getstatic cls fld desc)
      ⟨pc, stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hnone, hres]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem mapKey_finish_miss (r : String → Option (List JvmInstr)) (d subFuel k t : Nat)
    {lit : String} {hitPc : Nat} {rest : List JvmInstr} {key : String}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hl1 : locs 1 = .str key) (hne : key ≠ lit)
    (hdrop : mapTerminalKey_prog.drop t =
      .aload 1 :: .ldcStr lit :: .invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" ::
        .ifne hitPc :: .goto 201 :: rest) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (k + 8) mapTerminalKey_prog t (mapTerminalKey_prog.drop t)
        ⟨t, [], locs, jh, hp⟩ =
      some (.null, ⟨202, [.null], locs, jh, hp⟩) := by
  rw [hdrop]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_stringEquals]
  have hbeq : (key == lit) = false := beq_false_of_ne hne
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [runFast_ifne_fallthrough, runFast_goto]
  dsimp only [mapTerminalKey_prog, List.drop]
  rw [runFast_aconstNull, runFast_areturn]

private def mapKeyCases : List (Int32 × Nat) :=
  [(-937491361, 13), (42, 28), (43, 33), (45, 38), (47, 43), (48, 48), (49, 53), (50, 58),
    (51, 63), (52, 68), (53, 73), (54, 78), (55, 83), (56, 88), (57, 98), (61, 103),
    (67, 23), (99, 18), (67114680, 93), (2084662433, 8)]

private def ValidMissBucket (key : String) (t : Nat) : Prop :=
  t = 201 ∨
  ∃ lit hitPc rest,
    mapTerminalKey_prog.drop t =
      .aload 1 :: .ldcStr lit :: .invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" ::
        .ifne hitPc :: .goto 201 :: rest ∧
    key ≠ lit

private theorem runFast_checkCast_calcKey (r : String → Option (List JvmInstr))
    (d subFuel f pc pc0 : Nat) {prog rest : List JvmInstr} {ck : CalculatorKey}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey" :: rest)
        ⟨pc0, .ext (.calcKey ck) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcKey ck) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks r (d + 1) subFuel)
      (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey")
      ⟨pc, .ext (.calcKey ck) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.calcKey ck) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks r (d + 1) subFuel) rfl (by simp) hs rfl

private theorem lookupswitch_valid_miss_bucket (key : String)
    (h0 : key ≠ "0") (h1 : key ≠ "1") (h2 : key ≠ "2") (h3 : key ≠ "3") (h4 : key ≠ "4")
    (h5 : key ≠ "5") (h6 : key ≠ "6") (h7 : key ≠ "7") (h8 : key ≠ "8") (h9 : key ≠ "9")
    (hAdd : key ≠ "+") (hSub : key ≠ "-") (hMul : key ≠ "*") (hDiv : key ≠ "/")
    (hEq : key ≠ "=") (hEnt : key ≠ "Enter") (hc : key ≠ "c") (hC : key ≠ "C")
    (hEsc : key ≠ "Escape") (hBs : key ≠ "Backspace") :
    ValidMissBucket key (Jvm.lookupswitchTarget (javaStringHashCode key) mapKeyCases 201) := by
  unfold Jvm.lookupswitchTarget mapKeyCases
  rw [List.find?_cons]; dsimp only
  by_cases c1 : (-937491361 : Int32).toUInt32 == javaStringHashCode key
  · rw [c1]; exact Or.inr ⟨_, _, _, rfl, hBs⟩
  rw [Bool.eq_false_iff.mpr c1]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c2 : (42 : Int32).toUInt32 == javaStringHashCode key
  · rw [c2]; exact Or.inr ⟨_, _, _, rfl, hMul⟩
  rw [Bool.eq_false_iff.mpr c2]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c3 : (43 : Int32).toUInt32 == javaStringHashCode key
  · rw [c3]; exact Or.inr ⟨_, _, _, rfl, hAdd⟩
  rw [Bool.eq_false_iff.mpr c3]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c4 : (45 : Int32).toUInt32 == javaStringHashCode key
  · rw [c4]; exact Or.inr ⟨_, _, _, rfl, hSub⟩
  rw [Bool.eq_false_iff.mpr c4]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c5 : (47 : Int32).toUInt32 == javaStringHashCode key
  · rw [c5]; exact Or.inr ⟨_, _, _, rfl, hDiv⟩
  rw [Bool.eq_false_iff.mpr c5]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c6 : (48 : Int32).toUInt32 == javaStringHashCode key
  · rw [c6]; exact Or.inr ⟨_, _, _, rfl, h0⟩
  rw [Bool.eq_false_iff.mpr c6]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c7 : (49 : Int32).toUInt32 == javaStringHashCode key
  · rw [c7]; exact Or.inr ⟨_, _, _, rfl, h1⟩
  rw [Bool.eq_false_iff.mpr c7]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c8 : (50 : Int32).toUInt32 == javaStringHashCode key
  · rw [c8]; exact Or.inr ⟨_, _, _, rfl, h2⟩
  rw [Bool.eq_false_iff.mpr c8]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c9 : (51 : Int32).toUInt32 == javaStringHashCode key
  · rw [c9]; exact Or.inr ⟨_, _, _, rfl, h3⟩
  rw [Bool.eq_false_iff.mpr c9]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c10 : (52 : Int32).toUInt32 == javaStringHashCode key
  · rw [c10]; exact Or.inr ⟨_, _, _, rfl, h4⟩
  rw [Bool.eq_false_iff.mpr c10]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c11 : (53 : Int32).toUInt32 == javaStringHashCode key
  · rw [c11]; exact Or.inr ⟨_, _, _, rfl, h5⟩
  rw [Bool.eq_false_iff.mpr c11]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c12 : (54 : Int32).toUInt32 == javaStringHashCode key
  · rw [c12]; exact Or.inr ⟨_, _, _, rfl, h6⟩
  rw [Bool.eq_false_iff.mpr c12]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c13 : (55 : Int32).toUInt32 == javaStringHashCode key
  · rw [c13]; exact Or.inr ⟨_, _, _, rfl, h7⟩
  rw [Bool.eq_false_iff.mpr c13]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c14 : (56 : Int32).toUInt32 == javaStringHashCode key
  · rw [c14]; exact Or.inr ⟨_, _, _, rfl, h8⟩
  rw [Bool.eq_false_iff.mpr c14]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c15 : (57 : Int32).toUInt32 == javaStringHashCode key
  · rw [c15]; exact Or.inr ⟨_, _, _, rfl, h9⟩
  rw [Bool.eq_false_iff.mpr c15]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c16 : (61 : Int32).toUInt32 == javaStringHashCode key
  · rw [c16]; exact Or.inr ⟨_, _, _, rfl, hEq⟩
  rw [Bool.eq_false_iff.mpr c16]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c17 : (67 : Int32).toUInt32 == javaStringHashCode key
  · rw [c17]; exact Or.inr ⟨_, _, _, rfl, hC⟩
  rw [Bool.eq_false_iff.mpr c17]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c18 : (99 : Int32).toUInt32 == javaStringHashCode key
  · rw [c18]; exact Or.inr ⟨_, _, _, rfl, hc⟩
  rw [Bool.eq_false_iff.mpr c18]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c19 : (67114680 : Int32).toUInt32 == javaStringHashCode key
  · rw [c19]; exact Or.inr ⟨_, _, _, rfl, hEnt⟩
  rw [Bool.eq_false_iff.mpr c19]; dsimp only
  rw [List.find?_cons]; dsimp only
  by_cases c20 : (2084662433 : Int32).toUInt32 == javaStringHashCode key
  · rw [c20]; exact Or.inr ⟨_, _, _, rfl, hEsc⟩
  rw [Bool.eq_false_iff.mpr c20]; dsimp only
  exact Or.inl rfl

private theorem mapKey_hit_digit (r : String → Option (List JvmInstr)) (d subFuel k : Nat)
    (lit : String) (t hitPc : Nat) (dig : UInt32) (rest1 rest2 : List JvmInstr)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap CalcExt) (hp : CalcHeap)
    (hl1 : locs 1 = .str lit)
    (hhash : Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201 = t)
    (hdrop1 : mapTerminalKey_prog.drop t =
      .aload 1 :: .ldcStr lit :: .invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" ::
        .ifne hitPc :: .goto 201 :: rest1)
    (hdrop2 : mapTerminalKey_prog.drop hitPc =
      .newClass "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Digit" ::
      .dup :: .iconst dig ::
      .invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Digit" "<init>" "(I)V" ::
      .checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey" ::
      .goto 202 :: rest2) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (k + 12) mapTerminalKey_prog
        (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201)
        (mapTerminalKey_prog.drop (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201))
        ⟨Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201, [], locs, jh, hp⟩ =
      some (.ext (.calcKey (.digit dig)), ⟨202, [.ext (.calcKey (.digit dig))], locs, jh, hp⟩) := by
  rw [hhash, hdrop1]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_stringEquals]
  have hbeq : (lit == lit) = true := beq_self_eq_true lit
  rw [hbeq]
  simp only [↓reduceIte]
  rw [runFast_ifne_branch (by decide), hdrop2]
  rw [runFast_newClass r d subFuel _ _ _ (by decide), runFast_dup, runFast_iconst, runFast_digitInit]
  rw [runFast_checkCast_calcKey r d subFuel]
  rw [runFast_goto]
  dsimp only [mapTerminalKey_prog, List.drop]
  rw [runFast_areturn]

private theorem mapKey_hit_op (r : String → Option (List JvmInstr)) (d subFuel k : Nat)
    (lit fld : String) (op : CalculatorOp) (t hitPc : Nat) (rest1 rest2 : List JvmInstr)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap CalcExt) (hp : CalcHeap)
    (hl1 : locs 1 = .str lit)
    (hclean : jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" fld = none)
    (hres : ∀ pc stk, (mkCalcHooks r (d + 1) subFuel).resolveStatic ⟨pc, stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" fld
        "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;" = some (.ext (.calcOp op)))
    (hhash : Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201 = t)
    (hdrop1 : mapTerminalKey_prog.drop t =
      .aload 1 :: .ldcStr lit :: .invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" ::
        .ifne hitPc :: .goto 201 :: rest1)
    (hdrop2 : mapTerminalKey_prog.drop hitPc =
      .newClass "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Op" ::
      .dup ::
      .getstatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" fld
        "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;" ::
      .invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Op" "<init>"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;)V" ::
      .checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey" ::
      .goto 202 :: rest2) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (k + 12) mapTerminalKey_prog
        (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201)
        (mapTerminalKey_prog.drop (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201))
        ⟨Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201, [], locs, jh, hp⟩ =
      some (.ext (.calcKey (.op op)), ⟨202, [.ext (.calcKey (.op op))], locs, jh, hp⟩) := by
  rw [hhash, hdrop1]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_stringEquals]
  have hbeq : (lit == lit) = true := beq_self_eq_true lit
  rw [hbeq]
  simp only [↓reduceIte]
  rw [runFast_ifne_branch (by decide), hdrop2]
  rw [runFast_newClass r d subFuel _ _ _ (by decide), runFast_dup]
  rw [runFast_getStatic_cleanCalc r d subFuel _ _ _ hclean (hres _ _)]
  rw [runFast_opInit]
  rw [runFast_checkCast_calcKey r d subFuel]
  rw [runFast_goto]
  dsimp only [mapTerminalKey_prog, List.drop]
  rw [runFast_areturn]

private theorem mapKey_hit_singleton (r : String → Option (List JvmInstr)) (d subFuel k : Nat)
    (lit cls desc : String) (ck : CalculatorKey) (t hitPc : Nat) (rest1 rest2 : List JvmInstr)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap CalcExt) (hp : CalcHeap)
    (hl1 : locs 1 = .str lit)
    (hclean : jh.getStatic? cls "INSTANCE" = none)
    (hres : ∀ pc stk, (mkCalcHooks r (d + 1) subFuel).resolveStatic ⟨pc, stk, locs, jh, hp⟩
        cls "INSTANCE" desc = some (.ext (.calcKey ck)))
    (hhash : Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201 = t)
    (hdrop1 : mapTerminalKey_prog.drop t =
      .aload 1 :: .ldcStr lit :: .invokevirtual "java/lang/String" "equals" "(Ljava/lang/Object;)Z" ::
        .ifne hitPc :: .goto 201 :: rest1)
    (hdrop2 : mapTerminalKey_prog.drop hitPc =
      .getstatic cls "INSTANCE" desc ::
      .checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey" ::
      .goto 202 :: rest2) :
    Jvm.runJvmResFast (mkCalcHooks r (d + 1) subFuel) (k + 10) mapTerminalKey_prog
        (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201)
        (mapTerminalKey_prog.drop (Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201))
        ⟨Jvm.lookupswitchTarget (javaStringHashCode lit) mapKeyCases 201, [], locs, jh, hp⟩ =
      some (.ext (.calcKey ck), ⟨202, [.ext (.calcKey ck)], locs, jh, hp⟩) := by
  rw [hhash, hdrop1]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_stringEquals]
  have hbeq : (lit == lit) = true := beq_self_eq_true lit
  rw [hbeq]
  simp only [↓reduceIte]
  rw [runFast_ifne_branch (by decide), hdrop2]
  rw [runFast_getStatic_cleanCalc r d subFuel _ _ _ hclean (hres _ _)]
  rw [runFast_checkCast_calcKey r d subFuel]
  rw [runFast_goto]
  dsimp only [mapTerminalKey_prog, List.drop]
  rw [runFast_areturn]

/-- Bytecode equivalence theorem for `CalculatorEngineKt.mapTerminalKey`. -/
theorem mapTerminalKey_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 25 ≤ fuel) (key : String) (hp : CalcHeap)
    (jh : Jvm.JvmHeap CalcExt)
    (hstat : ∀ cls fld,
      cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
      cls ≠ "ComposableSingletons$CalculatorScreenKt" →
      jh.getStatic? cls fld = none) :
    let expected : JvmVal := match mapTerminalKeyModel key with
      | some k => .ext (.calcKey k)
      | none => .null
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel mapTerminalKey_prog
          (initCalcJvmState [(0, .str key)] hp jh) =
        some (expected, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  intro expected
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨202, [expected], @setLocal CalcExt (@setLocal CalcExt (fun _ => .i32 0) 0 (.str key)) 1 (.str key), jh, hp⟩,
    Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, rfl, rfl⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  have hl0 : (@setLocal CalcExt (fun _ => .i32 0) 0 (.str key)) 0 = .str key := rfl
  dsimp only [mapTerminalKey_prog]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam' resolveProg d' subFuel _ _ _ rfl]
  rw [runFast_aload, hl0, runFast_astore]
  let locs1 : Nat → JvmVal :=
    @setLocal CalcExt (@setLocal CalcExt (fun _ => .i32 0) 0 (.str key)) 1 (.str key)
  have hl1 : locs1 1 = .str key := rfl
  change Jvm.runJvmResFast (mkCalcHooks resolveProg (d' + 1) subFuel) (k + 20) mapTerminalKey_prog
      5 (mapTerminalKey_prog.drop 5) ⟨5, [], locs1, jh, hp⟩ = _
  dsimp only [mapTerminalKey_prog, List.drop]
  rw [runFast_aload, hl1, runFast_stringHashCode, runFast_lookupswitch]
  change Jvm.runJvmResFast (mkCalcHooks resolveProg (d' + 1) subFuel) (k + 17) mapTerminalKey_prog
      (Jvm.lookupswitchTarget (javaStringHashCode key) mapKeyCases 201)
      (mapTerminalKey_prog.drop (Jvm.lookupswitchTarget (javaStringHashCode key) mapKeyCases 201))
      ⟨Jvm.lookupswitchTarget (javaStringHashCode key) mapKeyCases 201, [], locs1, jh, hp⟩ =
    some (expected, ⟨202, [expected], locs1, jh, hp⟩)
  by_cases h0 : key = "0"
  · subst h0; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "0" 48 108 0 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h1 : key = "1"
  · subst h1; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "1" 53 114 1 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h2 : key = "2"
  · subst h2; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "2" 58 120 2 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h3 : key = "3"
  · subst h3; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "3" 63 126 3 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h4 : key = "4"
  · subst h4; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "4" 68 132 4 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h5 : key = "5"
  · subst h5; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "5" 73 138 5 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h6 : key = "6"
  · subst h6; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "6" 78 144 6 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h7 : key = "7"
  · subst h7; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "7" 83 150 7 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h8 : key = "8"
  · subst h8; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "8" 88 156 8 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases h9 : key = "9"
  · subst h9; exact mapKey_hit_digit resolveProg d' subFuel (k + 5) "9" 98 162 9 _ _ locs1 jh hp hl1 (by decide) rfl rfl
  by_cases hAdd : key = "+"
  · subst hAdd
    exact mapKey_hit_op resolveProg d' subFuel (k + 5) "+" "Add" .add 33 168 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hSub : key = "-"
  · subst hSub
    exact mapKey_hit_op resolveProg d' subFuel (k + 5) "-" "Sub" .sub 38 174 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hMul : key = "*"
  · subst hMul
    exact mapKey_hit_op resolveProg d' subFuel (k + 5) "*" "Mul" .mul 28 180 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hDiv : key = "/"
  · subst hDiv
    exact mapKey_hit_op resolveProg d' subFuel (k + 5) "/" "Div" .div 43 186 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hEq : key = "="
  · subst hEq
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "="
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Equals"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Equals;"
      .equals 103 192 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hEnt : key = "Enter"
  · subst hEnt
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "Enter"
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Equals"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Equals;"
      .equals 93 192 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hc : key = "c"
  · subst hc
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "c"
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear;"
      .clear 18 195 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hC : key = "C"
  · subst hC
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "C"
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear;"
      .clear 23 195 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hEsc : key = "Escape"
  · subst hEsc
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "Escape"
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear;"
      .clear 8 195 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  by_cases hBs : key = "Backspace"
  · subst hBs
    exact mapKey_hit_singleton resolveProg d' subFuel (k + 7) "Backspace"
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Backspace"
      "Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Backspace;"
      .backspace 13 198 _ _ locs1 jh hp hl1
      (hstat _ _ (by decide) (by decide)) (fun _ _ => by rfl) (by decide) rfl rfl
  have hexp : expected = .null := by
    dsimp only [expected, mapTerminalKeyModel]
    split
    · case h_1 k heq =>
      split at heq <;> first | contradiction | simp at heq
    · rfl
  rw [hexp]
  have hmb := lookupswitch_valid_miss_bucket key h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hAdd hSub hMul hDiv
    hEq hEnt hc hC hEsc hBs
  rcases hmb with ht | ⟨lit, hitPc, rest, hdrop, hne⟩
  · rw [ht]
    dsimp only [mapTerminalKey_prog, List.drop]
    rw [runFast_aconstNull, runFast_areturn]
  · exact mapKey_finish_miss resolveProg d' subFuel (k + 9) _ hl1 hne hdrop

end MosaicCalculator.KotlinJvmVerification
