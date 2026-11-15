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
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Family 6c: RLE Serialization & `finishRLE` -/

private theorem list_drop_step {α : Type} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  induction k generalizing l with
  | zero => cases l <;> simp_all
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons a as => exact ih h

open Lean Elab Tactic in
elab "step_drop6c " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| (conv => lhs; arg 4; rw [list_drop_step rfl]; try simp only [Nat.reduceAdd])))

private theorem HeapExtends_alloc {h : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {i : Nat} {o : Jvm.HeapObj AlgExt} (hget : h.get? i = some o) :
    (h.alloc obj).2.get? i = some o := by
  have hlt : i < h.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
  exact (jvmHeap_get?_alloc_lt h obj hlt).trans hget

private theorem decodeRLEWarning_alloc {h1 : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {v : JvmVal} {w : Algorithm.RLEWarning}
    (hdec : decodeRLEWarning h1 v = some w) : decodeRLEWarning (h1.alloc obj).2 v = some w := by
  cases v with
  | allocRef cls =>
    by_cases hc : cls = "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"
    · subst hc; simpa [decodeRLEWarning] using hdec
    · simp [decodeRLEWarning, hc] at hdec
  | heapRef a =>
    dsimp only [decodeRLEWarning] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some o =>
      rw [hg] at hdec
      rw [HeapExtends_alloc obj hg]
      exact hdec
  | _ => simp [decodeRLEWarning] at hdec

private theorem mapM_decodeRLEWarning_alloc {h1 : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {vs : List JvmVal} {ws : List Algorithm.RLEWarning}
    (hm : vs.mapM (decodeRLEWarning h1) = some ws) :
    vs.mapM (decodeRLEWarning (h1.alloc obj).2) = some ws := by
  induction vs generalizing ws with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [List.mapM_cons] at hm ⊢
    cases hdv : decodeRLEWarning h1 v with
    | none => simp [hdv] at hm
    | some w =>
      rw [decodeRLEWarning_alloc obj hdv]
      rw [hdv] at hm
      cases hrest : vs.mapM (decodeRLEWarning h1) with
      | none => simp [hrest] at hm
      | some ws' =>
        rw [hrest] at hm
        rw [ih hrest]
        exact hm

private theorem evalConcat_i32_str (n : UInt32) (s : String) :
    @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01" "(ILjava/lang/String;)Ljava/lang/String;"
      [.str s, .i32 n] = some (Jvm.i32ToDecimalString n ++ (s ++ ""), []) := rfl

private theorem evalConcat_str_i32 (a : String) (n : UInt32) :
    @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01" "(Ljava/lang/String;I)Ljava/lang/String;"
      [.i32 n, .str a] = some (a ++ (Jvm.i32ToDecimalString n ++ ""), []) := rfl

private theorem evalConcat_str_str_i32 (a b : String) (n : UInt32) :
    @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01\x01"
      "(Ljava/lang/String;Ljava/lang/String;I)Ljava/lang/String;"
      [.i32 n, .str b, .str a] = some (a ++ (b ++ (Jvm.i32ToDecimalString n ++ "")), []) := rfl

private theorem evalConcat_str_str (a b : String) :
    @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01"
      "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;"
      [.str b, .str a] = some (a ++ (b ++ ""), []) := rfl

private theorem runJvmValFast_invokedynamic_makeConcat {fuel : Nat}
    {prog rest : List JvmInstr} {pc : Nat}
    {recipe desc : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {res : String} {stkRest : List JvmVal}
    (heval : @Jvm.evalMakeConcatWithConstants AlgExt recipe desc stk = some (res, stkRest)) :
    runJvmValFast (fuel + 1) prog pc (.invokedynamic "makeConcatWithConstants" recipe desc :: rest)
        ⟨pc, stk, locs, jh, hp⟩ =
      runJvmValFast fuel prog (pc + 1) rest ⟨pc + 1, .str res :: stkRest, locs, jh, hp⟩ := by
  rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, Jvm.stepInstr, beq_self_eq_true, ↓reduceIte, heval]

private theorem runJvmResFast_invokedynamic_makeConcat {fuel : Nat}
    {prog rest : List JvmInstr} {pc : Nat}
    {recipe desc : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {res : String} {stkRest : List JvmVal}
    (heval : @Jvm.evalMakeConcatWithConstants AlgExt recipe desc stk = some (res, stkRest)) :
    runJvmResFast (fuel + 1) prog pc (.invokedynamic "makeConcatWithConstants" recipe desc :: rest)
        ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast fuel prog (pc + 1) rest ⟨pc + 1, .str res :: stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, Jvm.stepInstr, beq_self_eq_true, ↓reduceIte, heval]

private theorem setLocal_apply {Ext : Type} {locs : Nat → Jvm.JvmVal Ext} {idx i : Nat}
    {v : Jvm.JvmVal Ext} :
    setLocal locs idx v i = if (i == idx) = true then v else locs i := by
  simp [setLocal, Jvm.setLocal, beq_iff_eq]

open Lean Elab Tactic in
elab "step_res_plain " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]))
    evalTactic (← `(tactic| simp only [stepInstr, Jvm.stepInstr, setLocal_apply,
      Nat.reduceAdd, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]))

open Lean Elab Tactic in
elab "step_val_plain " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]))
    evalTactic (← `(tactic| simp only [stepInstr, Jvm.stepInstr, setLocal_apply,
      Nat.reduceAdd, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]))

/-! #### 1. `serializeRLE___closed__3` -/

theorem serializeRLE_closed3_equiv :
    ∃ v st', runJvmRes 80 f_Algorithm_serializeRLE___closed__3_prog (initJvmState []) =
        some (v, st') ∧
      decodeStrArray st' v = some #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"] := by
  let jh0 : Jvm.JvmHeap AlgExt := {}
  let h1 := (jh0.alloc (.objArray "java/lang/Object" #[])).2
  let h2 := ((h1.alloc (.objArray "java/lang/Object" #[.null])).2).set 1
    (.objArray "java/lang/Object" #[.str "#R 0 0"])
  let h3 := ((h2.alloc (.objArray "java/lang/Object" #[.str "#R 0 0", .null])).2).set 2
    (.objArray "java/lang/Object" #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23"])
  let h4 := ((h3.alloc (.objArray "java/lang/Object"
    #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .null])).2).set 3
    (.objArray "java/lang/Object"
      #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .str "!"])
  let locsOut : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (fun _ => .i32 0) 0 (.str "!")) 1 (.str "x = 0, y = 0, rule = B3/S23"))
      2 (.str "#R 0 0")) 3 (.heapRef 0)) 5 (.heapRef 1)) 6 (.heapRef 1)) 7 (.i32 0))
      4 (.heapRef 1)) 6 (.heapRef 2)) 7 (.heapRef 2)) 8 (.i32 0)) 5 (.heapRef 2))
      6 (.heapRef 3)) 7 (.heapRef 3)) 8 (.i32 0)
  refine ⟨.heapRef 3, ⟨71, [.heapRef 3], locsOut, h4, {}⟩, ?_, rfl⟩
  have hrep0 : Array.replicate (UInt32.toNat 0) (JvmVal.null : JvmVal) = #[] := rfl
  have hcp1 : Array.ofFn (n := (UInt32.ofNat (#[] : Array JvmVal).size + 1).toNat)
      (fun i => if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null) = #[.null] := by
    apply Array.ext
    · decide
    · intro i hi1 hi2
      have : i = 0 := by simp at hi1; omega
      subst this; rfl
  have hcp2 : Array.ofFn (n := (UInt32.ofNat #[(JvmVal.str "#R 0 0" : JvmVal)].size + 1).toNat)
      (fun i => if h : i.val < #[(JvmVal.str "#R 0 0" : JvmVal)].size then
        #[(JvmVal.str "#R 0 0" : JvmVal)][i.val] else (JvmVal.null : JvmVal)) =
      (#[.str "#R 0 0", .null] : Array JvmVal) := by
    apply Array.ext
    · decide
    · intro i hi1 hi2
      have hlt : i < 2 := by simpa using hi1
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h0 | rfl
      · have : i = 0 := by omega
        subst this; rfl
      · rfl
  have hcp3 : Array.ofFn
      (n := (UInt32.ofNat #[(JvmVal.str "#R 0 0" : JvmVal), .str "x = 0, y = 0, rule = B3/S23"].size + 1).toNat)
      (fun i => if h : i.val < #[(JvmVal.str "#R 0 0" : JvmVal), .str "x = 0, y = 0, rule = B3/S23"].size then
        #[(JvmVal.str "#R 0 0" : JvmVal), .str "x = 0, y = 0, rule = B3/S23"][i.val] else (JvmVal.null : JvmVal)) =
      (#[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .null] : Array JvmVal) := by
    apply Array.ext
    · decide
    · intro i hi1 hi2
      have hlt : i < 3 := by simpa using hi1
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h01 | rfl
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h01) with h0 | rfl
        · have : i = 0 := by omega
          subst this; rfl
        · rfl
      · rfl
  apply runJvmRes_of_runJvmResFast0 80 _ _ _ rfl
  dsimp only [f_Algorithm_serializeRLE___closed__3_prog, initJvmState, Jvm.initJvmState, List.foldl]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_anewarray_obj (by decide)]; norm_res_fuel
  rw [hrep0]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  rw [hcp1]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aastore rfl (by decide) (by decide)]; norm_res_fuel
  have hs1 : ∀ h, (#[(JvmVal.null : JvmVal)].set (UInt32.ofNat (#[] : Array JvmVal).size).toNat
      (JvmVal.str "#R 0 0") h : Array JvmVal) = #[.str "#R 0 0"] := fun _ => rfl
  rw [hs1]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  rw [hcp2]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aastore rfl (by decide) (by decide)]; norm_res_fuel
  have hs2 : ∀ h, (#[(JvmVal.str "#R 0 0" : JvmVal), .null].set
      (UInt32.ofNat #[(JvmVal.str "#R 0 0" : JvmVal)].size).toNat
      (.str "x = 0, y = 0, rule = B3/S23") h : Array JvmVal) =
      #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23"] := fun _ => rfl
  rw [hs2]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
  rw [hcp3]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aastore rfl (by decide) (by decide)]; norm_res_fuel
  have hs3 : ∀ h, (#[(JvmVal.str "#R 0 0" : JvmVal), .str "x = 0, y = 0, rule = B3/S23", .null].set
      (UInt32.ofNat #[(JvmVal.str "#R 0 0" : JvmVal), .str "x = 0, y = 0, rule = B3/S23"].size).toNat
      (.str "!") h : Array JvmVal) =
      #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .str "!"] := fun _ => rfl
  rw [hs3]
  heap_step_nonbranch_chunks
  rfl

/-! #### 2. `formatRLEItem` -/

private theorem u32_toString_eq_i32ToDecimalString {v : UInt32} (hv : v.toNat < 2 ^ 31) :
    Jvm.i32ToDecimalString v = toString v := by
  rw [i32ToDecimalString_eq_toString v]
  have hni : v.toInt32.toInt = ↑v.toNat := u32_toInt_eq_toNat hv
  change Int.repr v.toInt32.toInt = Nat.repr v.toNat
  rw [hni]
  rfl

theorem formatRLEItem_equiv (tag : UInt8) (count : UInt32) (hcount : count.toNat < 2 ^ 31) :
    runJvm 50 f_Algorithm_formatRLEItem_prog
        (initJvmState [(0, .i32 tag.toUInt32), (1, .i32 count)]) =
      some (.str (Algorithm.formatRLEItem tag count)) := by
  apply runJvm_of_runJvmValFast0 50 _ _ _ rfl
  let l0 : Nat → JvmVal := setLocal (setLocal (fun _ => .i32 0) 0 (.i32 tag.toUInt32)) 1 (.i32 count)
  let l1 : Nat → JvmVal := setLocal l0 2 .null
  let tagStr := if tag == 111 then "o" else if tag == 98 then "b" else if tag == 36 then "$" else "!"
  have h111_iff : tag.toUInt32 = 111 ↔ tag = 111 := by
    constructor <;> intro h
    · exact UInt8.eq_of_toBitVec_eq (by
        have := congrArg UInt32.toNat h
        simp [UInt32.toNat_ofNat] at this
        apply BitVec.eq_of_toNat_eq; exact this)
    · subst h; rfl
  have h98_iff : tag.toUInt32 = 98 ↔ tag = 98 := by
    constructor <;> intro h
    · exact UInt8.eq_of_toBitVec_eq (by
        have := congrArg UInt32.toNat h
        simp [UInt32.toNat_ofNat] at this
        apply BitVec.eq_of_toNat_eq; exact this)
    · subst h; rfl
  have h36_iff : tag.toUInt32 = 36 ↔ tag = 36 := by
    constructor <;> intro h
    · exact UInt8.eq_of_toBitVec_eq (by
        have := congrArg UInt32.toNat h
        simp [UInt32.toNat_ofNat] at this
        apply BitVec.eq_of_toNat_eq; exact this)
    · subst h; rfl
  have htagStr : runJvmValFast 50 f_Algorithm_formatRLEItem_prog 0 f_Algorithm_formatRLEItem_prog
      ⟨0, [], l0, {}, {}⟩ =
      runJvmValFast 30 f_Algorithm_formatRLEItem_prog 30
        (f_Algorithm_formatRLEItem_prog.drop 30) ⟨30, [], setLocal l1 2 (.str tagStr), {}, {}⟩ := by
    by_cases ht111 : tag = 111
    · have hu : tag.toUInt32 = 111 := h111_iff.mpr ht111
      have hts : tagStr = "o" := by subst ht111; rfl
      rw [hts]
      split_val_fuel 30
      dsimp only [f_Algorithm_formatRLEItem_prog]
      flat_step_blk f_Algorithm_formatRLEItem_prog
      simp only [hu, beq_self_eq_true, ↓reduceIte]
      flat_step_blk f_Algorithm_formatRLEItem_prog
      rfl
    · have hu111 : (tag.toUInt32 == 111) = false := beq_false_of_ne (fun h => ht111 (h111_iff.mp h))
      have hb111 : (tag == 111) = false := beq_false_of_ne ht111
      by_cases ht98 : tag = 98
      · have hu : tag.toUInt32 = 98 := h98_iff.mpr ht98
        have hts : tagStr = "b" := by subst ht98; rfl
        rw [hts]
        split_val_fuel 30
        dsimp only [f_Algorithm_formatRLEItem_prog]
        flat_step_blk f_Algorithm_formatRLEItem_prog
        simp only [hu111, Bool.false_eq_true, ↓reduceIte]
        flat_step_blk f_Algorithm_formatRLEItem_prog
        simp only [hu, beq_self_eq_true, ↓reduceIte]
        flat_step_blk f_Algorithm_formatRLEItem_prog
        rfl
      · have hu98 : (tag.toUInt32 == 98) = false := beq_false_of_ne (fun h => ht98 (h98_iff.mp h))
        have hb98 : (tag == 98) = false := beq_false_of_ne ht98
        by_cases ht36 : tag = 36
        · have hu : tag.toUInt32 = 36 := h36_iff.mpr ht36
          have hts : tagStr = "$" := by subst ht36; rfl
          rw [hts]
          split_val_fuel 30
          dsimp only [f_Algorithm_formatRLEItem_prog]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu111, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu98, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu, beq_self_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          rfl
        · have hu36 : (tag.toUInt32 == 36) = false := beq_false_of_ne (fun h => ht36 (h36_iff.mp h))
          have hb36 : (tag == 36) = false := beq_false_of_ne ht36
          have hts : tagStr = "!" := by
            simp only [tagStr, hb111, hb98, hb36, Bool.false_eq_true, ↓reduceIte]
          rw [hts]
          split_val_fuel 30
          dsimp only [f_Algorithm_formatRLEItem_prog]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu111, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu98, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          simp only [hu36, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_formatRLEItem_prog
          rfl
  change runJvmValFast 50 f_Algorithm_formatRLEItem_prog 0 f_Algorithm_formatRLEItem_prog
      ⟨0, [], l0, {}, {}⟩ = _
  rw [htagStr]
  have heval30 : runJvmValFast 30 f_Algorithm_formatRLEItem_prog 30
      (f_Algorithm_formatRLEItem_prog.drop 30) ⟨30, [], setLocal l1 2 (.str tagStr), {}, {}⟩ =
      some (.str (if count == 1 then tagStr else Jvm.i32ToDecimalString count ++ (tagStr ++ ""))) := by
    by_cases hc1 : count = 1
    · subst hc1
      dsimp only [f_Algorithm_formatRLEItem_prog, List.drop]
      flat_step_blk f_Algorithm_formatRLEItem_prog
      simp only [beq_self_eq_true, ↓reduceIte]
      flat_step_blk f_Algorithm_formatRLEItem_prog
    · have hcn : (count == 1) = false := beq_false_of_ne hc1
      dsimp only [f_Algorithm_formatRLEItem_prog, List.drop]
      flat_step_blk f_Algorithm_formatRLEItem_prog
      simp only [hcn, Bool.false_eq_true, ↓reduceIte]
      step_val_plain 2
      have hl1 : l1 1 = .i32 count := rfl
      rw [hl1]
      rw [runJvmValFast_invokedynamic_makeConcat (evalConcat_i32_str count tagStr)]
      flat_step_blk f_Algorithm_formatRLEItem_prog
  rw [heval30]
  rw [u32_toString_eq_i32ToDecimalString hcount]
  unfold Algorithm.formatRLEItem
  change some (JvmVal.str (if count == 1 then tagStr else toString count ++ (tagStr ++ ""))) =
    some (JvmVal.str (if count == 1 then
      (if tag == rleAlive then "o" else if tag == rleDead then "b" else if tag == rleRowEnd then "$" else "!")
    else
      s!"{count}{if tag == rleAlive then "o" else if tag == rleDead then "b"
        else if tag == rleRowEnd then "$" else "!"}"))
  simp only [String.append_empty]
  rfl

/-! #### 3. `formatRLEHeader` -/

theorem formatRLEHeader_equiv (minX minY : Int32) (width height : UInt32)
    (hw : width.toNat < 2 ^ 31) (hh : height.toNat < 2 ^ 31) :
    ∃ v st', runJvmRes 85 f_Algorithm_formatRLEHeader_prog
        (initJvmState [(0, .i32 minX.toUInt32), (1, .i32 minY.toUInt32),
          (2, .i32 width), (3, .i32 height)]) = some (v, st') ∧
      decodeStrArray st' v = some (Algorithm.formatRLEHeader minX minY width height) := by
  let l0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
    0 (.i32 minX.toUInt32)) 1 (.i32 minY.toUInt32)) 2 (.i32 width)) 3 (.i32 height)
  let s1 := "#R " ++ (Jvm.i32ToDecimalString minX.toUInt32 ++ "")
  let s2 := s1 ++ (" " ++ (Jvm.i32ToDecimalString minY.toUInt32 ++ ""))
  let s3 := "x = " ++ (Jvm.i32ToDecimalString width ++ "")
  let s4 := s3 ++ (", y = " ++ (Jvm.i32ToDecimalString height ++ ""))
  let s5 := s4 ++ (", rule = B3/S23" ++ "")
  let jh0 : Jvm.JvmHeap AlgExt := {}
  let h1 := (jh0.alloc (.objArray "java/lang/Object" #[])).2
  let a1 := h1.objects.size
  let jh2 := (h1.alloc (.objArray "java/lang/Object" #[.null])).2
  let h2 := jh2.set a1 (.objArray "java/lang/Object" #[.str s2])
  let a2 := h2.objects.size
  let jh3 := (h2.alloc (.objArray "java/lang/Object" #[.str s2, .null])).2
  let h3 := jh3.set a2 (.objArray "java/lang/Object" #[.str s2, .str s5])
  have hg1 : h1.get? jh0.objects.size = some (.objArray "java/lang/Object" #[]) :=
    jvmHeap_get?_alloc_self jh0 _
  have hg2 : h2.get? a1 = some (.objArray "java/lang/Object" #[.str s2]) := by
    simp [h2, jh2, Jvm.JvmHeap.set, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, a1]
  have hg3 : h3.get? a2 = some (.objArray "java/lang/Object" #[.str s2, .str s5]) := by
    simp [h3, jh3, Jvm.JvmHeap.set, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, a2]
  have hs2 : s2 = s!"#R {minX} {minY}" := by
    simp only [s2, s1, i32ToDecimalString_eq_toString minX.toUInt32,
      i32ToDecimalString_eq_toString minY.toUInt32, Int32.toInt32_toUInt32,
      String.append_empty, String.append_assoc]
    rfl
  have hs5 : s5 = s!"x = {width}, y = {height}, rule = B3/S23" := by
    simp only [s5, s4, s3, u32_toString_eq_i32ToDecimalString hw, u32_toString_eq_i32ToDecimalString hh,
      String.append_empty, String.append_assoc]
    rfl
  let stOut : JvmState := ⟨76, [.heapRef a2],
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        l0 4 (.str "#R ")) 5 (.str s1))
          6 (.str " ")) 7 (.str s2)) 8 (.str "x = ")) 9 (.str s3)) 10 (.str ", y = "))
          11 (.str s4)) 12 (.str ", rule = B3/S23")) 13 (.str s5)) 14 (.heapRef 0))
          16 (.heapRef a1)) 17 (.heapRef a1)) 18 (.i32 0)) 15 (.heapRef a1))
          16 (.heapRef a2)) 17 (.heapRef a2)) 18 (.i32 0),
    h3, {}⟩
  have hdec : decodeStrArray stOut (.heapRef a2) =
      some (Algorithm.formatRLEHeader minX minY width height) := by
    simp [stOut, decodeStrArray, hg3, hs2, hs5, Algorithm.formatRLEHeader]
  refine ⟨.heapRef a2, stOut, ?_, hdec⟩
  have hrun : runJvmRes 85 f_Algorithm_formatRLEHeader_prog
      (initJvmState [(0, .i32 minX.toUInt32), (1, .i32 minY.toUInt32),
        (2, .i32 width), (3, .i32 height)]) =
      some (.heapRef a2, stOut) := by
    apply runJvmRes_of_runJvmResFast0 85 _ _ _ rfl
    dsimp only [f_Algorithm_formatRLEHeader_prog, initJvmState, Jvm.initJvmState, List.foldl]
    step_res_plain 4
    rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_i32 "#R " minX.toUInt32)]
    step_res_plain 6
    rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_str_i32 s1 " " minY.toUInt32)]
    step_res_plain 5
    rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_i32 "x = " width)]
    step_res_plain 6
    rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_str_i32 s3 ", y = " height)]
    step_res_plain 5
    rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_str s4 ", rule = B3/S23")]
    simp only [Nat.reduceAdd]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (by decide)]; norm_res_fuel
    have hrep0 : Array.replicate (UInt32.toNat 0) (JvmVal.null : JvmVal) = #[] := rfl
    rw [hrep0]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj rfl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
    have hcopy1 : Array.ofFn (n := (UInt32.ofNat (#[] : Array JvmVal).size + 1).toNat)
        (fun i => if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null) =
        #[.null] := by
      apply Array.ext
      · decide
      · intro i hi1 hi2
        have : i = 0 := by simp at hi1; omega
        subst this; rfl
    rw [hcopy1]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore rfl (by decide) (by decide)]; norm_res_fuel
    have hset1 : ∀ h, (#[(JvmVal.null : JvmVal)].set (UInt32.ofNat (#[] : Array JvmVal).size).toNat
        (.str s2) h : Array JvmVal) = #[.str s2] := fun _ => rfl
    rw [hset1]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj rfl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj rfl]; norm_res_fuel
    have hcopy2 : Array.ofFn (n := (UInt32.ofNat #[(JvmVal.str s2 : JvmVal)].size + 1).toNat)
        (fun i => if h : i.val < #[(JvmVal.str s2 : JvmVal)].size then
          #[(JvmVal.str s2 : JvmVal)][i.val] else (JvmVal.null : JvmVal)) =
        (#[.str s2, .null] : Array JvmVal) := by
      apply Array.ext
      · rfl
      · intro i hi1 hi2
        have hlt2 : i < 2 := by simpa using hi1
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt2) with h0 | rfl
        · have : i = 0 := by omega
          subst this; rfl
        · rfl
    rw [hcopy2]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (cls := "java/lang/Object") (elems := #[.str s2, .null])
      rfl rfl (by simp)]; norm_res_fuel
    have hset2 : ∀ h, (#[(JvmVal.str s2 : JvmVal), .null].set
        (UInt32.ofNat #[(JvmVal.str s2 : JvmVal)].size).toNat (.str s5) h : Array JvmVal) =
        #[.str s2, .str s5] := fun _ => rfl
    rw [hset2]
    heap_step_nonbranch_chunks
    rfl
  exact hrun

/-! ### Part 2 helpers: Pair, UByte, UInt, GrowBuf (String & U8×U32) -/

private theorem stepStatic_growBufPush_str
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .str s :: .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf (b.push s)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_wrapRLEItems_closed0_6c
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_wrapRLEItems___closed__0" "()Lkotlin/Pair;" =
      .inl (some ⟨pc + 1, .pair (.boxedUByte 0) (.boxedUInt 0) :: rest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_instanceof_pair {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {a b : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 1 :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_instanceof_step rfl

private theorem runJvmResFast_checkcast_pair {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {a b : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_checkcast_step rfl

private theorem runJvmResFast_instanceof_boxedUByte_byte {f : Nat} {prog : List JvmInstr}
    {pc : Nat} {rest : List JvmInstr} {pc0 : Nat} {v : UInt32}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "java/lang/Byte" :: rest)
        ⟨pc0, .boxedUByte v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_instanceof_step rfl

private theorem runJvmResFast_checkcast_boxedUByte {f : Nat} {prog : List JvmInstr}
    {pc : Nat} {rest : List JvmInstr} {pc0 : Nat} {v : UInt32}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/UByte" :: rest)
        ⟨pc0, .boxedUByte v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .boxedUByte v :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_checkcast_step rfl

private theorem stepVirtual_ubyte_unbox
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedUByte v :: rest, locs, jh, hp⟩
      "kotlin/UByte" "unbox-impl" "()B" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

private theorem stepVirtual_uint_unbox
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

private theorem u8_toUInt32_toUInt8 (b : UInt8) : b.toUInt32.toUInt8 = b := by
  apply UInt8.eq_of_toBitVec_eq
  rw [UInt32.toUInt8, UInt8.toUInt32]
  simp

private theorem stepStatic_formatRLEItem
    {pc : Nat} {tag : UInt8} {count : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 count :: .i32 tag.toUInt32 :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_formatRLEItem-g_SBl1M" "(BI)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.formatRLEItem tag count) :: rest,
        locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 count :: .i32 tag.toUInt32 :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_formatRLEItem-g_SBl1M" "(BI)Ljava/lang/String;" =
      .inl (some ⟨pc + 1,
        .str (Algorithm.formatRLEItem tag.toUInt32.toUInt8 count) :: rest,
        locs, jh, hp⟩) := rfl
  rw [hfn, u8_toUInt32_toUInt8]

private theorem stepStatic_formatRLEItemLength
    {pc : Nat} {count : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 count :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_formatRLEItemLength-WZ4Q5Ns" "(I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.formatRLEItemLength count) :: rest,
        locs, jh, hp⟩) := rfl

private structure RleItemArrRep6c (items : Array (UInt8 × UInt32)) (elems : Array JvmVal) : Prop where
  size_eq : elems.size = items.size
  elem_eq : ∀ k (hk : k < items.size),
    elems[k]'(size_eq.symm ▸ hk) =
      .pair (.boxedUByte (items[k]'hk).1.toUInt32) (.boxedUInt (items[k]'hk).2)

private inductive U8U32PairRep6c : Algorithm.GrowBuf (UInt8 × UInt32) → JvmVal → Prop
  | empty (d : Algorithm.GrowBuf String) (he : d.data.isEmpty = true) (hz : d.size = 0) :
      U8U32PairRep6c Algorithm.GrowBuf.empty (.ext (.strGrowBuf d))
  | full (b : Algorithm.GrowBuf (UInt8 × UInt32)) :
      U8U32PairRep6c b (.ext (.u8U32PairGrowBuf b))

private theorem growBuf_eq_empty_of6c {α : Type} {b : Algorithm.GrowBuf α}
    (he : b.data.isEmpty = true) (hz : b.size = 0) : b = Algorithm.GrowBuf.empty := by
  have hd : b.data = #[] := Array.isEmpty_iff.mp he
  rcases b with ⟨d, s⟩
  dsimp only at hd hz
  subst hd hz
  rfl

private theorem stepStatic_growBufPush_u8u32
    {pc : Nat} {tag : UInt8} {len : UInt32} {bufVal : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf (UInt8 × UInt32)}
    (hrep : U8U32PairRep6c b bufVal) :
    stepInvokeStatic ⟨pc, .pair (.boxedUByte tag.toUInt32) (.boxedUInt len) :: bufVal :: rest,
        locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.u8U32PairGrowBuf (b.push (tag, len))) :: rest,
        locs, jh, hp⟩) := by
  cases hrep with
  | empty d he hz =>
    have hfn : stepInvokeStatic
        ⟨pc, .pair (.boxedUByte tag.toUInt32) (.boxedUInt len) ::
          .ext (.strGrowBuf d) :: rest, locs, jh, hp⟩
        "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
        (if (d.data.isEmpty && d.size == 0) = true then
          .inl (some ⟨pc + 1,
            .ext (.u8U32PairGrowBuf (Algorithm.GrowBuf.empty.push (tag.toUInt32.toUInt8, len))) :: rest,
            locs, jh, hp⟩)
        else .inr none) := rfl
    rw [hfn]
    simp [he, hz]
  | full b =>
    have hfn : stepInvokeStatic
        ⟨pc, .pair (.boxedUByte tag.toUInt32) (.boxedUInt len) ::
          .ext (.u8U32PairGrowBuf b) :: rest, locs, jh, hp⟩
        "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
        .inl (some ⟨pc + 1,
          .ext (.u8U32PairGrowBuf (b.push (tag.toUInt32.toUInt8, len))) :: rest,
          locs, jh, hp⟩) := rfl
    rw [hfn, u8_toUInt32_toUInt8]

private theorem u8Sext_eq_toUInt32_of_lt128 (b : UInt8) (hb : b < 128) :
    UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) = b.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq
  rw [UInt8.toUInt32]
  change BitVec.signExtend 32 b.toBitVec = BitVec.zeroExtend 32 b.toBitVec
  apply BitVec.signExtend_eq_setWidth_of_msb_false
  rw [BitVec.msb_eq_toNat]
  have hlt : b.toNat < 128 := UInt8.lt_iff_toNat_lt.mp hb
  have hbv : b.toBitVec.toNat = b.toNat := rfl
  decide +revert

/-! ### wrapRLEItems equivalence -/

private theorem stepStatic_compareUnsigned_i32
    {pc : Nat} {b a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_uintCtor6c
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_checkNotNull6c
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_checkNotNullParam6c
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem compareUnsigned_slt_false_of_not_lt (a b : UInt32) (h : ¬(a < b)) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = false := by
  by_cases heq : a == b
  · simp [heq]
  · simp [heq, h]

private theorem compareUnsigned_slt_true_of_lt (a b : UInt32) (h : a < b) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = true := by
  have hne : (a == b) = false :=
    beq_false_of_ne (fun heq => by subst heq; exact Nat.lt_irrefl a.toNat (UInt32.lt_iff_toNat_lt.mp h))
  simp [hne, h]

private theorem runJvmResFast_areturn6c {f pc : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  dsimp only [runJvmResFast]
  rw [Jvm.runJvmResFast.eq_def]
  simp [Jvm.stepInstr]

private theorem wrapRLEItems_base
    (numItems j lineLen : UInt32) (line : String) (out : Algorithm.GrowBuf String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hj : ¬(j < numItems))
    (hl1 : locs 1 = .i32 numItems) (hl2 : locs 2 = .i32 j)
    (hl3 : locs 3 = .str line) (hl4 : locs 4 = .i32 lineLen) (hl5 : locs 5 = .ext (.strGrowBuf out)) :
    ∃ fuel st',
      runJvmResFast fuel f_Algorithm_wrapRLEItems_prog 6
        (f_Algorithm_wrapRLEItems_prog.drop 6) ⟨6, [], locs, jh, hp⟩ = some st' ∧
      st'.1 = .ext (.strGrowBuf (if (lineLen != 0) = true then out.push line else out)) ∧
      st'.2.jvmHeap = jh ∧ st'.2.heap = hp := by
  by_cases hll : lineLen = 0
  · subst hll
    refine ⟨10, ⟨.ext (.strGrowBuf out), ⟨17, [.ext (.strGrowBuf out)], locs, jh, hp⟩⟩,
      ?_, by simp, rfl, rfl⟩
    step_drop6c 6
    step_res_plain 2; rw [hl2, hl1]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
    rw [runJvmResFast_iflt_fallthrough (compareUnsigned_slt_false_of_not_lt j numItems hj)]
    step_drop6c 2
    step_res_plain 1; rw [hl4]
    rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 2
    step_res_plain 1; rw [hl5]
    exact runJvmResFast_areturn6c
  · refine ⟨11, ⟨.ext (.strGrowBuf (out.push line)),
        ⟨15, [.ext (.strGrowBuf (out.push line))], locs, jh, hp⟩⟩,
      ?_, ?_, rfl, rfl⟩
    · step_drop6c 6
      step_res_plain 2; rw [hl2, hl1]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
      rw [runJvmResFast_iflt_fallthrough (compareUnsigned_slt_false_of_not_lt j numItems hj)]
      step_drop6c 2
      step_res_plain 1; rw [hl4]
      have hne : (lineLen == 0) = false := beq_false_of_ne hll
      rw [runJvmResFast_ifeq_fallthrough hne]
      step_drop6c 4
      step_res_plain 2; rw [hl5, hl3]
      rw [runJvmResFast_invokestatic_step stepStatic_growBufPush_str]
      exact runJvmResFast_areturn6c
    · have hne : (lineLen != 0) = true := by simp [hll]
      simp [hne]

private theorem wrapRLEItems_loop
    (n : Nat)
    (items : Array (UInt8 × UInt32)) (numItems j : UInt32) (line : String) (lineLen : UInt32)
    (out : Algorithm.GrowBuf String) (itemsAddr : Nat) (elems : Array JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hrep : RleItemArrRep6c items elems)
    (hget : jh.get? itemsAddr = some (.objArray "java/lang/Object" elems))
    (hnum : numItems.toNat ≤ items.size) (hnum31 : numItems.toNat < 2 ^ 31)
    (hn : numItems.toNat - j.toNat ≤ n)
    (hl0 : locs 0 = .heapRef itemsAddr) (hl1 : locs 1 = .i32 numItems)
    (hl2 : locs 2 = .i32 j) (hl3 : locs 3 = .str line)
    (hl4 : locs 4 = .i32 lineLen) (hl5 : locs 5 = .ext (.strGrowBuf out)) :
    ∃ fuel st',
      runJvmResFast fuel f_Algorithm_wrapRLEItems_prog 6
        (f_Algorithm_wrapRLEItems_prog.drop 6) ⟨6, [], locs, jh, hp⟩ = some st' ∧
      st'.1 = .ext (.strGrowBuf (Algorithm.wrapRLEItems items numItems j line lineLen out)) ∧
      st'.2.jvmHeap = jh ∧ st'.2.heap = hp := by
  induction n generalizing j line lineLen out locs with
  | zero =>
    have hj_ge : ¬(j < numItems) := fun h => by
      have := UInt32.lt_iff_toNat_lt.mp h
      omega
    rw [Algorithm.wrapRLEItems.eq_1]
    simp only [hj_ge, ↓reduceDIte]
    exact wrapRLEItems_base numItems j lineLen line out jh hp locs hj_ge hl1 hl2 hl3 hl4 hl5
  | succ n ih =>
    by_cases hj : j < numItems
    · rw [Algorithm.wrapRLEItems.eq_1]
      simp only [hj, ↓reduceDIte]
      have hj_lt_nat : j.toNat < numItems.toNat := hj
      have hj_elems : j.toNat < elems.size := by have := hrep.size_eq; omega
      have hj_items : j.toNat < items.size := by omega
      have hslt_j := u32_slt_zero_of_lt hj (by omega)
      have hcomp_t := compareUnsigned_slt_true_of_lt j numItems hj
      have helem : elems[j.toNat]'hj_elems =
          .pair (.boxedUByte (items[j.toNat]'hj_items).1.toUInt32)
            (.boxedUInt (items[j.toNat]'hj_items).2) := by
        simpa using hrep.elem_eq j.toNat hj_items
      have hidx_eq : items[j.toNat]! = items[j.toNat]'hj_items := by simp [hj_items]
      let item := items[j.toNat]'hj_items
      let text := Algorithm.formatRLEItem item.1 item.2
      let len := Algorithm.formatRLEItemLength item.2
      have hj1 := ui32_add1_toNat hj
      have hdec_n : numItems.toNat - (j + 1).toNat ≤ n := by omega
      let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal locs
        6 (.pair (.boxedUByte 0) (.boxedUInt 0)))
        7 (.pair (.boxedUByte item.1.toUInt32) (.boxedUInt item.2)))
        8 (.boxedUInt item.2)) 10 (.boxedUByte item.1.toUInt32)) 11 (.i32 0))
        9 (.i32 item.1.toUInt32)) 11 (.boxedUInt item.2)) 12 (.i32 0))
        10 (.i32 item.2)) 11 (.str text)) 13 (.boxedUInt item.2)) 14 (.i32 0))
        12 (.i32 item.2)) 13 (.i32 len)) 14 (.i32 (lineLen + len))
      have hpre : ∀ (fuelR : Nat),
          runJvmResFast (fuelR + 81) f_Algorithm_wrapRLEItems_prog 6
            (f_Algorithm_wrapRLEItems_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          runJvmResFast fuelR f_Algorithm_wrapRLEItems_prog 121
            (f_Algorithm_wrapRLEItems_prog.drop 121)
            ⟨121, [.i32 (if (70 : UInt32) == lineLen + len then 0
              else if (70 : UInt32) < lineLen + len then 4294967295 else 1)],
              locsMid, jh, hp⟩ := by
        intro fuelR
        step_drop6c 6
        step_res_plain 2; rw [hl2, hl1]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
        rw [runJvmResFast_iflt_branch hcomp_t]
        step_drop6c 9
        rw [runJvmResFast_invokestatic_step stepStatic_wrapRLEItems_closed0_6c]
        step_res_plain 3; rw [hl0, hl2]
        rw [runJvmResFast_aaload hget hslt_j hj_elems, helem]
        step_res_plain 2
        rw [runJvmResFast_instanceof_pair]
        rw [runJvmResFast_ifeq_fallthrough (by decide)]
        step_drop6c 4
        step_res_plain 1
        rw [runJvmResFast_checkcast_pair]
        rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
        rw [runJvmResFast_goto]; step_drop6c 8
        step_res_plain 2
        rw [runJvmResFast_instanceof_pair]
        rw [runJvmResFast_ifeq_fallthrough (by decide)]
        step_res_plain 1
        rw [runJvmResFast_checkcast_pair]
        rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
        rw [runJvmResFast_goto]; step_drop6c 6
        step_res_plain 4
        rw [runJvmResFast_instanceof_boxedUByte_byte]
        rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 14
        step_res_plain 2
        rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull6c rfl)]
        step_res_plain 1
        rw [runJvmResFast_checkcast_boxedUByte]
        rw [runJvmResFast_invokevirtual_step stepVirtual_ubyte_unbox]
        step_res_plain 6
        rw [runJvmResFast_instanceof_boxedUInt_int]
        rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 18
        step_res_plain 2
        rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull6c rfl)]
        step_res_plain 1
        rw [runJvmResFast_checkcast_boxedUInt]
        · rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
          step_res_plain 3
          rw [runJvmResFast_invokestatic_step stepStatic_formatRLEItem]
          step_res_plain 6
          rw [runJvmResFast_instanceof_boxedUInt_int]
          rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 18
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull6c rfl)]
          step_res_plain 1
          rw [runJvmResFast_checkcast_boxedUInt]
          · rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
            step_res_plain 2
            rw [runJvmResFast_invokestatic_step stepStatic_formatRLEItemLength]
            step_res_plain 2; rw [hl4]
            step_res_plain 2
            rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
            step_res_plain 3
            rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
            rfl
          · left; rfl
        · left; rfl
      by_cases hwrap : lineLen + len > 70
      · have hiflt := compareUnsigned_slt_true_of_lt 70 (lineLen + len) hwrap
        let locsNext := setLocal (setLocal (setLocal (setLocal locsMid
          15 (.i32 (j + 1))) 16 (.ext (.strGrowBuf (out.push line))))
          17 (.heapRef itemsAddr)) 18 (.i32 numItems)
        let locsLoop := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locsNext
          0 (.heapRef itemsAddr)) 1 (.i32 numItems)) 2 (.i32 (j + 1)))
          3 (.str text)) 4 (.i32 len)) 5 (.ext (.strGrowBuf (out.push line)))
        have hrec := ih (j + 1) text len (out.push line) locsLoop hdec_n
          rfl rfl rfl rfl rfl rfl
        rcases hrec with ⟨fuel', st', hrun', hres', hjh', hhp'⟩
        refine ⟨fuel' + 108, st', ?_, ?_, hjh', hhp'⟩
        · rw [hpre (fuel' + 27)]
          step_drop6c 1
          rw [runJvmResFast_iflt_branch hiflt]
          step_drop6c 26
          step_res_plain 1; rw [show locsMid 2 = .i32 j by simp [locsMid, setLocal_apply, hl2]]
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 3
          rw [show locsMid 5 = .ext (.strGrowBuf out) by simp [locsMid, setLocal_apply, hl5]]
          rw [show locsMid 3 = .str line by simp [locsMid, setLocal_apply, hl3]]
          rw [runJvmResFast_invokestatic_step stepStatic_growBufPush_str]
          step_res_plain 2
          rw [show locsMid 0 = .heapRef itemsAddr by simp [locsMid, setLocal_apply, hl0]]
          step_res_plain 2
          rw [show locsMid 1 = .i32 numItems by simp [locsMid, setLocal_apply, hl1]]
          step_res_plain 8
          rw [show locsMid 11 = .str text by simp [locsMid, setLocal_apply]]
          step_res_plain 2
          rw [show locsMid 13 = .i32 len by simp [locsMid, setLocal_apply]]
          step_res_plain 3
          rw [runJvmResFast_goto]
          change runJvmResFast fuel' f_Algorithm_wrapRLEItems_prog 6
              (f_Algorithm_wrapRLEItems_prog.drop 6)
              ⟨6, [], locsLoop, jh, hp⟩ = some st' at hrun'
          simpa [locsLoop, locsNext, setLocal_apply, Jvm.JvmVal.asI32] using hrun'
        · simpa [hidx_eq, hwrap, text, len, item] using hres'
      · have hiflt := compareUnsigned_slt_false_of_not_lt 70 (lineLen + len) hwrap
        let locsNext := setLocal (setLocal (setLocal (setLocal (setLocal locsMid
          15 (.heapRef itemsAddr)) 16 (.i32 numItems)) 17 (.i32 (j + 1)))
          18 (.str (line ++ text))) 19 (.ext (.strGrowBuf out))
        let locsLoop := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locsNext
          0 (.heapRef itemsAddr)) 1 (.i32 numItems)) 2 (.i32 (j + 1)))
          3 (.str (line ++ text))) 4 (.i32 (lineLen + len))) 5 (.ext (.strGrowBuf out))
        have hrec := ih (j + 1) (line ++ text) (lineLen + len) out locsLoop hdec_n
          rfl rfl rfl rfl rfl rfl
        rcases hrec with ⟨fuel', st', hrun', hres', hjh', hhp'⟩
        refine ⟨fuel' + 110, st', ?_, ?_, hjh', hhp'⟩
        · rw [hpre (fuel' + 29)]
          step_drop6c 1
          rw [runJvmResFast_iflt_fallthrough hiflt]
          step_drop6c 28
          step_res_plain 1; rw [show locsMid 0 = .heapRef itemsAddr by simp [locsMid, setLocal_apply, hl0]]
          step_res_plain 2; rw [show locsMid 1 = .i32 numItems by simp [locsMid, setLocal_apply, hl1]]
          step_res_plain 2; rw [show locsMid 2 = .i32 j by simp [locsMid, setLocal_apply, hl2]]
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 2; rw [show locsMid 3 = .str line by simp [locsMid, setLocal_apply, hl3]]
          step_res_plain 1; rw [show locsMid 11 = .str text by simp [locsMid, setLocal_apply]]
          rw [runJvmResFast_invokedynamic_makeConcat (evalConcat_str_str _ _)]
          step_res_plain 2; rw [show locsMid 5 = .ext (.strGrowBuf out) by simp [locsMid, setLocal_apply, hl5]]
          step_res_plain 9
          step_res_plain 1
          rw [show locsMid 14 = .i32 (lineLen + len) by simp [locsMid, setLocal_apply]]
          step_res_plain 3
          rw [runJvmResFast_goto]
          change runJvmResFast fuel' f_Algorithm_wrapRLEItems_prog 6
              (f_Algorithm_wrapRLEItems_prog.drop 6)
              ⟨6, [], locsLoop, jh, hp⟩ = some st' at hrun'
          simpa [locsLoop, locsNext, setLocal_apply, Jvm.JvmVal.asI32] using hrun'
        · simpa [hidx_eq, hwrap, text, len, item] using hres'
    · rw [Algorithm.wrapRLEItems.eq_1]
      simp only [hj, ↓reduceDIte]
      exact wrapRLEItems_base numItems j lineLen line out jh hp locs hj hl1 hl2 hl3 hl4 hl5

theorem wrapRLEItems_equiv
    (items : Array (UInt8 × UInt32)) (numItems j : UInt32) (line : String) (lineLen : UInt32)
    (out : Algorithm.GrowBuf String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hnum : numItems.toNat ≤ items.size) (hnum31 : numItems.toNat < 2 ^ 31) :
    let elems := items.map fun p => .pair (.boxedUByte p.1.toUInt32) (.boxedUInt p.2)
    let itemsAddr := (jh.alloc (.objArray "java/lang/Object" elems)).1
    let jh0 := (jh.alloc (.objArray "java/lang/Object" elems)).2
    let initSt := { initJvmState
      [(0, Jvm.JvmVal.heapRef itemsAddr), (1, Jvm.JvmVal.i32 numItems), (2, Jvm.JvmVal.i32 j),
       (3, Jvm.JvmVal.str line), (4, Jvm.JvmVal.i32 lineLen),
       (5, Jvm.JvmVal.ext (AlgExt.strGrowBuf out))]
      with jvmHeap := jh0, heap := hp }
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_wrapRLEItems_prog initSt = some st' ∧
      st'.1 = .ext (.strGrowBuf (Algorithm.wrapRLEItems items numItems j line lineLen out)) ∧
      st'.2.jvmHeap = jh0 ∧ st'.2.heap = hp := by
  intro elems itemsAddr jh0 initSt
  have hrep : RleItemArrRep6c items elems := by
    refine ⟨Array.size_map, ?_⟩
    intro k hk
    simp [elems]
  have hget : jh0.get? itemsAddr = some (.objArray "java/lang/Object" elems) :=
    jvmHeap_get?_alloc_self _ _
  have hloop := wrapRLEItems_loop (numItems.toNat - j.toNat) items numItems j line lineLen out
    itemsAddr elems jh0 hp initSt.locals hrep hget hnum hnum31 (Nat.le_refl _)
    rfl rfl rfl rfl rfl rfl
  rcases hloop with ⟨fuel, st', hrun, hres, hjh, hhp⟩
  refine ⟨fuel + 6, st', ?_, hres, hjh, hhp⟩
  apply runJvmRes_of_runJvmResFast0
  dsimp only [initSt, initJvmState, Jvm.initJvmState]
  change runJvmResFast (fuel + 6) f_Algorithm_wrapRLEItems_prog 0
      (f_Algorithm_wrapRLEItems_prog.drop 0) ⟨0, [], initSt.locals, jh0, hp⟩ = some st'
  step_drop6c 6
  step_res_plain 2
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam6c
    (by simp [initSt, initJvmState, Jvm.initJvmState, Jvm.JvmVal.isNull, setLocal_apply]))]
  step_res_plain 2
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam6c
    (by simp [initSt, initJvmState, Jvm.initJvmState, Jvm.JvmVal.isNull, setLocal_apply]))]
  exact hrun

/-! ### gridItems equivalence -/

private theorem stepStatic_ubyteCtor6c
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩
      "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_ubyteBox6c
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: rest, locs, jh, hp⟩
      "kotlin/UByte" "box-impl" "(B)Lkotlin/UByte;" =
      .inl (some ⟨pc + 1, .boxedUByte v :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_uintBox6c
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1, .boxedUInt v :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_remainderUnsigned6c
    {pc : Nat} {b a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hb : b ≠ 0) :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "remainderUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (a % b) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "remainderUnsigned" "(II)I" =
      if (b == 0) = true then .inr none
      else .inl (some ⟨pc + 1, .i32 (a % b) :: rest, locs, jh, hp⟩) := rfl
  rw [hfn]
  have hne : (b == 0) = false := beq_false_of_ne hb
  simp [hne]

private theorem stepSpecial_pairInit6c
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial
        ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest, locs, jh, hp⟩
      "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, .pair a b :: rest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_newClass_pair6c
    {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.newClass "kotlin/Pair" :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .allocRef "kotlin/Pair" :: stk, locs, jh, hp⟩ := by
  dsimp only [runJvmResFast]
  rw [Jvm.runJvmResFast.eq_def]
  simp [Jvm.stepInstr]

private theorem u8_toUInt32_beq6c (a b : UInt8) :
    (a.toUInt32 == b.toUInt32) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : a.toUInt32 ≠ b.toUInt32 := fun heq => h (by
      have := congrArg UInt32.toUInt8 heq
      simpa [u8_toUInt32_toUInt8] using this)
    rw [beq_false_of_ne hne, beq_false_of_ne h]

private theorem gridItems_base
    (total k : UInt32) (items : Algorithm.GrowBuf (UInt8 × UInt32)) (itemsVal : JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hk : ¬(k < total)) (hrep : U8U32PairRep6c items itemsVal)
    (hl2 : locs 2 = .i32 total) (hl3 : locs 3 = .i32 k) (hl7 : locs 7 = itemsVal) :
    ∃ fuel st',
      runJvmResFast fuel f_Algorithm_gridItems_prog 3
        (f_Algorithm_gridItems_prog.drop 3) ⟨3, [], locs, jh, hp⟩ = some st' ∧
      ∃ rVal, st'.1 = rVal ∧ U8U32PairRep6c items rVal ∧
      st'.2.jvmHeap = jh ∧ st'.2.heap = hp := by
  refine ⟨6, ⟨itemsVal, ⟨8, [itemsVal], locs, jh, hp⟩⟩, ?_, itemsVal, rfl, hrep, rfl, rfl⟩
  step_drop6c 6
  step_res_plain 2; rw [hl3, hl2]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
  rw [runJvmResFast_iflt_fallthrough (compareUnsigned_slt_false_of_not_lt k total hk)]
  step_drop6c 2
  step_res_plain 1; rw [hl7]
  exact runJvmResFast_areturn6c

private theorem gridItems_pre
    (g : Algorithm.AsciiBytes) (total k : UInt32) (gAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hk : k < total) (htot : total.toNat ≤ g.1.data.size) (htot31 : total.toNat < 2 ^ 31)
    (hg : jh.get? gAddr = some (.byteArray g.1.data))
    (hl0 : locs 0 = .heapRef gAddr) (hl2 : locs 2 = .i32 total) (hl3 : locs 3 = .i32 k) :
    ∃ locs53 : Nat → JvmVal,
      (∀ i ≤ 7, locs53 i = locs i) ∧
      locs53 8 = .i32 (g.1.data[k.toNat]'(Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hk) htot)).toUInt32 ∧
      ∀ fuelR,
        runJvmResFast (fuelR + 48) f_Algorithm_gridItems_prog 3
          (f_Algorithm_gridItems_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
        runJvmResFast fuelR f_Algorithm_gridItems_prog 53
          (f_Algorithm_gridItems_prog.drop 53) ⟨53, [], locs53, jh, hp⟩ := by
  have hk_lt_nat : k.toNat < total.toNat := UInt32.lt_iff_toNat_lt.mp hk
  have hk_g : k.toNat < g.1.data.size := Nat.lt_of_lt_of_le hk_lt_nat htot
  have hslt_k : k.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hk (by omega)
  have hcomp_t := compareUnsigned_slt_true_of_lt k total hk
  let tag : UInt8 := g.1.data[k.toNat]'hk_g
  have htag128 : tag < 128 := g.2 k.toNat hk_g
  have hsext := u8Sext_eq_toUInt32_of_lt128 tag htag128
  let locsAfter8 := setLocal locs 8 (.i32 tag.toUInt32)
  let locs53 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal locsAfter8
      9 (.i32 0)) 10 .null) 11 (.i32 0)) 12 (.i32 0)) 13 (.i32 0)) 14 (.i32 0))
      15 (.i32 0)) 16 (.i32 0)) 17 .null) 18 .null) 19 (.i32 0)) 20 (.i32 0))
      21 (.i32 0)) 22 .null) 23 (.i32 0)) 24 .null) 25 (.i32 0)) 26 (.i32 0)) 27 .null
  refine ⟨locs53, ?_, ?_, ?_⟩
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [locs53, locsAfter8, setLocal_apply]
  · simp [locs53, setLocal_apply, locsAfter8, tag]
  · intro fuelR
    step_drop6c 6
    step_res_plain 2; rw [hl3, hl2]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]
    rw [runJvmResFast_iflt_branch hcomp_t]
    step_drop6c 6
    step_res_plain 3; rw [hl0, hl3]
    rw [runJvmResFast_baload_byteArray hg hslt_k hk_g, hsext]
    rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor6c]
    step_res_plain 1
    step_drop6c 38
    step_res_plain 20
    step_res_plain 18
    rfl

private theorem gridItems_mid
    (tag runTag : UInt8) (runLen rowEnds : UInt32)
    (items : Algorithm.GrowBuf (UInt8 × UInt32)) (itemsVal : JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hrep : U8U32PairRep6c items itemsVal)
    (hl4 : locs 4 = .i32 runTag.toUInt32) (hl5 : locs 5 = .i32 runLen)
    (hl6 : locs 6 = .i32 rowEnds) (hl7 : locs 7 = itemsVal) (hl8 : locs 8 = .i32 tag.toUInt32) :
    let grows := runLen != 0 && tag == runTag
    let flush := runLen != 0 && !grows
    let items1 := if flush && rowEnds != 0 then items.push (Algorithm.rleRowEnd, rowEnds) else items
    let items2 := if flush then items1.push (runTag, runLen) else items1
    let rowEnds1 := if flush then 0 else rowEnds
    let curTag := if grows then runTag else tag
    let curLen := if grows then runLen + 1 else 1
    ∃ (fuelM : Nat) (locs129 : Nat → JvmVal),
      (∀ i ≤ 3, locs129 i = locs i) ∧
      U8U32PairRep6c items2 (locs129 18) ∧
      locs129 19 = .i32 rowEnds1 ∧
      locs129 20 = .i32 curTag.toUInt32 ∧
      locs129 21 = .i32 curLen ∧
      ∀ fuelR,
        runJvmResFast (fuelR + fuelM) f_Algorithm_gridItems_prog 53
          (f_Algorithm_gridItems_prog.drop 53) ⟨53, [], locs, jh, hp⟩ =
        runJvmResFast fuelR f_Algorithm_gridItems_prog 129
          (f_Algorithm_gridItems_prog.drop 129) ⟨129, [], locs129, jh, hp⟩ := by
  intro grows flush items1 items2 rowEnds1 curTag curLen
  by_cases hrl : runLen = 0
  · subst hrl
    have hgrows : grows = false := by simp [grows]
    have hflush : flush = false := by simp [flush]
    let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
      22 itemsVal) 23 (.i32 rowEnds)) 18 itemsVal) 19 (.i32 rowEnds))
      20 (.i32 tag.toUInt32)) 21 (.i32 1)
    refine ⟨16, locsN, ?_, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
        simp [locsN, setLocal_apply]
    · simp only [locsN, setLocal_apply, items2, items1, hflush]; exact hrep
    · simp [locsN, setLocal_apply, rowEnds1, hflush]
    · simp [locsN, setLocal_apply, curTag, hgrows]
    · simp [locsN, setLocal_apply, curLen, hgrows]
    · step_drop6c 2
      step_res_plain 1; rw [hl5]
      rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 5
      step_res_plain 4; rw [hl7, hl6]
      rw [runJvmResFast_goto]; step_drop6c 9
      step_res_plain 9; rw [hl8]
  · have hrl_ne : (runLen == 0) = false := beq_false_of_ne hrl
    by_cases htag : tag = runTag
    · subst htag
      have hgrows : grows = true := by simp [grows, hrl]
      have hflush : flush = false := by simp [flush, hgrows]
      let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        locs 24 itemsVal) 25 (.i32 rowEnds)) 26 (.i32 (runLen + 1))) 18 itemsVal)
        19 (.i32 rowEnds)) 20 (.i32 tag.toUInt32)) 21 (.i32 (runLen + 1))
      refine ⟨24, locsN, ?_, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
      · intro i hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
          simp [locsN, setLocal_apply]
      · simp only [locsN, setLocal_apply, items2, items1, hflush]; exact hrep
      · simp [locsN, setLocal_apply, rowEnds1, hflush]
      · simp [locsN, setLocal_apply, curTag]
      · simp [locsN, setLocal_apply, curLen, hgrows]
      · step_drop6c 5
        step_res_plain 1; rw [hl5]
        rw [runJvmResFast_ifeq_fallthrough hrl_ne]
        step_res_plain 2; rw [hl8, hl4]
        rw [runJvmResFast_if_icmpeq_branch rfl]; step_drop6c 5
        step_res_plain 4; rw [hl7, hl6]
        rw [runJvmResFast_goto]; step_drop6c 14
        step_res_plain 3; rw [hl5]
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
        step_res_plain 9; rw [hl4]
        rw [runJvmResFast_goto]
        dsimp only [locsN, Jvm.JvmVal.asI32]
    · have htag_ne : (tag.toUInt32 == runTag.toUInt32) = false := by
        rw [u8_toUInt32_beq6c]; exact beq_false_of_ne htag
      have hgrows : grows = false := by simp [grows, htag]
      have hflush : flush = true := by simp [flush, hrl, hgrows]
      by_cases hre : rowEnds = 0
      · subst hre
        have hre_z : items1 = items := by simp [items1]
        let locs27 := setLocal (setLocal locs 26 (.i32 0)) 27 itemsVal
        let pushed := items.push (runTag, runLen)
        let pushedVal := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed)
        let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          locs27 28 pushedVal) 22 pushedVal) 23 (.i32 0)) 18 pushedVal)
          19 (.i32 0)) 20 (.i32 tag.toUInt32)) 21 (.i32 1)
        refine ⟨37, locsN, ?_, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
        · intro i hi
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
            simp [locsN, locs27, setLocal_apply]
        · simp only [locsN, setLocal_apply, items2, hre_z, hflush, pushedVal, pushed]
          exact U8U32PairRep6c.full pushed
        · simp [locsN, setLocal_apply, rowEnds1]
        · simp [locsN, setLocal_apply, curTag, hgrows]
        · simp [locsN, setLocal_apply, curLen, hgrows]
        · step_drop6c 7
          step_res_plain 1; rw [hl5]
          rw [runJvmResFast_ifeq_fallthrough hrl_ne]
          step_res_plain 2; rw [hl8, hl4]
          rw [runJvmResFast_if_icmpeq_fallthrough htag_ne]
          step_res_plain 1; rw [hl6]
          rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 5
          step_res_plain 4; rw [hl7]
          rw [runJvmResFast_goto]; step_drop6c 16
          step_res_plain 1
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2; rw [hl4]
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1; rw [hl5]
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u8u32 hrep)]
          step_res_plain 6
          rw [runJvmResFast_goto]; step_drop6c 9
          step_res_plain 9; rw [hl8]
      · have hre_ne : (rowEnds == 0) = false := beq_false_of_ne hre
        have hitems1 : items1 = items.push (Algorithm.rleRowEnd, rowEnds) := by
          simp [items1, hflush, hre]
        let pushed1 := items.push (Algorithm.rleRowEnd, rowEnds)
        let pushed1Val := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed1)
        let locs27 := setLocal (setLocal (setLocal locs 28 pushed1Val) 26 (.i32 0)) 27 pushed1Val
        let pushed2 := pushed1.push (runTag, runLen)
        let pushed2Val := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed2)
        let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          locs27 28 pushed2Val) 22 pushed2Val) 23 (.i32 0)) 18 pushed2Val)
          19 (.i32 0)) 20 (.i32 tag.toUInt32)) 21 (.i32 1)
        refine ⟨47, locsN, ?_, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
        · intro i hi
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
            simp [locsN, locs27, setLocal_apply]
        · simp only [locsN, setLocal_apply, items2, hitems1, hflush, pushed2, pushed1, pushed2Val]
          exact U8U32PairRep6c.full pushed2
        · simp [locsN, setLocal_apply, rowEnds1, hflush]
        · simp [locsN, setLocal_apply, curTag, hgrows]
        · simp [locsN, setLocal_apply, curLen, hgrows]
        · step_drop6c 7
          step_res_plain 1; rw [hl5]
          rw [runJvmResFast_ifeq_fallthrough hrl_ne]
          step_res_plain 2; rw [hl8, hl4]
          rw [runJvmResFast_if_icmpeq_fallthrough htag_ne]
          step_res_plain 1; rw [hl6]
          rw [runJvmResFast_ifeq_fallthrough hre_ne]
          step_drop6c 15
          step_res_plain 1; rw [hl7]
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1; rw [hl6]
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [show (36 : UInt32) = (Algorithm.rleRowEnd : UInt8).toUInt32 from rfl]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u8u32 hrep)]
          step_res_plain 5
          rw [runJvmResFast_goto]; step_drop6c 16
          step_res_plain 1
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2; rw [hl4]
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1; rw [hl5]
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [runJvmResFast_invokestatic_step
            (stepStatic_growBufPush_u8u32 (U8U32PairRep6c.full pushed1))]
          step_res_plain 6
          rw [runJvmResFast_goto]; step_drop6c 9
          step_res_plain 9; rw [hl8]

private theorem gridItems_tail
    (w total k rowEnds1 curLen : UInt32) (curTag : UInt8) (gAddr : Nat)
    (items2 : Algorithm.GrowBuf (UInt8 × UInt32)) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hw : w ≠ 0)
    (hrep2 : U8U32PairRep6c items2 (locs 18))
    (hl0 : locs 0 = .heapRef gAddr) (hl1 : locs 1 = .i32 w)
    (hl2 : locs 2 = .i32 total) (hl3 : locs 3 = .i32 k)
    (hl19 : locs 19 = .i32 rowEnds1) (hl20 : locs 20 = .i32 curTag.toUInt32)
    (hl21 : locs 21 = .i32 curLen) :
    let eor := (k + 1) % w == 0
    let emit := eor && (curTag == Algorithm.rleAlive)
    let items3 := if emit && rowEnds1 != 0 then items2.push (Algorithm.rleRowEnd, rowEnds1) else items2
    let items4 := if emit then items3.push (Algorithm.rleAlive, curLen) else items3
    let rowEnds2 := if emit then 0 else rowEnds1
    let nextTag := if eor then Algorithm.rleDead else curTag
    let nextLen := if eor then 0 else curLen
    let nextRowEnds := if eor then rowEnds2 + 1 else rowEnds1
    let nextItems := if eor then items4 else items2
    ∃ (fuelT : Nat) (locs3 : Nat → JvmVal),
      locs3 0 = .heapRef gAddr ∧ locs3 1 = .i32 w ∧ locs3 2 = .i32 total ∧
      locs3 3 = .i32 (k + 1) ∧ locs3 4 = .i32 nextTag.toUInt32 ∧
      locs3 5 = .i32 nextLen ∧ locs3 6 = .i32 nextRowEnds ∧
      U8U32PairRep6c nextItems (locs3 7) ∧
      ∀ fuelR,
        runJvmResFast (fuelR + fuelT) f_Algorithm_gridItems_prog 129
          (f_Algorithm_gridItems_prog.drop 129) ⟨129, [], locs, jh, hp⟩ =
        runJvmResFast fuelR f_Algorithm_gridItems_prog 3
          (f_Algorithm_gridItems_prog.drop 3) ⟨3, [], locs3, jh, hp⟩ := by
  intro eor emit items3 items4 rowEnds2 nextTag nextLen nextRowEnds nextItems
  by_cases heor : (k + 1) % w = 0
  · have heor_t : eor = true := by simp [eor, heor]
    by_cases halive : curTag = Algorithm.rleAlive
    · subst halive
      have hemit : emit = true := by simp [emit, heor_t]
      by_cases hre : rowEnds1 = 0
      · subst hre
        have hitems3 : items3 = items2 := by simp [items3]
        let pushed := items2.push (Algorithm.rleAlive, curLen)
        let pushedVal := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed)
        let locsM := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal locs
          22 (.i32 (k + 1))) 13 (.i32 (k + 1))) 14 (.i32 curLen))
          15 (.i32 (Algorithm.rleAlive : UInt8).toUInt32)) 16 (.i32 1))
          17 (locs 18)) 23 pushedVal) 9 (.i32 (k + 1))) 10 pushedVal)
          11 (.i32 1)) 12 (.i32 0)
        let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal locsM
          13 (.heapRef gAddr)) 14 (.i32 w)) 15 (.i32 total)) 16 (.i32 1))
          0 (.heapRef gAddr)) 1 (.i32 w)) 2 (.i32 total)) 3 (.i32 (k + 1)))
          4 (.i32 (Algorithm.rleDead : UInt8).toUInt32)) 5 (.i32 0)) 6 (.i32 1))
          7 pushedVal
        refine ⟨71, locsN, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
        · simp [locsN, setLocal_apply, nextTag, heor_t]
        · simp [locsN, setLocal_apply, nextLen, heor_t]
        · simp [locsN, setLocal_apply, nextRowEnds, rowEnds2, heor_t]
        · simp only [locsN, setLocal_apply, nextItems, heor_t, items4, hitems3, hemit, pushedVal,
            pushed]
          exact U8U32PairRep6c.full pushed
        · step_drop6c 9
          step_res_plain 3; rw [hl3]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 3; rw [hl1]
          rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned6c hw)]
          dsimp only [Jvm.JvmVal.asI32]
          rw [runJvmResFast_ifeq_branch (by simp [heor])]; step_drop6c 14
          step_res_plain 2; rw [hl20]
          rw [runJvmResFast_if_icmpeq_branch (by simp [Algorithm.rleAlive])]; step_drop6c 12
          step_res_plain 1; rw [hl19]
          rw [runJvmResFast_ifeq_branch rfl]; step_drop6c 29
          step_res_plain 11
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2; rw [hl21]
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [show (111 : UInt32) = (Algorithm.rleAlive : UInt8).toUInt32 from rfl]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u8u32 hrep2)]
          step_res_plain 10; step_drop6c 28
          step_res_plain 9; rw [hl0, hl1, hl2]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 17
          rw [runJvmResFast_goto]
          dsimp only [locsN, locsM, pushedVal, pushed, Jvm.JvmVal.asI32,
            Algorithm.rleAlive, Algorithm.rleDead]
          rw [show (98 : UInt32) = (98 : UInt8).toUInt32 from rfl]
          rfl
      · have hre_ne : (rowEnds1 == 0) = false := beq_false_of_ne hre
        have hitems3 : items3 = items2.push (Algorithm.rleRowEnd, rowEnds1) := by
          simp [items3, hemit, hre]
        let pushed1 := items2.push (Algorithm.rleRowEnd, rowEnds1)
        let pushed1Val := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed1)
        let pushed2 := pushed1.push (Algorithm.rleAlive, curLen)
        let pushed2Val := JvmVal.ext (AlgExt.u8U32PairGrowBuf pushed2)
        let locsM' := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal locs
          22 (.i32 (k + 1))) 23 pushed1Val) 13 (.i32 (k + 1))) 14 (.i32 curLen))
          15 (.i32 (Algorithm.rleAlive : UInt8).toUInt32)) 16 (.i32 1))
          17 pushed1Val) 23 pushed2Val) 9 (.i32 (k + 1))) 10 pushed2Val)
          11 (.i32 1)) 12 (.i32 0)
        let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal locsM'
          13 (.heapRef gAddr)) 14 (.i32 w)) 15 (.i32 total)) 16 (.i32 (0 + 1)))
          0 (.heapRef gAddr)) 1 (.i32 w)) 2 (.i32 total)) 3 (.i32 (k + 1)))
          4 (.i32 (Algorithm.rleDead : UInt8).toUInt32)) 5 (.i32 0)) 6 (.i32 (0 + 1)))
          7 pushed2Val
        refine ⟨82, locsN, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
        · simp [locsN, setLocal_apply, nextTag, heor_t]
        · simp [locsN, setLocal_apply, nextLen, heor_t]
        · simp [locsN, setLocal_apply, nextRowEnds, rowEnds2, heor_t, hemit]
        · simp only [locsN, setLocal_apply, nextItems, heor_t, items4, hitems3, hemit, pushed2,
            pushed1, pushed2Val]
          exact U8U32PairRep6c.full pushed2
        · step_drop6c 9
          step_res_plain 3; rw [hl3]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 3; rw [hl1]
          rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned6c hw)]
          dsimp only [Jvm.JvmVal.asI32]
          rw [runJvmResFast_ifeq_branch (by simp [heor])]; step_drop6c 14
          step_res_plain 2; rw [hl20]
          rw [runJvmResFast_if_icmpeq_branch (by simp [Algorithm.rleAlive])]; step_drop6c 12
          step_res_plain 1; rw [hl19]
          rw [runJvmResFast_ifeq_fallthrough hre_ne]
          step_drop6c 31
          step_res_plain 1
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1; rw [hl19]
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [show (36 : UInt32) = (Algorithm.rleRowEnd : UInt8).toUInt32 from rfl]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u8u32 hrep2)]
          step_res_plain 11; rw [hl21]
          rw [runJvmResFast_goto]; step_drop6c 19
          step_res_plain 1
          rw [runJvmResFast_newClass_pair6c]
          step_res_plain 2
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteBox6c]
          step_res_plain 1
          rw [runJvmResFast_invokestatic_step stepStatic_uintBox6c]
          rw [runJvmResFast_invokespecial_step stepSpecial_pairInit6c]
          rw [show (111 : UInt32) = (Algorithm.rleAlive : UInt8).toUInt32 from rfl]
          rw [runJvmResFast_invokestatic_step
            (stepStatic_growBufPush_u8u32 (U8U32PairRep6c.full pushed1))]
          step_res_plain 10; step_drop6c 28
          step_res_plain 9; rw [hl0, hl1, hl2]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
          step_res_plain 17
          rw [runJvmResFast_goto]
          dsimp only [locsN, locsM', pushed1Val, pushed2Val, pushed2, pushed1,
            Jvm.JvmVal.asI32, Algorithm.rleAlive, Algorithm.rleRowEnd, Algorithm.rleDead]
          rw [show (98 : UInt32) = (98 : UInt8).toUInt32 from rfl]
    · have hnot111 : (curTag.toUInt32 == 111) = false := by
        rw [show (111 : UInt32) = (111 : UInt8).toUInt32 from rfl, u8_toUInt32_beq6c]
        exact beq_false_of_ne halive
      have hemit : emit = false := by simp [emit, halive]
      let locsM := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal locs 22 (.i32 (k + 1))) 9 (.i32 (k + 1))) 10 (locs 18))
        11 (.i32 1)) 12 (.i32 rowEnds1)) 13 (.heapRef gAddr)) 14 (.i32 w)) 15 (.i32 total)
      let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal locsM 16 (.i32 (rowEnds1 + 1))) 0 (.heapRef gAddr)) 1 (.i32 w))
        2 (.i32 total)) 3 (.i32 (k + 1))) 4 (.i32 (Algorithm.rleDead : UInt8).toUInt32))
        5 (.i32 0)) 6 (.i32 (rowEnds1 + 1))) 7 (locs 18)
      refine ⟨49, locsN, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
      · simp [locsN, setLocal_apply, nextTag, heor_t]
      · simp [locsN, setLocal_apply, nextLen, heor_t]
      · simp [locsN, setLocal_apply, nextRowEnds, rowEnds2, heor_t, hemit]
      · simpa [locsN, setLocal_apply, nextItems, heor_t, items4, items3, hemit] using hrep2
      · step_drop6c 9
        step_res_plain 3; rw [hl3]
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
        step_res_plain 3; rw [hl1]
        rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned6c hw)]
        dsimp only [Jvm.JvmVal.asI32]
        rw [runJvmResFast_ifeq_branch (by simp [heor])]; step_drop6c 12
        step_res_plain 2; rw [hl20]
        rw [runJvmResFast_if_icmpeq_fallthrough hnot111]
        step_res_plain 8; rw [hl19]
        rw [runJvmResFast_goto]; step_drop6c 28
        step_res_plain 3; rw [hl0, hl1]
        step_res_plain 6; rw [hl2]
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
        step_res_plain 17
        rw [runJvmResFast_goto]
        dsimp only [locsN, locsM, Jvm.JvmVal.asI32, Algorithm.rleDead]
        rw [show (98 : UInt32) = (98 : UInt8).toUInt32 from rfl]
  · have heor_f : ((k + 1) % w == 0) = false := beq_false_of_ne heor
    have heor_bool : eor = false := by simp [eor, heor]
    let locsN := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal locs
      22 (.i32 (k + 1))) 23 (.heapRef gAddr)) 24 (.i32 w)) 25 (.i32 total))
      0 (.heapRef gAddr)) 1 (.i32 w)) 2 (.i32 total)) 3 (.i32 (k + 1)))
      4 (.i32 curTag.toUInt32)) 5 (.i32 curLen)) 6 (.i32 rowEnds1)) 7 (locs 18)
    refine ⟨32, locsN, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun fuelR => ?_⟩
    · simp [locsN, setLocal_apply, nextTag, heor_bool]
    · simp [locsN, setLocal_apply, nextLen, heor_bool]
    · simp [locsN, setLocal_apply, nextRowEnds, heor_bool]
    · simpa [locsN, setLocal_apply, nextItems, heor_bool] using hrep2
    · step_drop6c 9
      step_res_plain 3; rw [hl3]
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 3; rw [hl1]
      rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned6c hw)]
      dsimp only [Jvm.JvmVal.asI32]
      rw [runJvmResFast_ifeq_fallthrough heor_f]
      step_drop6c 23
      step_res_plain 6; rw [hl0, hl1, hl2]
      step_res_plain 16; rw [hl20, hl21, hl19]
      rw [runJvmResFast_goto]

private theorem gridItems_loop
    (n : Nat)
    (g : Algorithm.AsciiBytes) (w total k : UInt32) (runTag : UInt8) (runLen rowEnds : UInt32)
    (items : Algorithm.GrowBuf (UInt8 × UInt32)) (itemsVal : JvmVal) (gAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (hrep : U8U32PairRep6c items itemsVal)
    (hg : jh.get? gAddr = some (.byteArray g.1.data))
    (htot : total.toNat ≤ g.1.data.size) (htot31 : total.toNat < 2 ^ 31) (hw : w ≠ 0)
    (hn : total.toNat - k.toNat ≤ n)
    (hl0 : locs 0 = .heapRef gAddr) (hl1 : locs 1 = .i32 w) (hl2 : locs 2 = .i32 total)
    (hl3 : locs 3 = .i32 k) (hl4 : locs 4 = .i32 runTag.toUInt32)
    (hl5 : locs 5 = .i32 runLen) (hl6 : locs 6 = .i32 rowEnds) (hl7 : locs 7 = itemsVal) :
    ∃ fuel st',
      runJvmResFast fuel f_Algorithm_gridItems_prog 3
        (f_Algorithm_gridItems_prog.drop 3) ⟨3, [], locs, jh, hp⟩ = some st' ∧
      ∃ rVal, st'.1 = rVal ∧
      U8U32PairRep6c (Algorithm.gridItems g w total k runTag runLen rowEnds items) rVal ∧
      st'.2.jvmHeap = jh ∧ st'.2.heap = hp := by
  induction n generalizing k runTag runLen rowEnds items itemsVal locs with
  | zero =>
    have hk : ¬(k < total) := by
      intro hlt
      have : k.toNat < total.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      omega
    rw [Algorithm.gridItems.eq_1]
    simp only [hk, ↓reduceDIte]
    exact gridItems_base total k items itemsVal jh hp locs hk hrep hl2 hl3 hl7
  | succ n ih =>
    by_cases hk : k < total
    · have hk_lt_nat : k.toNat < total.toNat := UInt32.lt_iff_toNat_lt.mp hk
      have hk_g : k.toNat < g.1.data.size := Nat.lt_of_lt_of_le hk_lt_nat htot
      have hk1 : (k + 1).toNat = k.toNat + 1 := ui32_add1_toNat hk
      have hdec : total.toNat - (k + 1).toNat ≤ n := by omega
      let tag : UInt8 := g.1.data[k.toNat]'hk_g
      have htag_eq : g.1.get! k.toNat = tag := by
        simp only [ByteArray.get!, getElem!, Array.get!Internal, Array.getD, hk_g, ↓reduceDIte]
        rfl
      let grows := runLen != 0 && tag == runTag
      let flush := runLen != 0 && !grows
      let items1 := if flush && rowEnds != 0 then items.push (Algorithm.rleRowEnd, rowEnds) else items
      let items2 := if flush then items1.push (runTag, runLen) else items1
      let rowEnds1 := if flush then 0 else rowEnds
      let curTag := if grows then runTag else tag
      let curLen := if grows then runLen + 1 else 1
      let eor := (k + 1) % w == 0
      let emit := eor && (curTag == Algorithm.rleAlive)
      let items3 := if emit && rowEnds1 != 0 then items2.push (Algorithm.rleRowEnd, rowEnds1) else items2
      let items4 := if emit then items3.push (Algorithm.rleAlive, curLen) else items3
      let rowEnds2 := if emit then 0 else rowEnds1
      let nextTag := if eor then Algorithm.rleDead else curTag
      let nextLen := if eor then 0 else curLen
      let nextRowEnds := if eor then rowEnds2 + 1 else rowEnds1
      let nextItems := if eor then items4 else items2
      obtain ⟨locs53, hloc53_07, hloc53_8, hpre⟩ :=
        gridItems_pre g total k gAddr jh hp locs hk htot htot31 hg hl0 hl2 hl3
      have hl53_0 : locs53 0 = .heapRef gAddr := by rw [hloc53_07 0 (by decide), hl0]
      have hl53_1 : locs53 1 = .i32 w := by rw [hloc53_07 1 (by decide), hl1]
      have hl53_2 : locs53 2 = .i32 total := by rw [hloc53_07 2 (by decide), hl2]
      have hl53_3 : locs53 3 = .i32 k := by rw [hloc53_07 3 (by decide), hl3]
      have hl53_4 : locs53 4 = .i32 runTag.toUInt32 := by rw [hloc53_07 4 (by decide), hl4]
      have hl53_5 : locs53 5 = .i32 runLen := by rw [hloc53_07 5 (by decide), hl5]
      have hl53_6 : locs53 6 = .i32 rowEnds := by rw [hloc53_07 6 (by decide), hl6]
      have hl53_7 : locs53 7 = itemsVal := by rw [hloc53_07 7 (by decide), hl7]
      obtain ⟨fuelM, locs129, hloc129_03, hrep2, h19, h20, h21, hmid⟩ :=
        gridItems_mid tag runTag runLen rowEnds items itemsVal jh hp locs53 hrep
          hl53_4 hl53_5 hl53_6 hl53_7 hloc53_8
      have h129_0 : locs129 0 = .heapRef gAddr := by rw [hloc129_03 0 (by decide), hl53_0]
      have h129_1 : locs129 1 = .i32 w := by rw [hloc129_03 1 (by decide), hl53_1]
      have h129_2 : locs129 2 = .i32 total := by rw [hloc129_03 2 (by decide), hl53_2]
      have h129_3 : locs129 3 = .i32 k := by rw [hloc129_03 3 (by decide), hl53_3]
      obtain ⟨fuelT, locsNext, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hrepN, htail⟩ :=
        gridItems_tail w total k rowEnds1 curLen curTag gAddr items2 locs129 jh hp hw
          hrep2 h129_0 h129_1 h129_2 h129_3 h19 h20 h21
      have hrec := ih (k + 1) nextTag nextLen nextRowEnds nextItems (locsNext 7) locsNext
        hrepN hdec hn0 hn1 hn2 hn3 hn4 hn5 hn6 rfl
      rcases hrec with ⟨fuel', st', hrun', rVal, hres', hrep_out, hjh', hhp'⟩
      refine ⟨fuel' + fuelT + fuelM + 48, st', ?_, rVal, hres', ?_, hjh', hhp'⟩
      · rw [show fuel' + fuelT + fuelM + 48 = (fuel' + fuelT + fuelM) + 48 from rfl]
        rw [hpre (fuel' + fuelT + fuelM), show fuel' + fuelT + fuelM = (fuel' + fuelT) + fuelM from rfl]
        rw [hmid (fuel' + fuelT), htail fuel']
        exact hrun'
      · rw [Algorithm.gridItems.eq_1]
        simp only [hk, ↓reduceDIte, htag_eq]
        by_cases heor_b : (k + 1) % w == 0
        · simpa [nextItems, nextTag, nextLen, nextRowEnds, items4, items3, rowEnds2,
            emit, eor, curTag, curLen, rowEnds1, items2, items1, flush, grows, heor_b] using
            hrep_out
        · simpa [nextItems, nextTag, nextLen, nextRowEnds, items4, items3, rowEnds2,
            emit, eor, curTag, curLen, rowEnds1, items2, items1, flush, grows, heor_b] using
            hrep_out
    · rw [Algorithm.gridItems.eq_1]
      simp only [hk, ↓reduceDIte]
      exact gridItems_base total k items itemsVal jh hp locs hk hrep hl2 hl3 hl7

theorem gridItems_equiv
    (g : Algorithm.AsciiBytes) (w total k : UInt32) (runTag : UInt8) (runLen rowEnds : UInt32)
    (items : Algorithm.GrowBuf (UInt8 × UInt32))
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (htot : total.toNat ≤ g.1.data.size) (htot31 : total.toNat < 2 ^ 31) (hw : w ≠ 0) :
    let gAddr := (jh.alloc (.byteArray g.1.data)).1
    let jh0 := (jh.alloc (.byteArray g.1.data)).2
    let initSt := { initJvmState
      [(0, Jvm.JvmVal.heapRef gAddr), (1, Jvm.JvmVal.i32 w), (2, Jvm.JvmVal.i32 total),
       (3, Jvm.JvmVal.i32 k), (4, Jvm.JvmVal.i32 runTag.toUInt32),
       (5, Jvm.JvmVal.i32 runLen), (6, Jvm.JvmVal.i32 rowEnds),
       (7, Jvm.JvmVal.ext (AlgExt.u8U32PairGrowBuf items))]
      with jvmHeap := jh0, heap := hp }
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_gridItems_prog initSt = some st' ∧
      ∃ rVal, st'.1 = rVal ∧
      U8U32PairRep6c (Algorithm.gridItems g w total k runTag runLen rowEnds items) rVal ∧
      st'.2.jvmHeap = jh0 ∧ st'.2.heap = hp := by
  intro gAddr jh0 initSt
  have hget : jh0.get? gAddr = some (.byteArray g.1.data) :=
    jvmHeap_get?_alloc_self _ _
  have hloop := gridItems_loop (total.toNat - k.toNat) g w total k runTag runLen rowEnds
    items (.ext (.u8U32PairGrowBuf items)) gAddr jh0 hp initSt.locals
    (U8U32PairRep6c.full items) hget htot htot31 hw (Nat.le_refl _)
    rfl rfl rfl rfl rfl rfl rfl rfl
  rcases hloop with ⟨fuel, st', hrun, rVal, hres, hrep, hjh, hhp⟩
  refine ⟨fuel + 3, st', ?_, rVal, hres, hrep, hjh, hhp⟩
  apply runJvmRes_of_runJvmResFast0
  dsimp only [initSt, initJvmState, Jvm.initJvmState]
  change runJvmResFast (fuel + 3) f_Algorithm_gridItems_prog 0
      (f_Algorithm_gridItems_prog.drop 0) ⟨0, [], initSt.locals, jh0, hp⟩ = some st'
  step_drop6c 3
  step_res_plain 2
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam6c
    (by simp [initSt, initJvmState, Jvm.initJvmState, Jvm.JvmVal.isNull, setLocal_apply]))]
  exact hrun

/-! #### 5. `serializeRLE` -/

private theorem stepStatic_growBufEmpty6c
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .null :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_empty___redArg" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_ulongArrSize6c
    {pc cId : Nat} {cells : Array UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hc : hp.u64Arrays[cId]? = some cells) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "kotlin/ULongArray" "getSize-impl" "([J)I" =
      .inl (some ⟨pc + 1, .i32 cells.size.toUInt32 :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "kotlin/ULongArray" "getSize-impl" "([J)I" =
      match hp.u64Arrays[cId]? with
      | some arr => .inl (some ⟨pc + 1, .i32 arr.size.toUInt32 :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn, hc]

private theorem stepStatic_serializeRLE_closed3_6c
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_serializeRLE___closed__3" "()[Ljava/lang/Object;" =
      let (addr, h') := jh.alloc (.objArray "java/lang/Object"
        #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .str "!"])
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

private theorem stepStatic_serializeRLE_closed0_6c
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_serializeRLE___closed__0" "()Lkotlin/Pair;" =
      .inl (some ⟨pc + 1, .pair (.boxedUByte 33) (.boxedUInt 1) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_asciiBytesReplicate6c
    {pc : Nat} {n : UInt32} {v : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hb : v.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, .i32 v :: .i32 n :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_AsciiBytes_replicate___redArg-LMfZGw8" "(IB)[B" =
      let newId := hp.asciiArrays.length
      let arr := Algorithm.AsciiBytes.replicate n v.toUInt8 hb
      .inl (some ⟨pc + 1, .ext (.asciiRef newId) :: rest, locs, jh,
        { hp with asciiArrays := hp.asciiArrays ++ [arr] }⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 v :: .i32 n :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_AsciiBytes_replicate___redArg-LMfZGw8" "(IB)[B" =
      if hb' : v.toUInt8 < 128 then
        let newId := hp.asciiArrays.length
        let arr := Algorithm.AsciiBytes.replicate n v.toUInt8 hb'
        .inl (some ⟨pc + 1, .ext (.asciiRef newId) :: rest, locs, jh,
          { hp with asciiArrays := hp.asciiArrays ++ [arr] }⟩)
      else .inr none := rfl
  rw [hfn]
  simp only [hb, ↓reduceDIte]

private theorem int32_toInt32_toUInt32_6c (x : Int32) : x.toUInt32.toInt32 = x := by
  cases x; rfl

private theorem stepStatic_fillGrid6c
    {pc cId gId : Nat} {minX minY : Int32} {w h i limit : UInt32} {ab : UInt8}
    {cells : Array UInt64} {g : Algorithm.AsciiBytes} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hc : hp.u64Arrays[cId]? = some cells) (hg : hp.asciiArrays[gId]? = some g)
    (ha : ab < 128) :
    stepInvokeStatic ⟨pc, .ext (.asciiRef gId) :: .i32 limit :: .i32 i :: .i32 ab.toUInt32 ::
        .i32 h :: .i32 w :: .i32 minY.toUInt32 :: .i32 minX.toUInt32 ::
        .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_fillGrid___redArg-RyWfpmY" "([JIIIIBII[B)V" =
      let g' := Algorithm.fillGrid cells minX minY w h ab ha i limit g
      .inl (some ⟨pc + 1, rest, locs, jh,
        { hp with asciiArrays := hp.asciiArrays.set gId g' }⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.asciiRef gId) :: .i32 limit :: .i32 i ::
      .i32 ab.toUInt32 :: .i32 h :: .i32 w :: .i32 minY.toUInt32 :: .i32 minX.toUInt32 ::
      .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_fillGrid___redArg-RyWfpmY" "([JIIIIBII[B)V" =
      let ab' := ab.toUInt32.toUInt8
      match hp.u64Arrays[cId]?, hp.asciiArrays[gId]? with
      | some cells, some g =>
        if ha' : ab' < 128 then
          let g' := Algorithm.fillGrid cells minX.toUInt32.toInt32 minY.toUInt32.toInt32
            w h ab' ha' i limit g
          .inl (some ⟨pc + 1, rest, locs, jh,
            { hp with asciiArrays := hp.asciiArrays.set gId g' }⟩)
        else .inr none
      | _, _ => .inr none := rfl
  rw [hfn, hc, hg]
  dsimp only
  simp only [u8_toUInt32_toUInt8, int32_toInt32_toUInt32_6c, ha, ↓reduceDIte]

private theorem stepStatic_gridItems6c
    {pc gId : Nat} {w total k runLen rowEnds : UInt32} {runTag : UInt8}
    {g : Algorithm.AsciiBytes} {itemsVal : JvmVal} {items : Algorithm.GrowBuf (UInt8 × UInt32)}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hg : hp.asciiArrays[gId]? = some g) (hrep : U8U32PairRep6c items itemsVal) :
    stepInvokeStatic ⟨pc, itemsVal :: .i32 rowEnds :: .i32 runLen :: .i32 runTag.toUInt32 ::
        .i32 k :: .i32 total :: .i32 w :: .ext (.asciiRef gId) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_gridItems-DRwJadE"
      "([BIIIBIILjava/lang/Object;)Ljava/lang/Object;" =
      let r := Algorithm.gridItems g w total k runTag runLen rowEnds items
      .inl (some ⟨pc + 1, .ext (.u8U32PairGrowBuf r) :: rest, locs, jh, hp⟩) := by
  cases hrep with
  | empty d hd1 hd2 =>
    have hfn : stepInvokeStatic ⟨pc, .ext (.strGrowBuf d) :: .i32 rowEnds :: .i32 runLen ::
        .i32 runTag.toUInt32 :: .i32 k :: .i32 total :: .i32 w :: .ext (.asciiRef gId) :: rest,
        locs, jh, hp⟩
        "RleLeanKt" "f_Algorithm_gridItems-DRwJadE"
        "([BIIIBIILjava/lang/Object;)Ljava/lang/Object;" =
        match hp.asciiArrays[gId]?,
            (if d.data.isEmpty && d.size == 0 then some Algorithm.GrowBuf.empty else none) with
        | some g, some items =>
          let r := Algorithm.gridItems g w total k runTag.toUInt32.toUInt8 runLen rowEnds items
          .inl (some ⟨pc + 1, .ext (.u8U32PairGrowBuf r) :: rest, locs, jh, hp⟩)
        | _, _ => .inr none := rfl
    rw [hfn, hg, u8_toUInt32_toUInt8]
    simp [hd1, hd2]
  | full =>
    have hfn : stepInvokeStatic ⟨pc, .ext (.u8U32PairGrowBuf items) :: .i32 rowEnds ::
        .i32 runLen :: .i32 runTag.toUInt32 :: .i32 k :: .i32 total :: .i32 w ::
        .ext (.asciiRef gId) :: rest, locs, jh, hp⟩
        "RleLeanKt" "f_Algorithm_gridItems-DRwJadE"
        "([BIIIBIILjava/lang/Object;)Ljava/lang/Object;" =
        match hp.asciiArrays[gId]?, some items with
        | some g, some items' =>
          let r := Algorithm.gridItems g w total k runTag.toUInt32.toUInt8 runLen rowEnds items'
          .inl (some ⟨pc + 1, .ext (.u8U32PairGrowBuf r) :: rest, locs, jh, hp⟩)
        | _, _ => .inr none := rfl
    rw [hfn, hg, u8_toUInt32_toUInt8]

private theorem list_foldl_encodePure6c {α : Type} (xs : List α) (f : α → JvmVal)
    (acc : Array JvmVal) (h : Jvm.JvmHeap AlgExt) :
    xs.foldl (fun p x => (p.1.push (f x), p.2)) (acc, h) =
      ((acc.toList ++ xs.map f).toArray, h) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Array.toList_push, List.append_assoc]

private theorem encodeGrowBufArray_pure6c {α : Type} (b : Algorithm.GrowBuf α) (f : α → JvmVal)
    (h : Jvm.JvmHeap AlgExt) :
    encodeGrowBufArray h (fun ch x => (f x, ch)) b =
      let (addr, h') := h.alloc (.objArray "java/lang/Object" (b.toArray.map f))
      (.heapRef addr, h') := by
  dsimp only [encodeGrowBufArray]
  rw [← Array.foldl_toList]
  rw [list_foldl_encodePure6c b.toArray.toList f #[] h]
  have hmap : (b.toArray.toList.map f).toArray = b.toArray.map f := by
    apply Array.ext
    · simp
    · intro i hi1 hi2; simp
  simp [hmap]

private theorem stepStatic_growBufToArray_u8u32_6c
    {pc : Nat} {b : Algorithm.GrowBuf (UInt8 × UInt32)}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.u8U32PairGrowBuf b) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      let (addr, h') := jh.alloc (.objArray "java/lang/Object"
        (b.toArray.map fun x => .pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2)))
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.u8U32PairGrowBuf b) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      let res := encodeGrowBufArray jh (fun ch x =>
        (.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2), ch)) b
      .inl (some ⟨pc + 1, res.1 :: rest, locs, res.2, hp⟩) := rfl
  rw [hfn, encodeGrowBufArray_pure6c]

private theorem stepStatic_growBufToArray_str6c
    {pc : Nat} {b : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strArr b.toArray :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_arraysCopyOf6c
    {pc addr : Nat} {elemCls : String} {elems : Array JvmVal} {newLen : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.objArray elemCls elems))
    (hnonneg : newLen.toBitVec.slt 0#32 = false) :
    stepInvokeStatic ⟨pc, .i32 newLen :: .heapRef addr :: rest, locs, jh, hp⟩
      "java/util/Arrays" "copyOf" "([Ljava/lang/Object;I)[Ljava/lang/Object;" =
      let copied := Array.ofFn (n := newLen.toNat)
        (fun i => if h : i.val < elems.size then elems[i.val] else .null)
      let (newAddr, h') := jh.alloc (.objArray elemCls copied)
      .inl (some ⟨pc + 1, .heapRef newAddr :: rest, locs, h', hp⟩) := by
  rw [stepStatic_arraysCopyOf_obj hnonneg hget]
  rfl

private theorem stepStatic_checkNotNullExpr6c
    {pc : Nat} {obj : JvmVal} {msg : String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnn : obj.isNull = false) :
    stepInvokeStatic ⟨pc, .str msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .str msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := rfl
  rw [hfn, hnn]
  rfl

private theorem stepStatic_formatRLEHeader6c
    {pc : Nat} {minX minY : Int32} {w h : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 h :: .i32 w :: .i32 minY.toUInt32 :: .i32 minX.toUInt32 :: rest,
        locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_formatRLEHeader-uqS13hg" "(IIII)[Ljava/lang/Object;" =
      let arr := Algorithm.formatRLEHeader minX minY w h
      let (addr, h') := jh.alloc (.objArray "java/lang/Object" (arr.map .str))
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

private theorem stepStatic_wrapRLEItems6c
    {pc itemsAddr : Nat} {items : Array (UInt8 × UInt32)}
    {j lineLen : UInt32} {line : String} {out : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? itemsAddr = some (.objArray "java/lang/Object"
      (items.map fun x => .pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2)))) :
    stepInvokeStatic ⟨pc, .ext (.strGrowBuf out) :: .i32 lineLen :: .str line :: .i32 j ::
        .i32 items.size.toUInt32 :: .heapRef itemsAddr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_wrapRLEItems-zax99WU"
      "([Ljava/lang/Object;IILjava/lang/String;ILjava/lang/Object;)Ljava/lang/Object;" =
      let r := Algorithm.wrapRLEItems items items.size.toUInt32 j line lineLen out
      .inl (some ⟨pc + 1, .ext (.strGrowBuf r) :: rest, locs, jh, hp⟩) := by
  have hfold : (items.map fun x => JvmVal.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2)).foldlM
      (fun acc (v : JvmVal) => match v with
        | .pair a b => some (acc.push (unboxU8 a, unboxI32 b))
        | _ => none) #[] = some items := by
    rw [← Array.foldlM_toList, Array.toList_map, List.foldlM_map]
    have hgen : ∀ (xs : List (UInt8 × UInt32)) (acc : Array (UInt8 × UInt32)),
        xs.foldlM (fun acc x => some (acc.push x)) acc =
          some (acc.toList ++ xs).toArray := by
      intro xs
      induction xs with
      | nil => intro acc; simp
      | cons x xs ih =>
        intro acc
        simp only [List.foldlM_cons, bind, Option.bind_some]
        rw [ih (acc.push x)]
        simp [Array.toList_push, List.append_assoc]
    have h0 := hgen items.toList #[]
    simpa [unboxU8, unboxI32, u8_toUInt32_toUInt8] using h0
  have hfn : stepInvokeStatic ⟨pc, .ext (.strGrowBuf out) :: .i32 lineLen :: .str line ::
      .i32 j :: .i32 items.size.toUInt32 :: .heapRef itemsAddr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_wrapRLEItems-zax99WU"
      "([Ljava/lang/Object;IILjava/lang/String;ILjava/lang/Object;)Ljava/lang/Object;" =
      match jh.get? itemsAddr with
      | some (.objArray _ elems) =>
        match elems.foldlM (fun acc v => match v with
            | .pair a b => some (acc.push (unboxU8 a, unboxI32 b))
            | _ => none) #[] with
        | some items' =>
          .inl (some ⟨pc + 1, .ext (.strGrowBuf
            (Algorithm.wrapRLEItems items' items.size.toUInt32 j line lineLen out)) :: rest,
            locs, jh, hp⟩)
        | none => .inr none
      | _ => .inr none := rfl
  rw [hfn, hget]
  dsimp only
  erw [hfold]

private theorem copyOf_set_push6c {α : Type} [Inhabited α] (xs : Array α) (d : α) (v : α) :
    (Array.ofFn (n := xs.size + 1) (fun i => if h : i.val < xs.size then xs[i.val] else d)).set!
      xs.size v = xs.push v := by
  apply Array.ext
  · simp
  · intro i hi1 hi2
    have hlt_a : i < xs.size + 1 := by simpa using hi2
    simp only [Array.set!] at hi1 ⊢
    rw [Array.getElem_setIfInBounds (hj := by simpa using hlt_a)]
    by_cases heq : xs.size = i
    · subst heq; simp
    · have hlt : i < xs.size := by omega
      simp [Array.getElem_push, hlt]
      intro h; omega

private theorem uint32_slt_zero_false6c (x : UInt32) (hx : x.toNat < 2 ^ 31) :
    x.toBitVec.slt 0#32 = false := by
  cases h : x.toBitVec.slt 0#32
  · rfl
  · rw [BitVec.slt, BitVec.toInt_zero, BitVec.toInt_eq_toNat_cond] at h
    have hbv : x.toBitVec.toNat = x.toNat := rfl
    rw [hbv] at h
    have h2 : 2 * x.toNat < 2 ^ 32 := by omega
    simp only [h2, ↓reduceIte] at h
    rw [decide_eq_true_iff] at h
    omega

theorem serializeRLE_equiv (cells : Array UInt64) (minX maxX minY maxY : Int32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (cId : Nat)
    (hc : hp.u64Arrays[cId]? = some cells)
    (hsz : ((let width := (maxX - minX + 1).toUInt32
             let height := (maxY - minY + 1).toUInt32
             let grid := Algorithm.fillGrid cells minX minY width height Algorithm.rleAlive
               (by decide) 0 cells.size.toUInt32
               (Algorithm.AsciiBytes.replicate (width * height) Algorithm.rleDead (by decide))
             (Algorithm.gridItems grid width (width * height) 0
               Algorithm.rleDead 0 0 Algorithm.GrowBuf.empty).toArray.size + 1) < 2 ^ 31)) :
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_serializeRLE_prog
        { initJvmState [(0, .ext (.u64Ref cId)), (1, .i32 minX.toUInt32),
            (2, .i32 maxX.toUInt32), (3, .i32 minY.toUInt32), (4, .i32 maxY.toUInt32)]
          with jvmHeap := jh, heap := hp } = some st' ∧
      decodeStrArray st'.2 st'.1 = some (Algorithm.serializeRLE cells minX maxX minY maxY) ∧
      (∀ i o, jh.get? i = some o → st'.2.jvmHeap.get? i = some o) := by
  let initSt : JvmState :=
    { initJvmState [(0, .ext (.u64Ref cId)), (1, .i32 minX.toUInt32),
        (2, .i32 maxX.toUInt32), (3, .i32 minY.toUInt32), (4, .i32 maxY.toUInt32)]
      with jvmHeap := jh, heap := hp }
  have hinit : initSt =
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
        0 (.ext (.u64Ref cId))) 1 (.i32 minX.toUInt32)) 2 (.i32 maxX.toUInt32))
        3 (.i32 minY.toUInt32)) 4 (.i32 maxY.toUInt32), jh, hp⟩ := rfl
  by_cases hcz : cells.size.toUInt32 = 0
  · let arrObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
      #[.str "#R 0 0", .str "x = 0, y = 0, rule = B3/S23", .str "!"]
    let res := jh.alloc arrObj
    have hrun : ∃ locsF,
        runJvmRes 12 f_Algorithm_serializeRLE_prog initSt =
          some (.heapRef res.1, ⟨126, [.heapRef res.1], locsF, res.2, hp⟩) := by
      apply Exists.intro _
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      change runJvmResFast 12 f_Algorithm_serializeRLE_prog 0 f_Algorithm_serializeRLE_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
          0 (.ext (.u64Ref cId))) 1 (.i32 minX.toUInt32)) 2 (.i32 maxX.toUInt32))
          3 (.i32 minY.toUInt32)) 4 (.i32 maxY.toUInt32), jh, hp⟩ = _
      conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_serializeRLE_prog)]
      step_drop6c 10
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam6c rfl)]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrSize6c hc)]
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 2
      rw [runJvmResFast_ifeq_branch (by simp [hcz])]; step_drop6c 2
      rw [runJvmResFast_invokestatic_step stepStatic_serializeRLE_closed3_6c]
      rw [runJvmResFast_areturn6c]
      rfl
    rcases hrun with ⟨locsF, hrun⟩
    refine ⟨12, (.heapRef res.1, ⟨126, [.heapRef res.1], locsF, res.2, hp⟩),
      hrun, ?_, fun _ _ hi => HeapExtends_alloc _ hi⟩
    · have hget : res.2.get? res.1 = some arrObj := jvmHeap_get?_alloc_self jh arrObj
      have hcz_b : (cells.size.toUInt32 == 0) = true := beq_iff_eq.mpr hcz
      simp [Algorithm.serializeRLE, hcz_b, decodeStrArray, hget, arrObj]
  · have hcnz : (cells.size.toUInt32 == 0) = false := beq_false_of_ne hcz
    let width : UInt32 := (maxX - minX + 1).toUInt32
    let height : UInt32 := (maxY - minY + 1).toUInt32
    have hw_eq : (maxX.toUInt32 - minX.toUInt32) + 1 = width := by
      cases maxX; cases minX; rfl
    have hh_eq : (maxY.toUInt32 - minY.toUInt32) + 1 = height := by
      cases maxY; cases minY; rfl
    let total := width * height
    let gId := hp.asciiArrays.length
    let g0 := Algorithm.AsciiBytes.replicate total Algorithm.rleDead (by decide)
    let hp1 : AlgHeap := { hp with asciiArrays := hp.asciiArrays ++ [g0] }
    let grid := Algorithm.fillGrid cells minX minY width height Algorithm.rleAlive
      (by decide) 0 cells.size.toUInt32 g0
    let hp2 : AlgHeap := { hp1 with asciiArrays := hp1.asciiArrays.set gId grid }
    let itemsBuf := Algorithm.gridItems grid width total 0 Algorithm.rleDead 0 0 .empty
    let items0 := itemsBuf.toArray
    let elems0 : Array JvmVal :=
      items0.map (fun x => JvmVal.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2))
    let r1 := jh.alloc (.objArray "java/lang/Object" elems0)
    let copied := Array.ofFn (n := items0.size + 1)
      (fun i => if h : i.val < elems0.size then elems0[i.val] else .null)
    let r2 := r1.2.alloc (.objArray "java/lang/Object" copied)
    let finalItems := items0.push (Algorithm.rleEnd, 1)
    let finalElems : Array JvmVal := finalItems.map
      (fun x => JvmVal.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2))
    let jh3 := r2.2.set r2.1 (.objArray "java/lang/Object" finalElems)
    let header := Algorithm.formatRLEHeader minX minY width height
    let r4 := jh3.alloc (.objArray "java/lang/Object" (header.map .str))
    let outInit := Algorithm.GrowBuf.empty.push header[0]! |>.push header[1]!
    let finalOut := Algorithm.wrapRLEItems finalItems finalItems.size.toUInt32 0 "" 0 outInit
    have htot_lt : items0.size + 1 < 2 ^ 31 := by
      simpa [items0, itemsBuf, grid, g0, total, width, height] using hsz
    have htonat1 : (items0.size.toUInt32 + 1).toNat = items0.size + 1 := by
      have h1 : (1 : UInt32).toNat = 1 := rfl
      have h2 : items0.size.toUInt32.toNat = items0.size := by
        simp [Nat.toUInt32, Nat.mod_eq_of_lt (by omega : items0.size < 2 ^ 32)]
      rw [UInt32.toNat_add, h1, h2, Nat.mod_eq_of_lt (by omega)]
    have hslt0 : (items0.size.toUInt32 + 1).toBitVec.slt 0#32 = false :=
      uint32_slt_zero_false6c _ (by rw [htonat1]; omega)
    have hcopy_eq : copied.set! items0.size (.pair (.boxedUByte 33) (.boxedUInt 1)) = finalElems := by
      have hsz_e : elems0.size = items0.size := by simp [elems0]
      have hofn : copied = Array.ofFn (n := elems0.size + 1)
          (fun i => if h : i.val < elems0.size then elems0[i.val] else .null) := by
        apply Array.ext
        · simp [copied, hsz_e]
        · intro i hi1 hi2
          simp [copied]
      rw [hofn, ← hsz_e, copyOf_set_push6c]
      simp [finalElems, finalItems, elems0, Array.map_push, Algorithm.rleEnd]
    have hset_jh3 : jh3 = (r2.2.set r2.1 (.objArray "java/lang/Object"
        (copied.set! elems0.size (.pair (.boxedUByte 33) (.boxedUInt 1))))) := by
      have hsz_e : elems0.size = items0.size := by simp [elems0]
      rw [hsz_e, hcopy_eq]
    have hget_g0 : hp1.asciiArrays[gId]? = some g0 := by simp [hp1, gId]
    have hget_grid : hp2.asciiArrays[gId]? = some grid := by
      simp [hp2, hp1, gId]
    have hget_r1 : r1.2.get? r1.1 = some (.objArray "java/lang/Object" elems0) :=
      jvmHeap_get?_alloc_self _ _
    have hget_r2 : r2.2.get? r2.1 = some (.objArray "java/lang/Object" copied) :=
      jvmHeap_get?_alloc_self _ _
    have hget_r1_after_r2 : r2.2.get? r1.1 = some (.objArray "java/lang/Object" elems0) :=
      HeapExtends_alloc _ hget_r1
    have hget_jh3_r1 : jh3.get? r1.1 = some (.objArray "java/lang/Object" elems0) := by
      have hne : r1.1 ≠ r2.1 := by
        have hlt : r1.1 < r1.2.objects.size := (Array.getElem?_eq_some_iff.mp hget_r1).1
        have heq : r2.1 = r1.2.objects.size := rfl
        omega
      have hlt2 : r2.1 < r2.2.objects.size := (Array.getElem?_eq_some_iff.mp hget_r2).1
      simp only [jh3, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, hlt2, ↓reduceDIte]
      rw [Array.getElem?_set]
      simp only [hne.symm, ↓reduceIte]
      exact hget_r1_after_r2
    have hget_jh3_r2 : jh3.get? r2.1 = some (.objArray "java/lang/Object" finalElems) :=
      jvmHeap_get?_set_self hget_r2
    have hget_r4_r2 : r4.2.get? r2.1 = some (.objArray "java/lang/Object" finalElems) :=
      HeapExtends_alloc _ hget_jh3_r2
    have hget_r4_r4 : r4.2.get? r4.1 = some (.objArray "java/lang/Object" (header.map JvmVal.str)) :=
      jvmHeap_get?_alloc_self _ _
    have hhdr_sz : (header.map (JvmVal.str : String → JvmVal)).size = 2 := by
      rw [Array.size_map]; dsimp only [header, Algorithm.formatRLEHeader]; rfl
    suffices hrun : ∃ locs',
        runJvmRes 130 f_Algorithm_serializeRLE_prog initSt =
          some (.strArr finalOut.toArray, ⟨124, [.strArr finalOut.toArray], locs', r4.2, hp2⟩) by
      obtain ⟨locs', hrun⟩ := hrun
      refine ⟨130, (.strArr finalOut.toArray, ⟨124, [.strArr finalOut.toArray], locs', r4.2, hp2⟩),
          hrun, ?_, ?_⟩
      · simp only [decodeStrArray, Algorithm.serializeRLE, hcnz]
        rfl
      · intro i o hi
        have h12 : r2.2.get? i = some o := HeapExtends_alloc _ (HeapExtends_alloc _ hi)
        have hlt_jh : i < jh.objects.size := (Array.getElem?_eq_some_iff.mp hi).1
        have hne : i ≠ r2.1 := by
          have hlt1 : jh.objects.size < r1.2.objects.size := by simp [r1, Jvm.JvmHeap.alloc]
          have heq : r2.1 = r1.2.objects.size := rfl
          omega
        have h23 : jh3.get? i = some o := by
          have hlt2 : r2.1 < r2.2.objects.size := (Array.getElem?_eq_some_iff.mp hget_r2).1
          simp only [jh3, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, hlt2, ↓reduceDIte]
          rw [Array.getElem?_set]
          simp only [hne.symm, ↓reduceIte]
          exact h12
        exact HeapExtends_alloc _ h23
    · apply Exists.intro
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      change runJvmResFast 130 f_Algorithm_serializeRLE_prog 0 f_Algorithm_serializeRLE_prog initSt = _
      rw [hinit]
      conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_serializeRLE_prog)]
      step_drop6c 10
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam6c rfl)]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrSize6c hc)]
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 2
      rw [runJvmResFast_ifeq_fallthrough hcnz]
      step_drop6c 24
      step_res_plain 16
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 3
      dsimp only [Jvm.JvmVal.asI32]
      rw [hw_eq, hh_eq]
      rw [runJvmResFast_invokestatic_step (stepStatic_asciiBytesReplicate6c (by decide))]
      step_drop6c 26
      step_res_plain 5
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 4
      rw [show (111 : UInt32) = (Algorithm.rleAlive : UInt8).toUInt32 from rfl]
      have hc1 : hp1.u64Arrays[cId]? = some cells := hc
      have hhp1 : ({ hp with asciiArrays := hp.asciiArrays ++
          [Algorithm.AsciiBytes.replicate (width * height) (UInt32.toUInt8 98) (by decide)] } :
          AlgHeap) = hp1 := rfl
      rw [hhp1]
      rw [runJvmResFast_invokestatic_step (stepStatic_fillGrid6c hc1 hget_g0 (by decide))]
      have hhp2 : ({ hp1 with asciiArrays := hp1.asciiArrays.set gId (Algorithm.fillGrid cells
          minX minY width height Algorithm.rleAlive (by decide) 0 cells.size.toUInt32 g0) } :
          AlgHeap) = hp2 := rfl
      rw [hhp2]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_growBufEmpty6c]
      step_res_plain 3
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 6
      rw [show (98 : UInt32) = (Algorithm.rleDead : UInt8).toUInt32 from rfl]
      rw [runJvmResFast_invokestatic_step (stepStatic_gridItems6c hget_grid
        (U8U32PairRep6c.empty _ rfl rfl))]
      step_drop6c 15
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_u8u32_6c]
      have helems_eq : Array.map (fun x => JvmVal.pair (.boxedUByte x.1.toUInt32) (.boxedUInt x.2))
          (Algorithm.gridItems grid width (width * height) 0 Algorithm.rleDead 0 0
            Algorithm.GrowBuf.empty).toArray = elems0 := rfl
      have hr1_1 : (Jvm.JvmVal.heapRef jh.objects.size : JvmVal) = .heapRef r1.1 := rfl
      have hr1_2 : Jvm.JvmHeap.mk (jh.objects.push (.objArray "java/lang/Object" elems0))
          jh.statics = r1.2 := rfl
      rw [helems_eq, hr1_1, hr1_2]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_serializeRLE_closed0_6c]
      step_res_plain 3
      rw [runJvmResFast_arraylength_obj hget_r1]
      step_res_plain 2
      dsimp only [Jvm.JvmVal.asI32]
      have hlen_e : elems0.size = items0.size := by simp [elems0]
      rw [hlen_e]
      rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf6c hget_r1 hslt0)]
      rw [htonat1]
      have hcopied_eq : Array.ofFn (n := items0.size + 1)
          (fun i => if h : i.val < elems0.size then elems0[i.val] else .null) = copied := rfl
      have hr2_1 : (Jvm.JvmVal.heapRef r1.2.objects.size : JvmVal) = .heapRef r2.1 := rfl
      have hr2_2 : Jvm.JvmHeap.mk (r1.2.objects.push (.objArray "java/lang/Object" copied))
          r1.2.statics = r2.2 := rfl
      rw [hcopied_eq, hr2_1, hr2_2]
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullExpr6c rfl)]
      step_drop6c 19
      step_res_plain 7
      rw [runJvmResFast_arraylength_obj hget_r1_after_r2]
      step_res_plain 1
      have hlt_lt : elems0.size < 2 ^ 31 := by omega
      have htonat_e : elems0.size.toUInt32.toNat = elems0.size := by
        simp [Nat.toUInt32, Nat.mod_eq_of_lt (by omega : elems0.size < 2 ^ 32)]
      have hslt_idx : elems0.size.toUInt32.toBitVec.slt 0#32 = false :=
        uint32_slt_zero_false6c _ (by rw [htonat_e]; exact hlt_lt)
      have htonat_idx : elems0.size.toUInt32.toNat < copied.size := by
        rw [htonat_e]
        simp [copied, hlen_e]
      rw [runJvmResFast_aastore hget_r2 hslt_idx htonat_idx]
      have hset_aastore : (r2.2.set r2.1 (.objArray "java/lang/Object"
          (copied.set elems0.size.toUInt32.toNat
            (.pair (.boxedUByte 33) (.boxedUInt 1)) htonat_idx))) = jh3 := by
        rw [hset_jh3]
        have hce : copied.set elems0.size.toUInt32.toNat
            (.pair (.boxedUByte 33) (.boxedUInt 1)) htonat_idx =
            copied.set! elems0.size (.pair (.boxedUByte 33) (.boxedUInt 1)) := by
          have he_lt : elems0.size < copied.size := by simpa [htonat_e] using htonat_idx
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, he_lt, ↓reduceDIte]
          have hset_congr : ∀ {i j : Nat} (hi : i < copied.size) (hj : j < copied.size),
              i = j → copied.set i (.pair (.boxedUByte 33) (.boxedUInt 1)) hi =
                copied.set j (.pair (.boxedUByte 33) (.boxedUInt 1)) hj := by
            rintro i _ hi hj rfl; rfl
          exact hset_congr htonat_idx he_lt htonat_e
        rw [hce]
      rw [hset_aastore]
      step_res_plain 5
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 1
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      rw [runJvmResFast_invokestatic_step stepStatic_formatRLEHeader6c]
      have hhdr_eq : Algorithm.formatRLEHeader minX minY width height = header := rfl
      have hr4_1 : (Jvm.JvmVal.heapRef jh3.objects.size : JvmVal) = .heapRef r4.1 := rfl
      have hr4_2 : Jvm.JvmHeap.mk (jh3.objects.push (.objArray "java/lang/Object" (header.map .str)))
          jh3.statics = r4.2 := rfl
      rw [hhdr_eq, hr4_1, hr4_2]
      step_drop6c 19
      step_res_plain 2
      rw [runJvmResFast_arraylength_obj hget_r4_r2]
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6c]
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step stepStatic_growBufEmpty6c]
      step_res_plain 4
      rw [runJvmResFast_aaload hget_r4_r4 (by decide) (by rw [hhdr_sz]; decide)]
      rw [Array.getElem_map]
      simp only [UInt32.toNat_zero]
      rw [runJvmResFast_invokestatic_step stepStatic_growBufPush_str]
      step_res_plain 4
      rw [runJvmResFast_aaload hget_r4_r4 (by decide) (by rw [hhdr_sz]; decide)]
      rw [Array.getElem_map]
      have h1_u32 : (1 : UInt32).toNat = 1 := rfl
      simp only [h1_u32]
      rw [runJvmResFast_invokestatic_step stepStatic_growBufPush_str]
      step_drop6c 12
      step_res_plain 7
      have h0 : 0 < header.size := by simp at hhdr_sz; omega
      have h1 : 1 < header.size := by simp at hhdr_sz; omega
      have hsz_fe : UInt32.ofNat finalElems.size = finalItems.size.toUInt32 := by
        simp [Nat.toUInt32, finalElems, finalItems]
      have hout : (Algorithm.GrowBuf.empty.push header[0]).push header[1] = outInit := by
        simp only [outInit, getElem!_pos header 0 h0, getElem!_pos header 1 h1]
      rw [hsz_fe, hout]
      rw [runJvmResFast_invokestatic_step (stepStatic_wrapRLEItems6c hget_r4_r2)]
      step_res_plain 2
      rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_str6c]
      rw [runJvmResFast_areturn6c]

end Algorithm.JvmVerification
