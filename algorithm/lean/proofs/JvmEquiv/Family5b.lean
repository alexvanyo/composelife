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
import JvmSemantics
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt

namespace Algorithm.JvmVerification

open Algorithm.JvmBytecode

/-! ### Shared local stepping & arithmetic helpers -/

private theorem runJvm_eq_of_runJvmRes {fuel : Nat} {prog : List JvmInstr}
    {st st' : JvmState} {v : JvmVal}
    (h : runJvmRes fuel prog st = some (v, st')) :
    runJvm fuel prog st = some v := by
  rw [runJvm_eq_runJvmRes, h]
  rfl

private theorem list_drop_step {n : Nat} {l : List JvmInstr} {a : JvmInstr} {as : List JvmInstr}
    (h : l.drop n = a :: as) :
    l.drop (n + 1) = as := by
  induction n generalizing l with
  | zero => simp only [List.drop_zero] at h; simp [h]
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons _ xs => exact ih h

open Lean Elab Tactic in
local elab "step_drop " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic|
      (conv => lhs; arg 4; rw [list_drop_step rfl]; try simp only [Nat.reduceAdd])))

private theorem runJvmResFast_step_nonbranch_nonret {f pc : Nat} {prog : List JvmInstr}
    {instr : JvmInstr} {rest : List JvmInstr}
    {pc0 : Nat} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hbr : Jvm.isBranchInstr instr = false)
    (hi2l : instr ≠ .i2l)
    (hstep : Jvm.stepInstr algHooks instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩)) :
    runJvmResFast (f + 1) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩ := by
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := hbr) (hno := fun h => hi2l h.1)]
  simp only [hstep, ↓reduceIte]

private theorem setLocal_ne_eq {Ext} {locs : Nat → Jvm.JvmVal Ext} {i j : Nat} {v : Jvm.JvmVal Ext}
    (h : decide (j = i) = false) : Jvm.setLocal locs i v j = locs j := by
  dsimp [Jvm.setLocal]; simp [of_decide_eq_false h]

private theorem setLocal_eq_val {Ext} {locs : Nat → Jvm.JvmVal Ext} {i j : Nat} {v : Jvm.JvmVal Ext}
    (h : decide (j = i) = true) : Jvm.setLocal locs i v j = v := by
  dsimp [Jvm.setLocal]; simp [of_decide_eq_true h]

private theorem runJvmResFast_areturn {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stkRest, locs, jh, hp⟩) := rfl

private theorem step1_helper {f' k pc : Nat} {prog : List JvmInstr} {instr : JvmInstr}
    {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hk : 1 ≤ k)
    (hbr : Jvm.isBranchInstr instr = false) (hi2l : instr ≠ .i2l)
    (hstep : Jvm.stepInstr algHooks instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩)) :
    runJvmResFast (f' + k) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f' + (k - 1)) prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩ := by
  rw [show f' + k = (f' + (k - 1)) + 1 from by omega]
  exact runJvmResFast_step_nonbranch_nonret hbr hi2l hstep

private theorem step1_load_helper {f' k pc idx : Nat} {prog : List JvmInstr} {instr : JvmInstr}
    {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hk : 1 ≤ k)
    (hi : instr = .aload idx ∨ instr = .iload idx ∨ instr = .lload idx)
    (hloc : locs idx = v) :
    runJvmResFast (f' + k) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f' + (k - 1)) prog (pc + 1) rest ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  rcases hi with rfl | rfl | rfl <;>
    exact step1_helper hk rfl (by intro h; cases h) (by unfold Jvm.stepInstr; dsimp only; rw [hloc])

local macro "step1_load" k:num v:term "," hloc:term : tactic => `(tactic| (
  rw [step1_load_helper (idx := $k) (v := $v) (by decide) (by simp) $hloc]
  (try (conv => lhs; arg 3; simp only [Nat.reduceAdd]))
  (try (conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]))
  (try (conv => lhs; arg 1; simp only [Nat.reduceSub, Nat.add_zero]))))

local macro "step1" : tactic => `(tactic| (
  rw [step1_helper (by decide) rfl (by intro h; cases h) rfl]
  (try (conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
    Jvm.JvmState.jvmHeap, Jvm.JvmState.heap, Jvm.JvmVal.asI32?]))
  (try (conv => lhs; arg 3; simp only [Nat.reduceAdd]))
  (try (conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]))
  (repeat (first
    | (conv => lhs; arg 5; arg 2; rw [setLocal_eq_val rfl])
    | (conv => lhs; arg 5; arg 2; rw [setLocal_ne_eq rfl])))
  (try (conv => lhs; arg 1; simp only [Nat.reduceSub, Nat.add_zero]))))

private theorem stepStatic_compareUnsigned
    {pc : Nat} {a b : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_u32_constructor
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_i2c {f pc : Nat} {prog rest : List JvmInstr} {pc0 : Nat}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.i2c :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (v &&& 65535) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
    (by unfold Jvm.stepInstr; rfl)

private theorem runJvmResFast_checkNotNullParameter {f pc : Nat} {prog rest : List JvmInstr}
    {pc0 : Nat} {msg obj : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnull : obj.isNull = false) :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, msg :: obj :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  cases hp
  exact stepStatic_checkNotNullParameter hnull

private theorem runJvmResFast_if_icmpge_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.sle a.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.if_icmpge tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl), evalResBranchInstrCons_if_icmpge, h]
  rfl

private theorem runJvmResFast_if_icmple_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : a.toBitVec.sle b.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.if_icmple tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl), evalResBranchInstrCons_if_icmple, h]
  rfl

private theorem i32_slt_eq_toString (v : UInt32) (hv : v.toNat < 2 ^ 31) :
    Jvm.i32ToDecimalString v = toString v := by
  rw [i32ToDecimalString_eq_toString]
  have hnat : v.toInt32.toInt = (v.toNat : Int) := by
    have h1 : v.toInt32.toInt = v.toBitVec.toInt := rfl
    rw [h1, BitVec.toInt]
    have h2 : 2 * v.toNat < 2 ^ 32 := by omega
    simp [h2]
  change Int.repr v.toInt32.toInt = toString v.toNat
  rw [hnat]
  rfl

private theorem evalConcat_str_str {a b : String} :
    @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01"
      "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;" [.str b, .str a] =
      some (a ++ (b ++ ""), []) := rfl

private theorem runJvmResFast_invokedynamic_concat2 {f pc : Nat} {prog rest : List JvmInstr}
    {pc0 : Nat} {a b : String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokedynamic "makeConcatWithConstants" "\x01\x01"
          "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;" :: rest)
        ⟨pc0, .str b :: .str a :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .str (a ++ b) :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rw [show Jvm.stepInstr algHooks
      (.invokedynamic "makeConcatWithConstants" "\x01\x01"
        "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      ⟨pc, .str b :: .str a :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str (a ++ (b ++ "")) :: stkRest, locs, jh, hp⟩) from rfl]
  simp [String.append_empty]

private theorem str_push_eq (s : String) (c : Char) :
    s ++ (String.singleton c ++ "") = s.push c := by
  rw [String.append_empty, ← String.push_eq_append]

/-- `s + c` for the cell characters `'*'` (42) / `'.'` (46). A `char` concatenation only evaluates for
non-surrogate code units, so the step is stated for the two concrete codes the loop emits. -/
private theorem runJvmResFast_invokedynamic_concat_char (b : Bool) {f pc : Nat} {prog rest : List JvmInstr}
    {pc0 : Nat} {s : String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokedynamic "makeConcatWithConstants" "\x01\x01"
          "(Ljava/lang/String;C)Ljava/lang/String;" :: rest)
        ⟨pc0, .i32 (if b then 42 else 46) :: .str s :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .str (s.push (if b then '*' else '.')) :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rw [← str_push_eq]
  cases b <;> rfl

/-! ### serializeMacrocell___closed__2 -/

theorem serializeMacrocell___closed__2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    let (_, h1) := jh.alloc (.objArray "java/lang/Object" #[])
    let emptyArr := Array.ofFn (n := 1) fun (i : Fin 1) =>
      if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null
    let (_, h2) := h1.alloc (.objArray "java/lang/Object" emptyArr)
    let h3 := h2.set h1.objects.size (.objArray "java/lang/Object"
      (emptyArr.set 0 (.str Algorithm.macrocellHeader) (by decide)))
    ∃ st',
      runJvmRes 40 f_Algorithm_serializeMacrocell___closed__2_prog
          ⟨0, [], fun _ => .null, jh, hp⟩ =
        some (.heapRef h1.objects.size, st') ∧
      st'.jvmHeap = h3 ∧ st'.heap = hp := by
  let h1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let emptyArr : Array JvmVal := Array.ofFn (n := 1) fun (i : Fin 1) =>
    if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null
  let h2 := (h1.alloc (.objArray "java/lang/Object" emptyArr)).2
  let h3 := h2.set h1.objects.size (.objArray "java/lang/Object"
    (emptyArr.set 0 (.str Algorithm.macrocellHeader) (by decide)))
  have hrun : runJvmRes 40 f_Algorithm_serializeMacrocell___closed__2_prog
      ⟨0, [], fun _ => .null, jh, hp⟩ =
      some (.heapRef h1.objects.size,
        ⟨25, [.heapRef h1.objects.size],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.str "[M2] (ComposeLife 1.0)")) 1 (.heapRef jh.objects.size))
            2 (.heapRef h1.objects.size)) 3 (.heapRef h1.objects.size)) 4 (.i32 0),
          h3, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 40 _ _ _ rfl
    rw [show (40 : Nat) = 10 + 30 from rfl]
    dsimp only [f_Algorithm_serializeMacrocell___closed__2_prog]
    step1; step1; step1
    rw [show (10 + 27 : Nat) = 36 + 1 from rfl]
    rw [runJvmResFast_anewarray_obj (by decide)]
    have hrep0 : Array.replicate (0 : UInt32).toNat (JvmVal.null : JvmVal) = #[] := rfl
    rw [hrep0]
    rw [show (36 : Nat) = 10 + 26 from rfl]
    step1; step1; step1
    have hget0 : h1.get? jh.objects.size = some (.objArray "java/lang/Object" #[]) :=
      jvmHeap_get?_alloc_self _ _
    rw [show (10 + 23 : Nat) = 32 + 1 from rfl]
    rw [runJvmResFast_arraylength_obj hget0]
    rw [show (32 : Nat) = 10 + 22 from rfl]
    step1; step1
    rw [show (10 + 20 : Nat) = 29 + 1 from rfl]
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) hget0)]
    rw [show (29 : Nat) = 10 + 19 from rfl]
    step1; step1; step1; step1; step1; step1; step1; step1; step1; step1
    rw [show (10 + 9 : Nat) = 18 + 1 from rfl]
    rw [runJvmResFast_arraylength_obj (by
      rw [jvmHeap_get?_alloc_lt _ _ (by simp [h1, Jvm.JvmHeap.alloc])]
      exact hget0)]
    rw [show (18 : Nat) = 10 + 8 from rfl]
    step1
    rw [show (UInt32.ofNat (#[] : Array JvmVal).size) = 0 from rfl]
    have hget1 : h2.get? h1.objects.size = some (.objArray "java/lang/Object" emptyArr) :=
      jvmHeap_get?_alloc_self _ _
    dsimp only [h2, emptyArr] at hget1
    rw [show (10 + 7 : Nat) = 16 + 1 from rfl]
    have haas : runJvmResFast (16 + 1) f_Algorithm_serializeMacrocell___closed__2_prog 23
        (f_Algorithm_serializeMacrocell___closed__2_prog.drop 23)
        ⟨23, [.str "[M2] (ComposeLife 1.0)", .i32 0, .heapRef h1.objects.size],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.str "[M2] (ComposeLife 1.0)")) 1 (.heapRef jh.objects.size))
            2 (.heapRef h1.objects.size)) 3 (.heapRef h1.objects.size)) 4 (.i32 0),
          h2, hp⟩ =
        runJvmResFast 16 f_Algorithm_serializeMacrocell___closed__2_prog 24
          [.aload 2, .areturn]
          ⟨24, [],
            setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
              0 (.str "[M2] (ComposeLife 1.0)")) 1 (.heapRef jh.objects.size))
              2 (.heapRef h1.objects.size)) 3 (.heapRef h1.objects.size)) 4 (.i32 0),
            h3, hp⟩ := by
      dsimp only [f_Algorithm_serializeMacrocell___closed__2_prog, List.drop]
      exact runJvmResFast_aastore (idx := 0) hget1 (by decide) (by decide)
    refine haas.trans ?_
    rw [show (16 : Nat) = 10 + 6 from rfl]
    step1
    exact runJvmResFast_areturn
  exact ⟨_, hrun, rfl, rfl⟩

/-! ### formatMacrocellNode -/

private abbrev fmConcatDesc : String :=
  "(Ljava/lang/String;Ljava/lang/String;ILjava/lang/String;ILjava/lang/String;ILjava/lang/String;I)Ljava/lang/String;"

theorem formatMacrocellNode_equiv (lvl nw ne sw se : UInt32)
    (hlvl : lvl.toNat < 2 ^ 31) (hnw : nw.toNat < 2 ^ 31)
    (hne : ne.toNat < 2 ^ 31) (hsw : sw.toNat < 2 ^ 31) (hse : se.toNat < 2 ^ 31)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 25 f_Algorithm_formatMacrocellNode_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
          0 (.i32 lvl)) 1 (.i32 nw)) 2 (.i32 ne)) 3 (.i32 sw)) 4 (.i32 se), jh, hp⟩ =
      some (.str (Algorithm.formatMacrocellNode lvl nw ne sw se)) := by
  have hconcat : @Jvm.evalMakeConcatWithConstants AlgExt
      "\x01\x01\x01\x01\x01\x01\x01\x01\x01" fmConcatDesc
      [.i32 se, .str " ", .i32 sw, .str " ", .i32 ne, .str " ", .i32 nw, .str " ",
        .str (Jvm.i32ToDecimalString lvl)] =
      some (Jvm.i32ToDecimalString lvl ++ (" " ++ (Jvm.i32ToDecimalString nw ++
        (" " ++ (Jvm.i32ToDecimalString ne ++ (" " ++ (Jvm.i32ToDecimalString sw ++
          (" " ++ (Jvm.i32ToDecimalString se ++ "")))))))), []) := rfl
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
    0 (.i32 lvl)) 1 (.i32 nw)) 2 (.i32 ne)) 3 (.i32 sw)) 4 (.i32 se)
  let locs1 := setLocal (setLocal locs0 5 (.str (Jvm.i32ToDecimalString lvl))) 6 (.str " ")
  let resStr := Jvm.i32ToDecimalString lvl ++ (" " ++ (Jvm.i32ToDecimalString nw ++
    (" " ++ (Jvm.i32ToDecimalString ne ++ (" " ++ (Jvm.i32ToDecimalString sw ++
      (" " ++ Jvm.i32ToDecimalString se)))))))
  have hres : runJvmRes 25 f_Algorithm_formatMacrocellNode_prog ⟨0, [], locs0, jh, hp⟩ =
      some (.str resStr, ⟨15, [.str resStr], locs1, jh, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 25 _ _ _ rfl
    rw [show (25 : Nat) = 10 + 15 from rfl]
    dsimp only [f_Algorithm_formatMacrocellNode_prog, locs0]
    step1
    rw [show (10 + 14 : Nat) = 23 + 1 from rfl]
    rw [runJvmResFast_invokestatic_step stepStatic_stringValueOfInt]
    rw [show (23 : Nat) = 10 + 13 from rfl]
    step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1
    have hinv : Jvm.stepInstr algHooks
        (.invokedynamic "makeConcatWithConstants" "\x01\x01\x01\x01\x01\x01\x01\x01\x01"
          fmConcatDesc)
        ⟨14, [.i32 se, .str " ", .i32 sw, .str " ", .i32 ne, .str " ", .i32 nw, .str " ",
          .str (Jvm.i32ToDecimalString lvl)], locs1, jh, hp⟩ =
        .inl (some ⟨15, [.str resStr], locs1, jh, hp⟩) := by
      unfold Jvm.stepInstr
      dsimp only
      rw [hconcat]
      simp [resStr, String.append_empty]
    dsimp only [fmConcatDesc] at hinv
    rw [show (10 + 1 : Nat) = (9 + 1) + 1 from rfl]
    rw [runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) hinv]
    exact runJvmResFast_areturn
  have heq : resStr = Algorithm.formatMacrocellNode lvl nw ne sw se := by
    simp only [resStr, i32_slt_eq_toString lvl hlvl, i32_slt_eq_toString nw hnw,
      i32_slt_eq_toString ne hne, i32_slt_eq_toString sw hsw, i32_slt_eq_toString se hse,
      Algorithm.formatMacrocellNode, String.append_assoc]
    rfl
  rw [← heq]
  exact runJvm_eq_of_runJvmRes hres

/-! ### formatLeafRow_loop & formatLeafRow -/

private theorem runJvmResFast_load_step {f pc : Nat} {prog : List JvmInstr}
    {k : Nat} {v : JvmVal} {instr : JvmInstr} {rest : List JvmInstr}
    {pc0 : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hi : instr = .aload k ∨ instr = .iload k ∨ instr = .lload k)
    (hk : locs k = v) :
    runJvmResFast (f + 1) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  rcases hi with rfl | rfl | rfl <;>
    exact runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) (by unfold Jvm.stepInstr; dsimp only; rw [hk])

private theorem stepStatic_leafContains
    {pc : Nat} {leaf : UInt64} {x y : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_leafContains-fMEO4hA" "(JII)Z" =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.leafContains leaf x y then 1 else 0) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_findLastLeafX
    {pc : Nat} {leaf : UInt64} {y : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 y :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_findLastLeafX-8GdB7C8" "(JI)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1,
        (match Algorithm.findLastLeafX leaf y with | some v => .boxedUInt v | none => .null) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_formatLeafRow_loop
    {pc : Nat} {leaf : UInt64} {y x limit : UInt32} {acc : String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic
      ⟨pc, .str acc :: .i32 limit :: .i32 x :: .i32 y :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_formatLeafRow_loop-L5XE2Go"
      "(JIIILjava/lang/String;)Ljava/lang/String;" =
      .inl (some ⟨pc + 1,
        .str (Algorithm.formatLeafRow.loop leaf y x limit acc) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_findLastLeafRow
    {pc : Nat} {leaf : UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_findLastLeafRow-VKZWuLQ" "(J)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1,
        (match Algorithm.findLastLeafRow leaf with | some v => .boxedUInt v | none => .null) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_formatLeafRow
    {pc : Nat} {leaf : UInt64} {y : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 y :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_formatLeafRow-8GdB7C8" "(JI)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.formatLeafRow leaf y) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_formatLeafNode_loop
    {pc : Nat} {leaf : UInt64} {y limit : UInt32} {acc : String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic
      ⟨pc, .str acc :: .i32 limit :: .i32 y :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_formatLeafNode_loop-9LuH6mI"
      "(JIILjava/lang/String;)Ljava/lang/String;" =
      .inl (some ⟨pc + 1,
        .str (Algorithm.formatLeafNode.loop leaf y limit acc) :: rest, locs, jh, hp⟩) := rfl

private theorem formatLeafRow_loop_aux (n : Nat) :
    ∀ (leaf : UInt64) (y x limit : UInt32) (acc : String)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      locs 0 = .i64 leaf → locs 2 = .i32 y → locs 3 = .i32 x →
      locs 4 = .i32 limit → locs 5 = .str acc →
      limit.toNat - x.toNat ≤ n →
      ∃ f locs',
        runJvmResFast f f_Algorithm_formatLeafRow_loop_prog 3
          (f_Algorithm_formatLeafRow_loop_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
          some (.str (Algorithm.formatLeafRow.loop leaf y x limit acc),
            ⟨10, [.str (Algorithm.formatLeafRow.loop leaf y x limit acc)], locs', jh, hp⟩) := by
  have step_exit : ∀ (leaf : UInt64) (y x limit : UInt32) (acc : String)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      locs 3 = .i32 x → locs 4 = .i32 limit → locs 5 = .str acc → ¬(x < limit) →
      ∃ locs',
        runJvmResFast 8 f_Algorithm_formatLeafRow_loop_prog 3
          (f_Algorithm_formatLeafRow_loop_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
          some (.str acc, ⟨10, [.str acc], locs', jh, hp⟩) := by
    intro leaf y x limit acc locs jh hp h3 h4 h5 hge
    refine ⟨setLocal locs 6 (.i32 0), ?_⟩
    conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 3 =
      [.iconst 0, .istore 6, .iload 3, .iload 4,
        .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 11,
        .aload 5, .areturn] ++ f_Algorithm_formatLeafRow_loop_prog.drop 11 from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [show (8 : Nat) = 0 + 8 from rfl]
    step1; step1
    rw [show (0 + 6 : Nat) = 5 + 1 from rfl]
    rw [runJvmResFast_load_step (k := 3) (v := .i32 x) (Or.inr (Or.inl rfl)) (by simp [setLocal, h3])]
    rw [show (5 : Nat) = 4 + 1 from rfl]
    rw [runJvmResFast_load_step (k := 4) (v := .i32 limit) (Or.inr (Or.inl rfl)) (by simp [setLocal, h4])]
    rw [show (4 : Nat) = 3 + 1 from rfl]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    have hflt : (if x == limit then (0 : UInt32) else if x < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    rw [show (3 : Nat) = 2 + 1 from rfl]
    rw [runJvmResFast_iflt_fallthrough hflt]
    rw [show (2 : Nat) = 1 + 1 from rfl]
    rw [runJvmResFast_load_step (k := 5) (v := .str acc) (Or.inl rfl) (by simp [setLocal, h5])]
    exact runJvmResFast_areturn
  induction n with
  | zero =>
    intro leaf y x limit acc locs jh hp _ _ h3 h4 h5 hn
    have hge : ¬(x < limit) := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [Algorithm.formatLeafRow.loop.eq_1]
    simp only [hge, ↓reduceDIte]
    obtain ⟨locs', hrun⟩ := step_exit leaf y x limit acc locs jh hp h3 h4 h5 hge
    exact ⟨8, locs', hrun⟩
  | succ n ih =>
    intro leaf y x limit acc locs jh hp h0 h2 h3 h4 h5 hn
    by_cases hlt : x < limit
    · have hsub : limit.toNat - (x + 1).toNat ≤ n := by
        have h1 := UInt32.lt_iff_toNat_lt.mp hlt
        rw [ui32_add1_toNat hlt]
        omega
      let ch := if Algorithm.leafContains leaf x y then '*' else '.'
      let chCode : UInt32 := if Algorithm.leafContains leaf x y then 42 else 46
      let acc' := acc.push ch
      let locsEnd :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal locs 6 (.i32 0))
            7 (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)))
            6 (.i32 chCode)) 7 (.i64 leaf)) 9 (.i32 y)) 10 (.i32 (x + 1)))
          11 (.i32 limit)) 13 (.i32 0)) 14 (.i32 chCode)) 12 (.str acc')) 0 (.i64 leaf))
          2 (.i32 y)) 3 (.i32 (x + 1))) 4 (.i32 limit)) 5 (.str acc')
      obtain ⟨fRec, locs', hrec⟩ := ih leaf y (x + 1) limit acc' locsEnd jh hp
        (by simp [locsEnd, setLocal]) (by simp [locsEnd, setLocal])
        (by simp [locsEnd, setLocal]) (by simp [locsEnd, setLocal])
        (by simp [locsEnd, setLocal]) hsub
      rw [Algorithm.formatLeafRow.loop.eq_1]
      simp only [hlt, ↓reduceDIte]
      refine ⟨if Algorithm.leafContains leaf x y then fRec + 56 else fRec + 57, locs', ?_⟩
      -- Step pc 3..11 (head check, branch to 11)
      rw [show (if Algorithm.leafContains leaf x y = true then fRec + 56 else fRec + 57) =
        (if Algorithm.leafContains leaf x y = true then fRec + 50 else fRec + 51) + 6 from by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [hc]]
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 3 =
        [.iconst 0, .istore 6, .iload 3, .iload 4,
          .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 11] ++
          f_Algorithm_formatLeafRow_loop_prog.drop 9 from rfl]
      simp only [List.cons_append, List.nil_append]
      step1; step1
      rw [runJvmResFast_load_step (k := 3) (v := .i32 x) (Or.inr (Or.inl rfl)) (by simp [setLocal, h3])]
      rw [runJvmResFast_load_step (k := 4) (v := .i32 limit) (Or.inr (Or.inl rfl)) (by simp [setLocal, h4])]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      have hflt : (if x == limit then (0 : UInt32) else if x < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          true := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
      rw [runJvmResFast_iflt_branch hflt]
      -- Now at pc 11; slice 11..23: leafContains branch
      rw [show (if Algorithm.leafContains leaf x y = true then fRec + 50 else fRec + 51) =
        (if Algorithm.leafContains leaf x y = true then fRec + 45 else fRec + 46) + 5 from by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [hc]]
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 11 =
        [.lload 0, .iload 3, .iload 2,
          .invokestatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_leafContains-fMEO4hA" "(JII)Z", .istore 7] ++
          f_Algorithm_formatLeafRow_loop_prog.drop 16 from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_load_step (k := 0) (v := .i64 leaf) (Or.inr (Or.inr rfl)) (by simp [setLocal, h0])]
      rw [runJvmResFast_load_step (k := 3) (v := .i32 x) (Or.inr (Or.inl rfl)) (by simp [setLocal, h3])]
      rw [runJvmResFast_load_step (k := 2) (v := .i32 y) (Or.inr (Or.inl rfl)) (by simp [setLocal, h2])]
      rw [runJvmResFast_invokestatic_step stepStatic_leafContains]
      step1
      have hch_br : ∀ f0,
          runJvmResFast (if Algorithm.leafContains leaf x y then f0 + 4 else f0 + 5)
            f_Algorithm_formatLeafRow_loop_prog 16 (f_Algorithm_formatLeafRow_loop_prog.drop 16)
            ⟨16, [], setLocal (setLocal locs 6 (.i32 0)) 7
              (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)), jh, hp⟩ =
          runJvmResFast f0 f_Algorithm_formatLeafRow_loop_prog 23
            (f_Algorithm_formatLeafRow_loop_prog.drop 23)
            ⟨23, [], setLocal (setLocal (setLocal locs 6 (.i32 0)) 7
              (.i32 (if Algorithm.leafContains leaf x y then 1 else 0))) 6 (.i32 chCode), jh, hp⟩ := by
        intro f0
        by_cases hc : Algorithm.leafContains leaf x y
        · simp only [hc, ↓reduceIte]
          conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 16 =
            [.iload 7, .ifne 21, .iconst 46, .istore 6, .goto 23, .iconst 42, .istore 6] ++
              f_Algorithm_formatLeafRow_loop_prog.drop 23 from rfl]
          simp only [List.cons_append, List.nil_append]
          rw [show f0 + 4 = f0 + 1 + 1 + 1 + 1 from by omega]
          rw [runJvmResFast_load_step (k := 7) (v := .i32 1) (Or.inr (Or.inl rfl)) (by simp [setLocal])]
          rw [runJvmResFast_ifne_branch (by decide)]
          conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 21 =
            [.iconst 42, .istore 6] ++ f_Algorithm_formatLeafRow_loop_prog.drop 23 from rfl]
          simp only [List.cons_append, List.nil_append]
          step1; step1
          simp [chCode, hc]
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 16 =
            [.iload 7, .ifne 21, .iconst 46, .istore 6, .goto 23, .iconst 42, .istore 6] ++
              f_Algorithm_formatLeafRow_loop_prog.drop 23 from rfl]
          simp only [List.cons_append, List.nil_append]
          rw [show f0 + 5 = f0 + 1 + 1 + 1 + 1 + 1 from by omega]
          rw [runJvmResFast_load_step (k := 7) (v := .i32 0) (Or.inr (Or.inl rfl)) (by simp [setLocal])]
          rw [runJvmResFast_ifne_fallthrough]
          step1; step1
          rw [runJvmResFast_goto]
          simp [chCode, hc]
      have hbr_fuel :
          (if Algorithm.leafContains leaf x y = true then fRec + 45 else fRec + 46) =
          if Algorithm.leafContains leaf x y = true then (fRec + 41) + 4 else (fRec + 41) + 5 := by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [hc] <;> omega
      rw [hbr_fuel, hch_br]
      -- Step pc 23..47
      rw [show (fRec + 41 : Nat) = (fRec + 17) + 24 from by omega]
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 23 =
        [.lload 0, .lstore 7, .iload 2, .istore 9, .iload 3, .iconst 1, .iadd,
          .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 10,
          .iload 4, .istore 11, .iconst 0, .istore 13, .iload 6, .istore 14,
          .iload 14, .iconst 65536, .if_icmpge 63,
          .aload 5, .iload 14, .iflt 47, .iload 14, .iconst 65535, .if_icmple 59] ++
          f_Algorithm_formatLeafRow_loop_prog.drop 47 from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_load_step (k := 0) (v := .i64 leaf) (Or.inr (Or.inr rfl)) (by simp [setLocal, h0])]
      step1
      rw [runJvmResFast_load_step (k := 2) (v := .i32 y) (Or.inr (Or.inl rfl)) (by simp [setLocal, h2])]
      step1
      rw [runJvmResFast_load_step (k := 3) (v := .i32 x) (Or.inr (Or.inl rfl)) (by simp [setLocal, h3])]
      step1; step1
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      step1
      rw [runJvmResFast_load_step (k := 4) (v := .i32 limit) (Or.inr (Or.inl rfl)) (by simp [setLocal, h4])]
      step1; step1; step1
      rw [runJvmResFast_load_step (k := 6) (v := .i32 chCode) (Or.inr (Or.inl rfl)) (by simp [setLocal, chCode])]
      step1
      rw [runJvmResFast_load_step (k := 14) (v := .i32 chCode) (Or.inr (Or.inl rfl)) (by simp [setLocal, chCode])]
      step1
      have hge65536 : (65536 : UInt32).toBitVec.sle chCode.toBitVec = false := by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [chCode, hc] <;> decide
      rw [runJvmResFast_if_icmpge_fallthrough hge65536]
      rw [runJvmResFast_load_step (k := 5) (v := .str acc) (Or.inl rfl) (by simp [setLocal, h5])]
      rw [runJvmResFast_load_step (k := 14) (v := .i32 chCode) (Or.inr (Or.inl rfl)) (by simp [setLocal, chCode])]
      have hlt0 : chCode.toBitVec.slt 0#32 = false := by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [chCode, hc] <;> decide
      rw [runJvmResFast_iflt_fallthrough hlt0]
      rw [runJvmResFast_load_step (k := 14) (v := .i32 chCode) (Or.inr (Or.inl rfl)) (by simp [setLocal, chCode])]
      step1
      have hle65535 : chCode.toBitVec.sle (65535 : UInt32).toBitVec = true := by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [chCode, hc] <;> decide
      rw [runJvmResFast_if_icmple_branch hle65535]
      norm_res_fuel
      -- Now at pc 59..63
      rw [show (fRec + 17 : Nat) = (fRec + 13) + 4 from by omega]
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 59 =
        [.iload 14, .i2c,
          .invokedynamic "makeConcatWithConstants" "\x01\x01" "(Ljava/lang/String;C)Ljava/lang/String;",
          .goto 130] ++ f_Algorithm_formatLeafRow_loop_prog.drop 63 from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_load_step (k := 14) (v := .i32 chCode) (Or.inr (Or.inl rfl)) (by simp [setLocal, chCode])]
      rw [runJvmResFast_i2c]
      have hi2c : chCode &&& 65535 = chCode := by
        by_cases hc : Algorithm.leafContains leaf x y <;> simp [chCode, hc] <;> decide
      rw [hi2c]
      rw [runJvmResFast_invokedynamic_concat_char (Algorithm.leafContains leaf x y)]
      rw [show acc.push (if Algorithm.leafContains leaf x y then '*' else '.') = acc' from rfl]
      rw [runJvmResFast_goto]
      -- Now at pc 130..143 -> goto 3 (13 instrs)
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafRow_loop_prog.drop 130 =
        [.nop, .astore 12, .lload 7, .lstore 0, .iload 9, .istore 2, .iload 10, .istore 3,
          .iload 11, .istore 4, .aload 12, .astore 5, .goto 3] from rfl]
      rw [show fRec + 13 = fRec + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from by omega]
      step1; step1
      rw [runJvmResFast_load_step (k := 7) (v := .i64 leaf) (Or.inr (Or.inr rfl)) (by simp [setLocal])]
      step1
      rw [runJvmResFast_load_step (k := 9) (v := .i32 y) (Or.inr (Or.inl rfl)) (by simp [setLocal])]
      step1
      rw [runJvmResFast_load_step (k := 10) (v := .i32 (x + 1)) (Or.inr (Or.inl rfl)) (by simp [setLocal])]
      step1
      rw [runJvmResFast_load_step (k := 11) (v := .i32 limit) (Or.inr (Or.inl rfl)) (by simp [setLocal])]
      step1
      rw [runJvmResFast_load_step (k := 12) (v := .str acc') (Or.inl rfl) (by simp [setLocal, acc'])]
      step1
      rw [runJvmResFast_goto]
      exact hrec
    · rw [Algorithm.formatLeafRow.loop.eq_1]
      simp only [hlt, ↓reduceDIte]
      obtain ⟨locs', hrun⟩ := step_exit leaf y x limit acc locs jh hp h3 h4 h5 hlt
      exact ⟨8, locs', hrun⟩

theorem formatLeafRow_loop_equiv (leaf : UInt64) (y x limit : UInt32) (acc : String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ f,
      runJvm f f_Algorithm_formatLeafRow_loop_prog
          ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.i64 leaf)) 2 (.i32 y)) 3 (.i32 x)) 4 (.i32 limit)) 5 (.str acc), jh, hp⟩ =
        some (.str (Algorithm.formatLeafRow.loop leaf y x limit acc)) := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
    0 (.i64 leaf)) 2 (.i32 y)) 3 (.i32 x)) 4 (.i32 limit)) 5 (.str acc)
  obtain ⟨fLoop, locs', hloop⟩ := formatLeafRow_loop_aux (limit.toNat - x.toNat)
    leaf y x limit acc locs0 jh hp rfl rfl rfl rfl rfl (Nat.le_refl _)
  have hres : runJvmRes (fLoop + 3) f_Algorithm_formatLeafRow_loop_prog ⟨0, [], locs0, jh, hp⟩ =
      some (.str (Algorithm.formatLeafRow.loop leaf y x limit acc),
        ⟨10, [.str (Algorithm.formatLeafRow.loop leaf y x limit acc)], locs', jh, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 (fLoop + 3) _ _ _ rfl
    rw [show fLoop + 3 = fLoop + 1 + 2 from by omega]
    dsimp only [f_Algorithm_formatLeafRow_loop_prog]
    step1; step1
    rw [runJvmResFast_checkNotNullParameter rfl]
    exact hloop
  exact ⟨fLoop + 3, runJvm_eq_of_runJvmRes hres⟩

theorem formatLeafRow_equiv (leaf : UInt64) (y : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 35 f_Algorithm_formatLeafRow_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i64 leaf)) 2 (.i32 y), jh, hp⟩ =
      some (.str (Algorithm.formatLeafRow leaf y)) := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (fun _ => .null) 0 (.i64 leaf)) 2 (.i32 y)
  cases hfx : Algorithm.findLastLeafX leaf y with
  | none =>
    simp only [Algorithm.formatLeafRow, hfx]
    have hres : runJvmRes 35 f_Algorithm_formatLeafRow_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.str "", ⟨7, [.str ""], setLocal locs0 3 .null, jh, hp⟩) := by
      apply runJvmRes_of_runJvmResFast0 35 _ _ _ rfl
      rw [show (35 : Nat) = 10 + 25 from rfl]
      dsimp only [f_Algorithm_formatLeafRow_prog, locs0]
      step1; step1
      rw [show (10 + 23 : Nat) = 32 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_findLastLeafX]
      simp only [hfx]
      rw [show (32 : Nat) = 10 + 22 from rfl]
      step1; step1
      rw [show (10 + 20 : Nat) = 29 + 1 from rfl]
      rw [runJvmResFast_ifnonnull_fallthrough]
      rw [show (29 : Nat) = 10 + 19 from rfl]
      step1
      rw [show (10 + 18 : Nat) = 27 + 1 from rfl]
      exact runJvmResFast_areturn
    exact runJvm_eq_of_runJvmRes hres
  | some lastX =>
    simp only [Algorithm.formatLeafRow, hfx]
    suffices hres : ∃ locs', runJvmRes 35 f_Algorithm_formatLeafRow_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.str (Algorithm.formatLeafRow.loop leaf y 0 (lastX + 1) ""),
          ⟨38, [.str (Algorithm.formatLeafRow.loop leaf y 0 (lastX + 1) "")], locs', jh, hp⟩) by
      obtain ⟨locs', hres'⟩ := hres
      exact runJvm_eq_of_runJvmRes hres'
    apply Exists.intro
    · apply runJvmRes_of_runJvmResFast0 35 _ _ _ rfl
      rw [show (35 : Nat) = 10 + 25 from rfl]
      dsimp only [f_Algorithm_formatLeafRow_prog]
      step1_load 0 (.i64 leaf), (by simp [locs0, setLocal])
      step1_load 2 (.i32 y), (by simp [locs0, setLocal])
      rw [show (10 + 23 : Nat) = 32 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_findLastLeafX]
      simp only [hfx]
      rw [show (32 : Nat) = 10 + 22 from rfl]
      step1; step1
      rw [show (10 + 20 : Nat) = 29 + 1 from rfl]
      rw [runJvmResFast_ifnonnull_branch rfl]
      conv => lhs; arg 4; dsimp only [f_Algorithm_formatLeafRow_prog, List.drop]
      rw [show (29 : Nat) = 10 + 19 from rfl]
      step1; step1; step1; step1; step1
      rw [show (10 + 14 : Nat) = 23 + 1 from rfl]
      rw [runJvmResFast_instanceof_boxedUInt_int]
      rw [show (23 : Nat) = 22 + 1 from rfl]
      rw [runJvmResFast_ifeq_branch rfl]
      conv => lhs; arg 4; dsimp only [f_Algorithm_formatLeafRow_prog, List.drop]
      rw [show (22 : Nat) = 10 + 12 from rfl]
      step1
      rw [show (10 + 11 : Nat) = 20 + 1 from rfl]
      rw [runJvmResFast_invokevirtual_step (by rfl :
        stepInvokeVirtual ⟨21, [.boxedUInt lastX], setLocal (setLocal (setLocal locs0
          3 (.boxedUInt lastX)) 5 (.boxedUInt lastX)) 6 (.i32 0), jh, hp⟩
          "kotlin/UInt" "unbox-impl" "()I" = _)]
      rw [show (20 : Nat) = 10 + 10 from rfl]
      step1; step1; step1; step1; step1; step1
      rw [show (10 + 4 : Nat) = 13 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      rw [show (13 : Nat) = 3 + 10 from rfl]
      step1; step1; step1
      step1_load 0 (.i64 leaf), (by simp [locs0, setLocal])
      step1_load 2 (.i32 y), (by simp [locs0, setLocal])
      step1; step1; step1
      rw [show (3 + 2 : Nat) = 4 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_formatLeafRow_loop]
      rw [show (4 : Nat) = 3 + 1 from rfl]
      exact runJvmResFast_areturn

/-! ### formatLeafNode_loop & formatLeafNode -/

private theorem formatLeafNode_loop_aux (n : Nat) :
    ∀ (leaf : UInt64) (y limit : UInt32) (acc : String)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      locs 0 = .i64 leaf → locs 2 = .i32 y → locs 3 = .i32 limit → locs 4 = .str acc →
      limit.toNat - y.toNat ≤ n →
      ∃ f locs',
        runJvmResFast f f_Algorithm_formatLeafNode_loop_prog 3
          (f_Algorithm_formatLeafNode_loop_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
          some (.str (Algorithm.formatLeafNode.loop leaf y limit acc),
            ⟨8, [.str (Algorithm.formatLeafNode.loop leaf y limit acc)], locs', jh, hp⟩) := by
  induction n with
  | zero =>
    intro leaf y limit acc locs jh hp _ h2 h3 h4 hn
    have hge : ¬(y < limit) := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [Algorithm.formatLeafNode.loop.eq_1]
    simp only [hge, ↓reduceDIte]
    refine ⟨6, locs, ?_⟩
    conv => lhs; arg 4; rw [show f_Algorithm_formatLeafNode_loop_prog.drop 3 =
      [.iload 2, .iload 3, .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I",
        .iflt 9, .aload 4, .areturn] ++ f_Algorithm_formatLeafNode_loop_prog.drop 9 from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [show (6 : Nat) = 5 + 1 from rfl]
    rw [runJvmResFast_load_step (Or.inr (Or.inl rfl)) h2]
    rw [show (5 : Nat) = 4 + 1 from rfl]
    rw [runJvmResFast_load_step (Or.inr (Or.inl rfl)) h3]
    rw [show (4 : Nat) = 3 + 1 from rfl]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    have hflt : (if y == limit then (0 : UInt32) else if y < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    rw [show (3 : Nat) = 2 + 1 from rfl]
    rw [runJvmResFast_iflt_fallthrough hflt]
    rw [show (2 : Nat) = 1 + 1 from rfl]
    rw [runJvmResFast_load_step (Or.inl rfl) h4]
    exact runJvmResFast_areturn
  | succ n ih =>
    intro leaf y limit acc locs jh hp h0 h2 h3 h4 hn
    by_cases hlt : y < limit
    · have hsub : limit.toNat - (y + 1).toNat ≤ n := by
        have h1 := UInt32.lt_iff_toNat_lt.mp hlt
        rw [ui32_add1_toNat hlt]
        omega
      let rowStr := Algorithm.formatLeafRow leaf y
      let acc1 := acc ++ rowStr
      let acc2 := acc1 ++ "$"
      let locsEnd :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal locs 5 (.i32 (y + 1))) 6 (.str rowStr)) 7 (.str acc1))
          8 (.str "$")) 9 (.i64 leaf)) 11 (.i32 limit)) 12 (.str acc2))
          0 (.i64 leaf)) 2 (.i32 (y + 1))) 3 (.i32 limit)) 4 (.str acc2)
      have heqAcc : acc ++ rowStr ++ "$" = acc2 := rfl
      obtain ⟨fRec, locs', hrec⟩ := ih leaf (y + 1) limit acc2 locsEnd
        jh hp
        (by simp [locsEnd, setLocal]) (by simp [locsEnd, setLocal])
        (by simp [locsEnd, setLocal]) (by simp [locsEnd, setLocal]) hsub
      rw [Algorithm.formatLeafNode.loop.eq_1]
      simp only [hlt, ↓reduceDIte]
      rw [heqAcc]
      refine ⟨fRec + 36, locs', ?_⟩
      rw [show fRec + 36 = (fRec + 32) + 4 from by omega]
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafNode_loop_prog.drop 3 =
        [.iload 2, .iload 3, .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I",
          .iflt 9] ++ f_Algorithm_formatLeafNode_loop_prog.drop 7 from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [show (fRec + 32) + 4 = (fRec + 35) + 1 from by omega]
      rw [runJvmResFast_load_step (k := 2) (v := .i32 y) (Or.inr (Or.inl rfl)) h2]
      rw [show fRec + 35 = (fRec + 34) + 1 from by omega]
      rw [runJvmResFast_load_step (k := 3) (v := .i32 limit) (Or.inr (Or.inl rfl)) h3]
      rw [show fRec + 34 = (fRec + 33) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      have hflt : (if y == limit then (0 : UInt32) else if y < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          true := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
      rw [show fRec + 33 = (fRec + 32) + 1 from by omega]
      rw [runJvmResFast_iflt_branch hflt]
      -- Now at pc 9..41 (32 instrs)
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafNode_loop_prog.drop 9 =
        [.iload 2, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
          .istore 5, .lload 0, .iload 2,
          .invokestatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_formatLeafRow-8GdB7C8" "(JI)Ljava/lang/String;",
          .astore 6, .aload 4, .aload 6,
          .invokedynamic "makeConcatWithConstants" "\x01\x01"
            "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;",
          .astore 7, .ldcStr "$", .astore 8, .lload 0, .lstore 9, .iload 3, .istore 11,
          .aload 7, .aload 8,
          .invokedynamic "makeConcatWithConstants" "\x01\x01"
            "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;",
          .astore 12, .lload 9, .lstore 0, .iload 5, .istore 2, .iload 11, .istore 3,
          .aload 12, .astore 4, .goto 3] from rfl]
      step1_load 2 (.i32 y), h2
      step1; step1
      rw [show fRec + 29 = (fRec + 28) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      rw [show fRec + 28 = fRec + 28 from rfl]
      step1
      step1_load 0 (.i64 leaf), (by simp [setLocal, h0])
      step1_load 2 (.i32 y), (by simp [setLocal, h2])
      rw [show fRec + 25 = (fRec + 24) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_formatLeafRow]
      rw [show fRec + 24 = fRec + 24 from rfl]
      step1
      step1_load 4 (.str acc), (by simp [setLocal, h4])
      step1_load 6 (.str rowStr), (by simp [setLocal, rowStr])
      rw [show fRec + 21 = (fRec + 20) + 1 from by omega]
      rw [runJvmResFast_invokedynamic_concat2]
      rw [show acc ++ rowStr = acc1 from rfl]
      rw [show fRec + 20 = fRec + 20 from rfl]
      step1; step1; step1
      step1_load 0 (.i64 leaf), (by simp [setLocal, h0])
      step1
      step1_load 3 (.i32 limit), (by simp [setLocal, h3])
      step1
      step1_load 7 (.str acc1), (by simp [setLocal])
      step1_load 8 (.str "$"), (by simp [setLocal])
      rw [show fRec + 11 = (fRec + 10) + 1 from by omega]
      rw [runJvmResFast_invokedynamic_concat2]
      rw [show acc1 ++ "$" = acc2 from rfl]
      rw [show fRec + 10 = fRec + 10 from rfl]
      step1
      step1_load 9 (.i64 leaf), (by simp [setLocal])
      step1
      step1_load 5 (.i32 (y + 1)), (by simp [setLocal])
      step1
      step1_load 11 (.i32 limit), (by simp [setLocal])
      step1
      step1_load 12 (.str acc2), (by simp [setLocal])
      step1
      rw [show fRec + 1 = fRec + 1 from rfl]
      rw [runJvmResFast_goto]
      exact hrec
    · rw [Algorithm.formatLeafNode.loop.eq_1]
      simp only [hlt, ↓reduceDIte]
      refine ⟨6, locs, ?_⟩
      conv => lhs; arg 4; rw [show f_Algorithm_formatLeafNode_loop_prog.drop 3 =
        [.iload 2, .iload 3, .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I",
          .iflt 9, .aload 4, .areturn] ++ f_Algorithm_formatLeafNode_loop_prog.drop 9 from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [show (6 : Nat) = 5 + 1 from rfl]
      rw [runJvmResFast_load_step (Or.inr (Or.inl rfl)) h2]
      rw [show (5 : Nat) = 4 + 1 from rfl]
      rw [runJvmResFast_load_step (Or.inr (Or.inl rfl)) h3]
      rw [show (4 : Nat) = 3 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      have hflt : (if y == limit then (0 : UInt32) else if y < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt
      rw [show (3 : Nat) = 2 + 1 from rfl]
      rw [runJvmResFast_iflt_fallthrough hflt]
      rw [show (2 : Nat) = 1 + 1 from rfl]
      rw [runJvmResFast_load_step (Or.inl rfl) h4]
      exact runJvmResFast_areturn

theorem formatLeafNode_loop_equiv (leaf : UInt64) (y limit : UInt32) (acc : String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ f,
      runJvm f f_Algorithm_formatLeafNode_loop_prog
          ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.i64 leaf)) 2 (.i32 y)) 3 (.i32 limit)) 4 (.str acc), jh, hp⟩ =
        some (.str (Algorithm.formatLeafNode.loop leaf y limit acc)) := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (fun _ => .null)
    0 (.i64 leaf)) 2 (.i32 y)) 3 (.i32 limit)) 4 (.str acc)
  obtain ⟨fLoop, locs', hloop⟩ := formatLeafNode_loop_aux (limit.toNat - y.toNat)
    leaf y limit acc locs0 jh hp rfl rfl rfl rfl (Nat.le_refl _)
  have hres : runJvmRes (fLoop + 3) f_Algorithm_formatLeafNode_loop_prog ⟨0, [], locs0, jh, hp⟩ =
      some (.str (Algorithm.formatLeafNode.loop leaf y limit acc),
        ⟨8, [.str (Algorithm.formatLeafNode.loop leaf y limit acc)], locs', jh, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 (fLoop + 3) _ _ _ rfl
    rw [show fLoop + 3 = fLoop + 1 + 2 from by omega]
    dsimp only [f_Algorithm_formatLeafNode_loop_prog]
    step1; step1
    rw [runJvmResFast_checkNotNullParameter rfl]
    exact hloop
  exact ⟨fLoop + 3, runJvm_eq_of_runJvmRes hres⟩

theorem formatLeafNode_equiv (leaf : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 35 f_Algorithm_formatLeafNode_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.i64 leaf), jh, hp⟩ =
      some (.str (Algorithm.formatLeafNode leaf)) := by
  let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.i64 leaf)
  cases hfy : Algorithm.findLastLeafRow leaf with
  | none =>
    simp only [Algorithm.formatLeafNode, hfy]
    have hres : runJvmRes 35 f_Algorithm_formatLeafNode_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.str "$", ⟨6, [.str "$"], setLocal locs0 2 .null, jh, hp⟩) := by
      apply runJvmRes_of_runJvmResFast0 35 _ _ _ rfl
      rw [show (35 : Nat) = 10 + 25 from rfl]
      dsimp only [f_Algorithm_formatLeafNode_prog, locs0]
      step1
      rw [show (10 + 24 : Nat) = 33 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_findLastLeafRow]
      simp only [hfy]
      rw [show (33 : Nat) = 10 + 23 from rfl]
      step1; step1
      rw [show (10 + 21 : Nat) = 30 + 1 from rfl]
      rw [runJvmResFast_ifnonnull_fallthrough]
      rw [show (30 : Nat) = 10 + 20 from rfl]
      step1
      rw [show (10 + 19 : Nat) = 28 + 1 from rfl]
      exact runJvmResFast_areturn
    exact runJvm_eq_of_runJvmRes hres
  | some lastY =>
    simp only [Algorithm.formatLeafNode, hfy]
    suffices hres : ∃ locs', runJvmRes 35 f_Algorithm_formatLeafNode_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.str (Algorithm.formatLeafNode.loop leaf 0 (lastY + 1) ""),
          ⟨36, [.str (Algorithm.formatLeafNode.loop leaf 0 (lastY + 1) "")], locs', jh, hp⟩) by
      obtain ⟨locs', hres'⟩ := hres
      exact runJvm_eq_of_runJvmRes hres'
    apply Exists.intro
    · apply runJvmRes_of_runJvmResFast0 35 _ _ _ rfl
      rw [show (35 : Nat) = 10 + 25 from rfl]
      dsimp only [f_Algorithm_formatLeafNode_prog]
      step1_load 0 (.i64 leaf), (by simp [locs0, setLocal])
      rw [show (10 + 24 : Nat) = 33 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_findLastLeafRow]
      simp only [hfy]
      rw [show (33 : Nat) = 10 + 23 from rfl]
      step1; step1
      rw [show (10 + 21 : Nat) = 30 + 1 from rfl]
      rw [runJvmResFast_ifnonnull_branch rfl]
      conv => lhs; arg 4; dsimp only [f_Algorithm_formatLeafNode_prog, List.drop]
      rw [show (30 : Nat) = 10 + 20 from rfl]
      step1; step1; step1; step1; step1
      rw [show (10 + 15 : Nat) = 24 + 1 from rfl]
      rw [runJvmResFast_instanceof_boxedUInt_int]
      rw [show (24 : Nat) = 23 + 1 from rfl]
      rw [runJvmResFast_ifeq_branch rfl]
      conv => lhs; arg 4; dsimp only [f_Algorithm_formatLeafNode_prog, List.drop]
      rw [show (23 : Nat) = 10 + 13 from rfl]
      step1
      rw [show (10 + 12 : Nat) = 21 + 1 from rfl]
      rw [runJvmResFast_invokevirtual_step (by rfl :
        stepInvokeVirtual ⟨20, [.boxedUInt lastY], setLocal (setLocal (setLocal locs0
          2 (.boxedUInt lastY)) 4 (.boxedUInt lastY)) 5 (.i32 0), jh, hp⟩
          "kotlin/UInt" "unbox-impl" "()I" = _)]
      rw [show (21 : Nat) = 10 + 11 from rfl]
      step1; step1; step1; step1; step1; step1
      rw [show (10 + 5 : Nat) = 14 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      rw [show (14 : Nat) = 4 + 10 from rfl]
      step1; step1; step1
      step1_load 0 (.i64 leaf), (by simp [locs0, setLocal])
      step1; step1; step1
      rw [show (4 + 3 : Nat) = 6 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_formatLeafNode_loop]
      rw [show (6 : Nat) = 5 + 1 from rfl]
      exact runJvmResFast_areturn

/-! ### Extra Step Helpers for Group 2 & Group 3 -/

private theorem runJvmResFast_tableswitch {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {low : Int32} {targets : List Nat} {defT : Nat} {rest : List JvmInstr} {pc0 : Nat}
    {key : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets defT :: rest)
        ⟨pc0, .i32 key :: stkRest, locs, jh, hp⟩ =
      let t := Jvm.tableswitchTarget key low targets defT
      runJvmResFast f prog t (prog.drop t) ⟨t, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl), evalResBranchInstrCons_tableswitch]

private theorem runJvmResFast_lcmp {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : UInt64} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lcmp :: rest)
        ⟨pc0, .i64 b :: .i64 a :: stkRest, locs, jh, hp⟩ =
      let res : UInt32 :=
        if a == b then 0
        else if a.toBitVec.slt b.toBitVec then (4294967295 : UInt32)
        else 1
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_instanceof_pair {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 1 :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_instanceof_boxedULong_long {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : UInt64} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "java/lang/Long" :: rest)
        ⟨pc0, .boxedULong v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_checkcast_pair {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_newClass_pair {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.newClass "kotlin/Pair" :: rest)
        ⟨pc0, stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .allocRef "kotlin/Pair" :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_invokespecial_pair_init {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" :: rest)
        ⟨pc0, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h)
  rfl

private theorem runJvmResFast_checkNotNull {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {msg : String} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnn : v ≠ .null) :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  have his : Jvm.JvmVal.isNull v = false := by cases v <;> simp_all [Jvm.JvmVal.isNull]
  exact Jvm.runJvmResFast_invokestatic_step algHooks
    (Jvm.stepInvokeStatic_intrinsics_checkNotNull algHooks his)

private theorem stepVirtual_uint_unbox {pc : Nat} {v : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_ulongBox {pc : Nat} {v : UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 v :: rest, locs, jh, hp⟩
      "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, .boxedULong v :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_remainderUnsigned {pc : Nat} {a b : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hb : b ≠ 0) :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "remainderUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (a % b) :: rest, locs, jh, hp⟩) := by
  have hb0 : (b == 0) = false := beq_false_of_ne hb
  have h0 : stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "remainderUnsigned" "(II)I" =
      if (b == 0) = true then .inr none
      else .inl (some ⟨pc + 1, .i32 (a % b) :: rest, locs, jh, hp⟩) := rfl
  rw [h0]
  simp [hb0]

private theorem stepStatic_intValueOf {pc : Nat} {v : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: rest, locs, jh, hp⟩
      "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" =
      .inl (some ⟨pc + 1, .boxedInt v :: rest, locs, jh, hp⟩) := rfl

private theorem list_drop_step_idx {α : Type} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  induction k generalizing l with
  | zero => cases l <;> simp_all
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons a as => exact ih h

open Lean Elab Tactic in
local elab "step_drop_at " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic|
      (conv => lhs; arg 4; rw [list_drop_step_idx rfl]; try simp only [Nat.reduceAdd])))

/-! ### List_lookup (addLeaf & addNode) -/

private def LeafBucketListRep (jh : Jvm.JvmHeap AlgExt) : List (UInt64 × UInt32) → JvmVal → Prop
  | [], .heapRef addr => ∃ cls elems,
    jh.get? addr = some (.objArray cls elems) ∧ elems[0]? = some (.boxedInt 0)
  | (k, v) :: tl, .heapRef addr => ∃ cls elems tlVal,
    jh.get? addr = some (.objArray cls elems) ∧
    elems[0]? = some (.boxedInt 1) ∧
    elems[1]? = some (.pair (.boxedULong k) (.boxedUInt v)) ∧
    elems[2]? = some tlVal ∧
    LeafBucketListRep jh tl tlVal
  | _, _ => False

private theorem jvmHeap_addr_lt_of_get? {Ext : Type} {jh : Jvm.JvmHeap Ext}
    {addr : Nat} {obj : Jvm.HeapObj Ext} (hget : jh.get? addr = some obj) :
    addr < jh.objects.size := by
  simp only [Jvm.JvmHeap.get?, Array.getElem?_eq_some_iff] at hget
  exact hget.1

private theorem LeafBucketListRep.mono_alloc {jh : Jvm.JvmHeap AlgExt} {obj : Jvm.HeapObj AlgExt}
    {xs : List (UInt64 × UInt32)} {v : JvmVal}
    (hrep : LeafBucketListRep jh xs v) :
    LeafBucketListRep (jh.alloc obj).2 xs v := by
  induction xs generalizing v with
  | nil =>
    cases v with
    | heapRef addr =>
      rcases hrep with ⟨cls, elems, hget, h0⟩
      exact ⟨cls, elems,
        by rw [jvmHeap_get?_alloc_lt jh obj (jvmHeap_addr_lt_of_get? hget)]; exact hget, h0⟩
    | _ => exact hrep
  | cons hd tl ih =>
    rcases hd with ⟨k, val⟩
    cases v with
    | heapRef addr =>
      rcases hrep with ⟨cls, elems, tlVal, hget, h0, h1, h2, htl⟩
      exact ⟨cls, elems, tlVal,
        by rw [jvmHeap_get?_alloc_lt jh obj (jvmHeap_addr_lt_of_get? hget)]; exact hget,
        h0, h1, h2, ih htl⟩
    | _ => exact hrep

private theorem encodeLeafBucketList_rep (jh : Jvm.JvmHeap AlgExt) (xs : List (UInt64 × UInt32)) :
    LeafBucketListRep (encodeLeafBucketList jh xs).2 xs (encodeLeafBucketList jh xs).1 := by
  induction xs generalizing jh with
  | nil =>
    refine ⟨"java/lang/Object", #[.boxedInt 0], jvmHeap_get?_alloc_self _ _, rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    dsimp only [encodeLeafBucketList]
    refine ⟨"java/lang/Object",
      #[.boxedInt 1, .pair (.boxedULong k) (.boxedUInt v), (encodeLeafBucketList jh tl).1],
      (encodeLeafBucketList jh tl).1, jvmHeap_get?_alloc_self _ _, rfl, rfl, rfl,
      LeafBucketListRep.mono_alloc (ih jh)⟩

private theorem runJvmResFast_checkcast_objArray_any {f pc pc0 addr : Nat}
    {prog rest : List JvmInstr} {cls : String} {elems : Array JvmVal} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    runJvmResFast (f + 1) prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ := by
  apply runJvmResFast_checkcast_step
  unfold Jvm.stepInstr Jvm.evalCheckCast Jvm.JvmHeap.checkCast Jvm.JvmHeap.checkInstanceOf
  dsimp only
  rw [hget]
  simp [Jvm.HeapObj.matchesType]

private theorem runJvmResFast_aaload_elem {f pc pc0 addr : Nat} {idx : UInt32}
    {prog rest : List JvmInstr} {cls : String} {elems : Array JvmVal} {val : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (helem : elems[idx.toNat]? = some val) :
    runJvmResFast (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, val :: stkRest, locs, jh, hp⟩ := by
  rcases Array.getElem?_eq_some_iff.mp helem with ⟨hlt, rfl⟩
  exact runJvmResFast_aaload hget hslt hlt

private theorem array_push_set_last {α : Type} (a : Array α) (x y : α)
    (hlt : a.size < (a.push x).size) :
    (a.push x).set a.size y hlt = a.push y := by
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp only [Array.getElem_set, Array.getElem_push]
    split
    · split <;> simp_all; omega
    · split
      · rfl
      · rename_i hne hlt'
        exfalso
        simp only [Array.size_push] at hi2
        omega

private theorem alloc_obj1_set (jh : Jvm.JvmHeap AlgExt) (v0 : JvmVal)
    {h1 : (0 : UInt32).toNat < (Array.replicate (1 : UInt32).toNat JvmVal.null).size} :
    ((jh.alloc (.objArray "java/lang/Object"
        (Array.replicate (1 : UInt32).toNat JvmVal.null))).2.set jh.objects.size
        (.objArray "java/lang/Object"
          ((Array.replicate (1 : UInt32).toNat JvmVal.null).set (0 : UInt32).toNat v0 h1))) =
      (jh.alloc (.objArray "java/lang/Object" #[v0])).2 := by
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.size_push, Nat.lt_succ_self, ↓reduceDIte]
  congr 1
  rw [show (Array.replicate (1 : UInt32).toNat JvmVal.null).set (0 : UInt32).toNat v0 h1 = #[v0] from rfl]
  exact array_push_set_last jh.objects _ _ _

private theorem alloc_obj2_step0 (jh : Jvm.JvmHeap AlgExt) (cls : String) (v0 : JvmVal)
    {h1 : (0 : UInt32).toNat < (Array.replicate (2 : UInt32).toNat JvmVal.null).size} :
    ((jh.alloc (.objArray cls (Array.replicate (2 : UInt32).toNat JvmVal.null))).2.set
        jh.objects.size
        (.objArray cls ((Array.replicate (2 : UInt32).toNat JvmVal.null).set (0 : UInt32).toNat v0 h1))) =
      (jh.alloc (.objArray cls #[v0, JvmVal.null])).2 := by
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.size_push, Nat.lt_succ_self, ↓reduceDIte]
  congr 1
  rw [show (Array.replicate (2 : UInt32).toNat JvmVal.null).set (0 : UInt32).toNat v0 h1 =
    #[v0, JvmVal.null] from rfl]
  exact array_push_set_last jh.objects _ _ _

private theorem alloc_obj2_step1 (jh : Jvm.JvmHeap AlgExt) (cls : String) (v0 v1 : JvmVal)
    {h2 : (1 : UInt32).toNat < (#[v0, JvmVal.null] : Array JvmVal).size} :
    ((jh.alloc (.objArray cls #[v0, JvmVal.null])).2.set jh.objects.size
        (.objArray cls ((#[v0, JvmVal.null] : Array JvmVal).set (1 : UInt32).toNat v1 h2))) =
      (jh.alloc (.objArray cls #[v0, v1])).2 := by
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.size_push, Nat.lt_succ_self, ↓reduceDIte]
  congr 1
  rw [show (#[v0, JvmVal.null] : Array JvmVal).set (1 : UInt32).toNat v1 h2 = #[v0, v1] from rfl]
  exact array_push_set_last jh.objects _ _ _

private theorem list_lookup_addLeaf_aux (xs : List (UInt64 × UInt32))
    (k : UInt64) (listVal : JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hl0 : locs 0 = .i64 k) (hl2 : locs 2 = listVal)
    (hrep : LeafBucketListRep jh xs listVal) :
    ∃ (f : Nat) (locs' : Nat → JvmVal),
      let retObj : Jvm.HeapObj AlgExt := match xs.lookup k with
        | none => .objArray "java/lang/Object" #[.boxedInt 0]
        | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v]
      let pc' : Nat := match xs.lookup k with
        | none => 24
        | some _ => 103
      runJvmResFast f f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
          0 f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
          ⟨0, [], locs, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨pc', [.heapRef jh.objects.size], locs',
          (jh.alloc retObj).2, hp⟩) := by
  induction xs generalizing listVal locs with
  | nil =>
    cases listVal
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, hget, h0⟩
      suffices hsuff : ∃ locs',
          runJvmResFast 25
            f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
            0 f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
            ⟨0, [], locs, jh, hp⟩ =
          some (.heapRef jh.objects.size, ⟨24, [.heapRef jh.objects.size], locs',
            (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩) by
        obtain ⟨locs', hs⟩ := hsuff
        exact ⟨25, locs', hs⟩
      apply Exists.intro
      · rw [show (25 : Nat) = 12 + 13 from rfl]
        conv =>
          lhs; arg 4
          rw [show f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog =
            f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog.drop 0
            from rfl]
        step_drop_at 13
        step1_load 2 (.heapRef addr), hl2
        step1
        rw [runJvmResFast_checkNotNull (by intro h; cases h)]
        step1_load 2 (.heapRef addr), hl2
        rw [runJvmResFast_checkcast_objArray_any hget]
        step1
        rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h0)]
        step1; step1
        rw [runJvmResFast_checkNotNull (by intro h; cases h)]
        rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
        rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
        rw [runJvmResFast_tableswitch]
        rw [show Jvm.tableswitchTarget 0 0 [13, 25] 104 = 13 from by decide]
        dsimp only
        step_drop_at 12
        rw [show (12 : Nat) = 1 + 11 from rfl]
        step1
        rw [runJvmResFast_anewarray_obj (by decide)]
        step1; step1; step1; step1
        rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
        have hgetNew : ((jh.alloc (.objArray "java/lang/Object"
            (Array.replicate (UInt32.toNat 1) .null))).2).get? jh.objects.size =
            some (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 1) .null)) :=
          jvmHeap_get?_alloc_self _ _
        rw [runJvmResFast_aastore (idx := 0) hgetNew (by decide) (by decide)]
        step1; step1; step1
        rw [alloc_obj1_set]
        exact runJvmResFast_areturn
    all_goals exact False.elim hrep
  | cons hd tl ih =>
    rcases hd with ⟨hk, hv⟩
    cases listVal
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, tlVal, hget, h0, h1, h2, htl⟩
      by_cases heq : k == hk
      · have hke : k = hk := LawfulBEq.eq_of_beq heq
        subst hke
        suffices hsuff : ∃ locs',
            runJvmResFast 71
              f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
              0 f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
              ⟨0, [], locs, jh, hp⟩ =
            some (.heapRef jh.objects.size, ⟨103, [.heapRef jh.objects.size], locs',
              (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt hv])).2, hp⟩) by
          obtain ⟨locs', hs⟩ := hsuff
          refine ⟨71, locs', ?_⟩
          simp only [List.lookup, beq_self_eq_true]
          exact hs
        apply Exists.intro
        · rw [show (71 : Nat) = 58 + 13 from rfl]
          conv =>
            lhs; arg 4
            rw [show f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog =
              f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog.drop 0
              from rfl]
          step_drop_at 13
          step1_load 2 (.heapRef addr), hl2
          step1
          rw [runJvmResFast_checkNotNull (by intro h; cases h)]
          step1_load 2 (.heapRef addr), hl2
          rw [runJvmResFast_checkcast_objArray_any hget]
          step1
          rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h0)]
          step1; step1
          rw [runJvmResFast_checkNotNull (by intro h; cases h)]
          rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
          rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
          rw [runJvmResFast_tableswitch]
          rw [show Jvm.tableswitchTarget 1 0 [13, 25] 104 = 25 from by decide]
          dsimp only
          step_drop_at 17
          rw [show (58 : Nat) = 41 + 17 from rfl]
          step1_load 2 (.heapRef addr), hl2
          rw [runJvmResFast_checkcast_objArray_any hget]
          step1
          rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h1)]
          step1
          step1_load 2 (.heapRef addr), (by simp [hl2, setLocal])
          rw [runJvmResFast_checkcast_objArray_any hget]
          step1
          rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h2)]
          step1; step1
          rw [runJvmResFast_instanceof_pair]
          rw [runJvmResFast_ifeq_fallthrough (by decide)]
          step1
          rw [runJvmResFast_checkcast_pair]
          rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
          rw [runJvmResFast_goto]
          step_drop_at 8
          rw [show (41 : Nat) = 33 + 8 from rfl]
          step1; step1
          rw [runJvmResFast_instanceof_pair]
          rw [runJvmResFast_ifeq_fallthrough (by decide)]
          step1
          rw [runJvmResFast_checkcast_pair]
          rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
          rw [runJvmResFast_goto]
          step_drop_at 6
          rw [show (33 : Nat) = 27 + 6 from rfl]
          step1; step1; step1; step1
          rw [runJvmResFast_instanceof_boxedULong_long]
          rw [runJvmResFast_ifeq_branch rfl]
          step_drop_at 11
          rw [show (27 : Nat) = 16 + 11 from rfl]
          step1; step1
          rw [runJvmResFast_checkNotNull (by intro h; cases h)]
          step1
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          rw [runJvmResFast_invokevirtual_step stepVirtual_ulong_unbox]
          step1
          step1_load 0 (.i64 k), (by simp [hl0, setLocal])
          step1
          rw [runJvmResFast_lcmp]
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [runJvmResFast_ifeq_branch rfl]
          step_drop_at 16
          rw [show (16 : Nat) = 1 + 15 from rfl]
          step1
          rw [runJvmResFast_anewarray_obj (by decide)]
          step1; step1; step1; step1
          rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
          have hgetNew : ((jh.alloc (.objArray "java/lang/Object"
              (Array.replicate (UInt32.toNat 2) .null))).2).get? jh.objects.size =
              some (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 2) .null)) :=
            jvmHeap_get?_alloc_self _ _
          rw [runJvmResFast_aastore (idx := 0) hgetNew (by decide) (by decide)]
          rw [alloc_obj2_step0]
          step1; step1
          step1_load 5 (.boxedUInt hv), (by simp [setLocal])
          have hgetNew2 : ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2).get?
              jh.objects.size =
              some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) :=
            jvmHeap_get?_alloc_self _ _
          rw [runJvmResFast_aastore (idx := 1) hgetNew2 (by decide) (by decide)]
          rw [alloc_obj2_step1]
          step1; step1; step1
          exact runJvmResFast_areturn
      · have hne : (k == hk) = false := Bool.eq_false_of_ne_true heq
        let locsRec := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          3 (.pair (.boxedULong hk) (.boxedUInt hv))) 4 tlVal) 5 (.boxedUInt hv))
          8 (.boxedULong hk)) 9 (.i32 0)) 6 (.i64 hk)) 0 (.i64 k)) 2 tlVal
        have hl0_rec : locsRec 0 = .i64 k := by simp [locsRec, setLocal]
        have hl2_rec : locsRec 2 = tlVal := by simp [locsRec, setLocal]
        obtain ⟨fRec, locs', hrec⟩ := ih tlVal locsRec hl0_rec hl2_rec htl
        refine ⟨fRec + 60, locs', ?_⟩
        simp only [List.lookup, hne]
        rw [show fRec + 60 = (fRec + 47) + 13 from by omega]
        conv =>
          lhs; arg 4
          rw [show f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog =
            f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog.drop 0
            from rfl]
        step_drop_at 13
        step1_load 2 (.heapRef addr), hl2
        step1
        rw [runJvmResFast_checkNotNull (by intro h; cases h)]
        step1_load 2 (.heapRef addr), hl2
        rw [runJvmResFast_checkcast_objArray_any hget]
        step1
        rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h0)]
        step1; step1
        rw [runJvmResFast_checkNotNull (by intro h; cases h)]
        rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
        rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
        rw [runJvmResFast_tableswitch]
        rw [show Jvm.tableswitchTarget 1 0 [13, 25] 104 = 25 from by decide]
        dsimp only
        step_drop_at 17
        rw [show fRec + 47 = (fRec + 30) + 17 from by omega]
        step1_load 2 (.heapRef addr), hl2
        rw [runJvmResFast_checkcast_objArray_any hget]
        step1
        rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h1)]
        step1
        step1_load 2 (.heapRef addr), (by simp [hl2, setLocal])
        rw [runJvmResFast_checkcast_objArray_any hget]
        step1
        rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h2)]
        step1; step1
        rw [runJvmResFast_instanceof_pair]
        rw [runJvmResFast_ifeq_fallthrough (by decide)]
        step1
        rw [runJvmResFast_checkcast_pair]
        rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
        rw [runJvmResFast_goto]
        step_drop_at 8
        rw [show fRec + 30 = (fRec + 22) + 8 from by omega]
        step1; step1
        rw [runJvmResFast_instanceof_pair]
        rw [runJvmResFast_ifeq_fallthrough (by decide)]
        step1
        rw [runJvmResFast_checkcast_pair]
        rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
        rw [runJvmResFast_goto]
        step_drop_at 6
        rw [show fRec + 22 = (fRec + 16) + 6 from by omega]
        step1; step1; step1; step1
        rw [runJvmResFast_instanceof_boxedULong_long]
        rw [runJvmResFast_ifeq_branch rfl]
        step_drop_at 11
        rw [show fRec + 16 = (fRec + 5) + 11 from by omega]
        step1; step1
        rw [runJvmResFast_checkNotNull (by intro h; cases h)]
        step1
        rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
        rw [runJvmResFast_invokevirtual_step stepVirtual_ulong_unbox]
        step1
        step1_load 0 (.i64 k), (by simp [hl0, setLocal])
        step1
        rw [runJvmResFast_lcmp]
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have hcmp_ne0 : ((if k.toBitVec.slt hk.toBitVec then (4294967295 : UInt32) else 1) == 0) =
            false := by
          split <;> decide
        rw [runJvmResFast_ifeq_fallthrough hcmp_ne0]
        step_drop_at 5
        step1_load 0 (.i64 k), (by simp [hl0, setLocal])
        step1; step1; step1
        rw [runJvmResFast_goto]
        conv =>
          lhs; arg 4
          rw [show f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog.drop 0 =
            f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog from rfl]
        exact hrec
    all_goals exact False.elim hrep

theorem list_lookup_addLeaf_equiv (xs : List (UInt64 × UInt32)) (k : UInt64) (listVal : JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hrep : LeafBucketListRep jh xs listVal) :
    let retObj : Jvm.HeapObj AlgExt := match xs.lookup k with
      | none => .objArray "java/lang/Object" #[.boxedInt 0]
      | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v]
    ∃ f st',
      runJvmRes f f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg_prog
          ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i64 k)) 2 listVal, jh, hp⟩ =
        some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap = (jh.alloc retObj).2 ∧ st'.heap = hp := by
  let locs0 := setLocal (setLocal (fun _ => .null) 0 (.i64 k)) 2 listVal
  obtain ⟨f, locs', hres⟩ := list_lookup_addLeaf_aux xs k listVal locs0 jh hp
    (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) hrep
  exact ⟨f, _, runJvmRes_of_runJvmResFast0 f _ _ _ rfl hres, rfl, rfl⟩

/-! ### Part 3: `List_lookup (addNode)` -/

private def NodeBucketListRep (jh : Jvm.JvmHeap AlgExt) :
    List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32) → JvmVal → Prop
  | [], .heapRef addr =>
    ∃ cls elems, jh.get? addr = some (.objArray cls elems) ∧
      elems[0]? = some (.boxedInt 0)
  | (hk, hv) :: tl, .heapRef addr =>
    ∃ cls elems tlVal, jh.get? addr = some (.objArray cls elems) ∧
      elems[0]? = some (.boxedInt 1) ∧
      elems[1]? = some (.pair (encodeNodeKey hk) (.boxedUInt hv)) ∧
      elems[2]? = some tlVal ∧
      NodeBucketListRep jh tl tlVal
  | _, _ => False

private theorem NodeBucketListRep.mono_alloc {jh : Jvm.JvmHeap AlgExt} {obj : Jvm.HeapObj AlgExt}
    {xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)} {v : JvmVal}
    (hrep : NodeBucketListRep jh xs v) : NodeBucketListRep (jh.alloc obj).2 xs v := by
  induction xs generalizing v with
  | nil =>
    cases v <;> simp only [NodeBucketListRep] at hrep ⊢
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, hget, h0⟩
      exact ⟨cls, elems,
        by rw [jvmHeap_get?_alloc_lt jh obj (jvmHeap_addr_lt_of_get? hget)]; exact hget, h0⟩
  | cons hd tl ih =>
    rcases hd with ⟨hk, hv⟩
    cases v <;> simp only [NodeBucketListRep] at hrep ⊢
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, tlVal, hget, h0, h1, h2, htl⟩
      exact ⟨cls, elems, tlVal,
        by rw [jvmHeap_get?_alloc_lt jh obj (jvmHeap_addr_lt_of_get? hget)]; exact hget,
        h0, h1, h2, ih htl⟩

private theorem encodeNodeBucketList_rep (jh : Jvm.JvmHeap AlgExt)
    (xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)) :
    NodeBucketListRep (encodeNodeBucketList jh xs).2 xs
      (encodeNodeBucketList jh xs).1 := by
  induction xs with
  | nil =>
    dsimp only [encodeNodeBucketList, NodeBucketListRep]
    exact ⟨"java/lang/Object", #[.boxedInt 0], jvmHeap_get?_alloc_self _ _, rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    dsimp only [encodeNodeBucketList, NodeBucketListRep]
    exact ⟨"java/lang/Object",
      #[.boxedInt 1, .pair (encodeNodeKey k) (.boxedUInt v),
        (encodeNodeBucketList jh tl).1],
      (encodeNodeBucketList jh tl).1, jvmHeap_get?_alloc_self _ _, rfl, rfl, rfl,
      NodeBucketListRep.mono_alloc ih⟩

private abbrev progAN : List JvmInstr :=
  f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg_prog

private theorem addNode_stage0_nil (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (cls : String) (elems : Array JvmVal)
    (hl1 : locs 1 = .heapRef addr)
    (hget : jh.get? addr = some (.objArray cls elems))
    (h0 : elems[0]? = some (.boxedInt 0)) :
    ∃ locs',
      runJvmResFast 25 progAN 3 (progAN.drop 3) ⟨3, [], locs, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨27, [.heapRef jh.objects.size], locs',
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩) := by
  apply Exists.intro
  · rw [show (25 : Nat) = 12 + 13 from rfl]
    step_drop_at 13
    step1_load 1 (.heapRef addr), hl1
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 1 (.heapRef addr), hl1
    rw [runJvmResFast_checkcast_objArray_any hget]
    step1
    rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h0)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
    rw [runJvmResFast_tableswitch]
    rw [show Jvm.tableswitchTarget 0 0 [16, 28] 345 = 16 from by decide]
    dsimp only
    step_drop_at 12
    rw [show (12 : Nat) = 1 + 11 from rfl]
    step1
    rw [runJvmResFast_anewarray_obj (by decide)]
    step1; step1; step1; step1
    rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
    have hgetNew : ((jh.alloc (.objArray "java/lang/Object"
        (Array.replicate (UInt32.toNat 1) .null))).2).get? jh.objects.size =
        some (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 1) .null)) :=
      jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore (idx := 0) hgetNew (by decide) (by decide)]
    step1; step1; step1
    rw [alloc_obj1_set]
    exact runJvmResFast_areturn

private theorem addNode_stage0_cons {f : Nat} (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (addr : Nat) (cls : String) (elems : Array JvmVal)
    (hl1 : locs 1 = .heapRef addr)
    (hget : jh.get? addr = some (.objArray cls elems))
    (h0 : elems[0]? = some (.boxedInt 1)) :
    runJvmResFast (f + 13) progAN 3 (progAN.drop 3) ⟨3, [], locs, jh, hp⟩ =
      runJvmResFast f progAN 28 (progAN.drop 28) ⟨28, [], locs, jh, hp⟩ := by
  step_drop_at 13
  step1_load 1 (.heapRef addr), hl1
  step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1_load 1 (.heapRef addr), hl1
  rw [runJvmResFast_checkcast_objArray_any hget]
  step1
  rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h0)]
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
  rw [runJvmResFast_tableswitch]
  rw [show Jvm.tableswitchTarget 1 0 [16, 28] 345 = 28 from by decide]

private theorem addNode_stage1_eq {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {addr : Nat} {cls : String} {elems : Array JvmVal}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k) (hl1 : locs 1 = .heapRef addr)
    (hget : jh.get? addr = some (.objArray cls elems))
    (h1 : elems[1]? = some (.pair (encodeNodeKey hk) (.boxedUInt hv)))
    (h2 : elems[2]? = some tlVal)
    (heq : k.1 = hk.1)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 4 = tlVal →
      locs1 5 = .boxedUInt hv →
      locs1 6 = .pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
        (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))) →
      locs1 7 = .pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
        (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))) →
      ∃ f1 locs', runJvmResFast f1 progAN 124 (progAN.drop 124) ⟨124, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 28 (progAN.drop 28) ⟨28, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_nw : JvmVal := .pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))
  let hk_nw_p : JvmVal := .pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))
  let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal locs 2 (.pair (encodeNodeKey hk) (.boxedUInt hv)))
      3 (encodeNodeKey hk)) 4 tlVal) 5 (.boxedUInt hv)) 6 p_nw) 7 hk_nw_p)
      9 (.boxedUInt hk.1)) 10 (.i32 0)) 8 (.i32 hk.1)
  obtain ⟨f1, locs', h1_run⟩ := hcont locs1
    (by simp [locs1, setLocal, hl0]) (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
    (by simp [locs1, setLocal, p_nw]) (by simp [locs1, setLocal, hk_nw_p])
  refine ⟨f1 + 64, locs', ?_⟩
  rw [show f1 + 64 = (f1 + 52) + 12 from by omega]
  step_drop_at 12
  step1_load 1 (.heapRef addr), hl1
  rw [runJvmResFast_checkcast_objArray_any hget]
  step1
  rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h1)]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 13
  rw [show f1 + 52 = (f1 + 39) + 13 from by omega]
  step1
  step1_load 1 (.heapRef addr), (by simp [hl1, setLocal])
  rw [runJvmResFast_checkcast_objArray_any hget]
  step1
  rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h2)]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 12
  rw [show f1 + 39 = (f1 + 27) + 12 from by omega]
  step1
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  dsimp only [encodeNodeKey]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 27 = (f1 + 19) + 8 from by omega]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 19 = (f1 + 13) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 13
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  dsimp only [encodeNodeKey]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_branch heq]
  exact h1_run

private theorem addNode_stage1_ne {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {addr : Nat} {cls : String} {elems : Array JvmVal}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k) (hl1 : locs 1 = .heapRef addr)
    (hget : jh.get? addr = some (.objArray cls elems))
    (h1 : elems[1]? = some (.pair (encodeNodeKey hk) (.boxedUInt hv)))
    (h2 : elems[2]? = some tlVal)
    (hne : (k.1 == hk.1) = false)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 1 = tlVal →
      ∃ f1 locs', runJvmResFast f1 progAN 3 (progAN.drop 3) ⟨3, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 28 (progAN.drop 28) ⟨28, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_nw : JvmVal := .pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))
  let hk_nw_p : JvmVal := .pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal locs 2 (.pair (encodeNodeKey hk) (.boxedUInt hv)))
      3 (encodeNodeKey hk)) 4 tlVal) 5 (.boxedUInt hv)) 6 p_nw) 7 hk_nw_p)
      9 (.boxedUInt hk.1)) 10 (.i32 0)) 8 (.i32 hk.1)
  let locs1 := setLocal (setLocal locsMid 0 (encodeNodeKey k)) 1 tlVal
  obtain ⟨f1, locs', h1_run⟩ :=
    hcont locs1 (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 69, locs', ?_⟩
  rw [show f1 + 69 = (f1 + 57) + 12 from by omega]
  step_drop_at 12
  step1_load 1 (.heapRef addr), hl1
  rw [runJvmResFast_checkcast_objArray_any hget]
  step1
  rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h1)]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 13
  rw [show f1 + 57 = (f1 + 44) + 13 from by omega]
  step1
  step1_load 1 (.heapRef addr), (by simp [hl1, setLocal])
  rw [runJvmResFast_checkcast_objArray_any hget]
  step1
  rw [runJvmResFast_aaload_elem hget (by decide) (by simpa using h2)]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 12
  rw [show f1 + 44 = (f1 + 32) + 12 from by omega]
  step1
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  dsimp only [encodeNodeKey]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 32 = (f1 + 24) + 8 from by omega]
  step1; step1
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 24 = (f1 + 18) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 18
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  dsimp only [encodeNodeKey]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_fallthrough hne]
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  step1
  step1_load 4 tlVal, (by simp [setLocal])
  step1
  rw [runJvmResFast_goto]
  exact h1_run

private theorem addNode_stage2_eq {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal) (hl5 : locs 5 = .boxedUInt hv)
    (hl6 : locs 6 = .pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
      (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))))
    (hl7 : locs 7 = .pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
      (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))))
    (heq : k.2.1 = hk.2.1)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 4 = tlVal →
      locs1 5 = .boxedUInt hv →
      locs1 9 = .pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)) →
      locs1 10 = .pair (.boxedUInt hk.2.2.1) (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)) →
      ∃ f1 locs', runJvmResFast f1 progAN 183 (progAN.drop 183) ⟨183, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 124 (progAN.drop 124) ⟨124, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_ne : JvmVal :=
    .pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))
  let hk_ne_p : JvmVal :=
    .pair (.boxedUInt hk.2.2.1) (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))
  let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal locs 9 p_ne) 10 hk_ne_p)
    12 (.boxedUInt hk.2.1)) 13 (.i32 0)) 11 (.i32 hk.2.1)
  obtain ⟨f1, locs', h1_run⟩ := hcont locs1
    (by simp [locs1, setLocal, hl0]) (by simp [locs1, setLocal, hl4])
    (by simp [locs1, setLocal, hl5]) (by simp [locs1, setLocal, p_ne])
    (by simp [locs1, setLocal, hk_ne_p])
  refine ⟨f1 + 38, locs', ?_⟩
  rw [show f1 + 38 = (f1 + 27) + 11 from by omega]
  step_drop_at 11
  step1_load 6 (.pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))), hl6
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 27 = (f1 + 19) + 8 from by omega]
  step1
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 19 = (f1 + 13) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 13
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 6 (.pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))), (by simp [hl6, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_branch heq]
  exact h1_run

private theorem addNode_stage2_ne {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal)
    (hl6 : locs 6 = .pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
      (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))))
    (hl7 : locs 7 = .pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
      (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))))
    (hne : (k.2.1 == hk.2.1) = false)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 1 = tlVal →
      ∃ f1 locs', runJvmResFast f1 progAN 3 (progAN.drop 3) ⟨3, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 124 (progAN.drop 124) ⟨124, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_ne : JvmVal :=
    .pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))
  let hk_ne_p : JvmVal :=
    .pair (.boxedUInt hk.2.2.1) (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs 9 p_ne) 10 hk_ne_p)
    12 (.boxedUInt hk.2.1)) 13 (.i32 0)) 11 (.i32 hk.2.1)
  let locs1 := setLocal (setLocal locsMid 0 (encodeNodeKey k)) 1 tlVal
  obtain ⟨f1, locs', h1_run⟩ :=
    hcont locs1 (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 43, locs', ?_⟩
  rw [show f1 + 43 = (f1 + 32) + 11 from by omega]
  step_drop_at 11
  step1_load 6 (.pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))), hl6
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 32 = (f1 + 24) + 8 from by omega]
  step1
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 7 (.pair (.boxedUInt hk.2.1) (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))), (by simp [hl7, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 24 = (f1 + 18) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 18
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 6 (.pair (.boxedUInt k.2.1) (.pair (.boxedUInt k.2.2.1)
    (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))), (by simp [hl6, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_fallthrough hne]
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  step1
  step1_load 4 tlVal, (by simp [hl4, setLocal])
  step1
  rw [runJvmResFast_goto]
  exact h1_run

private theorem addNode_stage3_eq {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal) (hl5 : locs 5 = .boxedUInt hv)
    (hl9 : locs 9 = .pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))
    (hl10 : locs 10 = .pair (.boxedUInt hk.2.2.1)
      (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))
    (heq : k.2.2.1 = hk.2.2.1)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 4 = tlVal →
      locs1 5 = .boxedUInt hv →
      locs1 12 = .pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2) →
      locs1 13 = .pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2) →
      ∃ f1 locs', runJvmResFast f1 progAN 242 (progAN.drop 242) ⟨242, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 183 (progAN.drop 183) ⟨183, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_swse : JvmVal := .pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)
  let hk_swse_p : JvmVal := .pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)
  let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal locs 12 p_swse) 13 hk_swse_p)
    15 (.boxedUInt hk.2.2.1)) 16 (.i32 0)) 14 (.i32 hk.2.2.1)
  obtain ⟨f1, locs', h1_run⟩ := hcont locs1
    (by simp [locs1, setLocal, hl0]) (by simp [locs1, setLocal, hl4])
    (by simp [locs1, setLocal, hl5]) (by simp [locs1, setLocal, p_swse])
    (by simp [locs1, setLocal, hk_swse_p])
  refine ⟨f1 + 38, locs', ?_⟩
  rw [show f1 + 38 = (f1 + 27) + 11 from by omega]
  step_drop_at 11
  step1_load 9 (.pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1)
    (.boxedUInt k.2.2.2.2))), hl9
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 27 = (f1 + 19) + 8 from by omega]
  step1
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 19 = (f1 + 13) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 13
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 9 (.pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1)
    (.boxedUInt k.2.2.2.2))), (by simp [hl9, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_branch heq]
  exact h1_run

private theorem addNode_stage3_ne {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal)
    (hl9 : locs 9 = .pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)))
    (hl10 : locs 10 = .pair (.boxedUInt hk.2.2.1)
      (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)))
    (hne : (k.2.2.1 == hk.2.2.1) = false)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 1 = tlVal →
      ∃ f1 locs', runJvmResFast f1 progAN 3 (progAN.drop 3) ⟨3, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 183 (progAN.drop 183) ⟨183, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let p_swse : JvmVal := .pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)
  let hk_swse_p : JvmVal := .pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs 12 p_swse) 13 hk_swse_p)
    15 (.boxedUInt hk.2.2.1)) 16 (.i32 0)) 14 (.i32 hk.2.2.1)
  let locs1 := setLocal (setLocal locsMid 0 (encodeNodeKey k)) 1 tlVal
  obtain ⟨f1, locs', h1_run⟩ :=
    hcont locs1 (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 43, locs', ?_⟩
  rw [show f1 + 43 = (f1 + 32) + 11 from by omega]
  step_drop_at 11
  step1_load 9 (.pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1)
    (.boxedUInt k.2.2.2.2))), hl9
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_pair]
  step1
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 32 = (f1 + 24) + 8 from by omega]
  step1
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 10 (.pair (.boxedUInt hk.2.2.1)
    (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))), (by simp [hl10, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 24 = (f1 + 18) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 18
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 9 (.pair (.boxedUInt k.2.2.1) (.pair (.boxedUInt k.2.2.2.1)
    (.boxedUInt k.2.2.2.2))), (by simp [hl9, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_fallthrough hne]
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  step1
  step1_load 4 tlVal, (by simp [hl4, setLocal])
  step1
  rw [runJvmResFast_goto]
  exact h1_run

private theorem addNode_stage4_eq {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal) (hl5 : locs 5 = .boxedUInt hv)
    (hl12 : locs 12 = .pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))
    (hl13 : locs 13 = .pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))
    (heq : k.2.2.2.1 = hk.2.2.2.1)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 4 = tlVal →
      locs1 5 = .boxedUInt hv →
      locs1 15 = .i32 k.2.2.2.2 →
      locs1 16 = .boxedUInt hk.2.2.2.2 →
      ∃ f1 locs', runJvmResFast f1 progAN 302 (progAN.drop 302) ⟨302, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 242 (progAN.drop 242) ⟨242, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal locs 15 (.i32 k.2.2.2.2))
    16 (.boxedUInt hk.2.2.2.2)) 18 (.boxedUInt hk.2.2.2.1)) 19 (.i32 0)) 17 (.i32 hk.2.2.2.1)
  obtain ⟨f1, locs', h1_run⟩ := hcont locs1
    (by simp [locs1, setLocal, hl0]) (by simp [locs1, setLocal, hl4])
    (by simp [locs1, setLocal, hl5]) (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 39, locs', ?_⟩
  rw [show f1 + 39 = (f1 + 27) + 12 from by omega]
  step_drop_at 12
  step1_load 12 (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)), hl12
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 27 = (f1 + 19) + 8 from by omega]
  step1
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 19 = (f1 + 13) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 13
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 12 (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)), (by simp [hl12, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_branch heq]
  exact h1_run

private theorem addNode_stage4_ne {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal)
    (hl12 : locs 12 = .pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2))
    (hl13 : locs 13 = .pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2))
    (hne : (k.2.2.2.1 == hk.2.2.2.1) = false)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 1 = tlVal →
      ∃ f1 locs', runJvmResFast f1 progAN 3 (progAN.drop 3) ⟨3, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 242 (progAN.drop 242) ⟨242, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs 15 (.i32 k.2.2.2.2))
    16 (.boxedUInt hk.2.2.2.2)) 18 (.boxedUInt hk.2.2.2.1)) 19 (.i32 0)) 17 (.i32 hk.2.2.2.1)
  let locs1 := setLocal (setLocal locsMid 0 (encodeNodeKey k)) 1 tlVal
  obtain ⟨f1, locs', h1_run⟩ :=
    hcont locs1 (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 44, locs', ?_⟩
  rw [show f1 + 44 = (f1 + 32) + 12 from by omega]
  step_drop_at 12
  step1_load 12 (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)), hl12
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
  rw [runJvmResFast_goto]
  step_drop_at 8
  rw [show f1 + 32 = (f1 + 24) + 8 from by omega]
  step1
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_instanceof_pair]
  rw [runJvmResFast_ifeq_fallthrough (by decide)]
  step1_load 13 (.pair (.boxedUInt hk.2.2.2.1) (.boxedUInt hk.2.2.2.2)), (by simp [hl13, setLocal])
  rw [runJvmResFast_checkcast_pair]
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_goto]
  step_drop_at 6
  rw [show f1 + 24 = (f1 + 18) + 6 from by omega]
  step1; step1; step1; step1
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 18
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 12 (.pair (.boxedUInt k.2.2.2.1) (.boxedUInt k.2.2.2.2)), (by simp [hl12, setLocal])
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  rw [runJvmResFast_if_icmpeq_fallthrough hne]
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  step1
  step1_load 4 tlVal, (by simp [hl4, setLocal])
  step1
  rw [runJvmResFast_goto]
  exact h1_run

private theorem addNode_stage5_eq {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {hv : UInt32} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl5 : locs 5 = .boxedUInt hv)
    (hl15 : locs 15 = .i32 k.2.2.2.2)
    (hl16 : locs 16 = .boxedUInt hk.2.2.2.2)
    (heq : k.2.2.2.2 = hk.2.2.2.2) :
    ∃ f2 locs', runJvmResFast f2 progAN 302 (progAN.drop 302) ⟨302, [], locs, jh, hp⟩ =
      some (.heapRef jh.objects.size, ⟨344, [.heapRef jh.objects.size], locs',
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt hv])).2, hp⟩) := by
  suffices hs : ∃ locs',
      runJvmResFast 33 progAN 302 (progAN.drop 302) ⟨302, [], locs, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨344, [.heapRef jh.objects.size], locs',
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt hv])).2, hp⟩) by
    obtain ⟨locs', hs⟩ := hs
    exact ⟨33, locs', hs⟩
  apply Exists.intro
  · rw [show (33 : Nat) = 26 + 7 from rfl]
    step_drop_at 7
    step1_load 16 (.boxedUInt hk.2.2.2.2), hl16
    step1; step1; step1
    step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
    rw [runJvmResFast_instanceof_boxedUInt_int]
    rw [runJvmResFast_ifeq_branch rfl]
    step_drop_at 10
    rw [show (26 : Nat) = 16 + 10 from rfl]
    step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
    step1
    step1_load 15 (.i32 k.2.2.2.2), (by simp [hl15, setLocal])
    step1
    rw [runJvmResFast_if_icmpeq_branch heq]
    step_drop_at 16
    rw [show (16 : Nat) = 1 + 15 from rfl]
    step1
    rw [runJvmResFast_anewarray_obj (by decide)]
    step1; step1; step1; step1
    rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
    have hgetNew : ((jh.alloc (.objArray "java/lang/Object"
        (Array.replicate (UInt32.toNat 2) .null))).2).get? jh.objects.size =
        some (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 2) .null)) :=
      jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore (idx := 0) hgetNew (by decide) (by decide)]
    rw [alloc_obj2_step0]
    step1; step1
    step1_load 5 (.boxedUInt hv), (by simp [hl5, setLocal])
    have hgetNew2 : ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2).get?
        jh.objects.size =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) :=
      jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore (idx := 1) hgetNew2 (by decide) (by decide)]
    rw [alloc_obj2_step1]
    step1; step1; step1
    exact runJvmResFast_areturn

private theorem addNode_stage5_ne {k hk : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {tlVal : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {retVal : JvmVal} {pcRet : Nat} {jh' : Jvm.JvmHeap AlgExt}
    (hl0 : locs 0 = encodeNodeKey k)
    (hl4 : locs 4 = tlVal)
    (hl15 : locs 15 = .i32 k.2.2.2.2)
    (hl16 : locs 16 = .boxedUInt hk.2.2.2.2)
    (hne : (k.2.2.2.2 == hk.2.2.2.2) = false)
    (hcont : ∀ locs1,
      locs1 0 = encodeNodeKey k →
      locs1 1 = tlVal →
      ∃ f1 locs', runJvmResFast f1 progAN 3 (progAN.drop 3) ⟨3, [], locs1, jh, hp⟩ =
        some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩)) :
    ∃ f2 locs', runJvmResFast f2 progAN 302 (progAN.drop 302) ⟨302, [], locs, jh, hp⟩ =
      some (retVal, ⟨pcRet, [retVal], locs', jh', hp⟩) := by
  let locsMid := setLocal (setLocal (setLocal locs 19 (.boxedUInt hk.2.2.2.2))
    20 (.i32 0)) 18 (.i32 hk.2.2.2.2)
  let locs1 := setLocal (setLocal locsMid 0 (encodeNodeKey k)) 1 tlVal
  obtain ⟨f1, locs', h1_run⟩ :=
    hcont locs1 (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
  refine ⟨f1 + 22, locs', ?_⟩
  rw [show f1 + 22 = (f1 + 15) + 7 from by omega]
  step_drop_at 7
  step1_load 16 (.boxedUInt hk.2.2.2.2), hl16
  step1; step1; step1
  step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl]
  step_drop_at 15
  step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
  step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1_load 19 (.boxedUInt hk.2.2.2.2), (by simp [setLocal])
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
  step1
  step1_load 15 (.i32 k.2.2.2.2), (by simp [hl15, setLocal])
  step1
  rw [runJvmResFast_if_icmpeq_fallthrough hne]
  step1_load 0 (encodeNodeKey k), (by simp [hl0, setLocal])
  step1
  step1_load 4 tlVal, (by simp [hl4, setLocal])
  step1
  rw [runJvmResFast_goto]
  exact h1_run

private theorem nodeKey_beq_true_iff
    {a b : UInt32 × UInt32 × UInt32 × UInt32 × UInt32} :
    (a == b) = true ↔
      a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ a.2.2.2.1 = b.2.2.2.1 ∧
        a.2.2.2.2 = b.2.2.2.2 := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  simp [beq_iff_eq]

private theorem list_lookup_addNode_aux
    (xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32))
    (k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (listVal : JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hl0 : locs 0 = encodeNodeKey k) (hl1 : locs 1 = listVal)
    (hrep : NodeBucketListRep jh xs listVal) :
    ∃ (f : Nat) (locs' : Nat → JvmVal),
      let retObj : Jvm.HeapObj AlgExt := match xs.lookup k with
        | none => .objArray "java/lang/Object" #[.boxedInt 0]
        | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v]
      let pc' : Nat := match xs.lookup k with
        | none => 27
        | some _ => 344
      runJvmResFast f progAN 3 (progAN.drop 3) ⟨3, [], locs, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨pc', [.heapRef jh.objects.size], locs',
          (jh.alloc retObj).2, hp⟩) := by
  induction xs generalizing listVal locs with
  | nil =>
    cases listVal
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, hget, h0⟩
      obtain ⟨locs', hs⟩ := addNode_stage0_nil locs jh hp addr cls elems hl1 hget h0
      exact ⟨25, locs', hs⟩
    all_goals exact False.elim hrep
  | cons hd tl ih =>
    rcases hd with ⟨hk, hv⟩
    cases listVal
    case heapRef addr =>
      rcases hrep with ⟨cls, elems, tlVal, hget, h0, h1, h2, htl⟩
      by_cases heq : k == hk
      · have hke : k.1 = hk.1 ∧ k.2.1 = hk.2.1 ∧ k.2.2.1 = hk.2.2.1 ∧
            k.2.2.2.1 = hk.2.2.2.1 ∧ k.2.2.2.2 = hk.2.2.2.2 :=
          nodeKey_beq_true_iff.mp heq
        rcases hke with ⟨he1, he2, he3, he4, he5⟩
        obtain ⟨f, locs', hsuf⟩ :=
          addNode_stage1_eq hl0 hl1 hget h1 h2 he1 fun l1 h10 h14 h15 h16 h17 =>
            addNode_stage2_eq h10 h14 h15 h16 h17 he2 fun l2 h20 h24 h25 h29 h210 =>
              addNode_stage3_eq h20 h24 h25 h29 h210 he3 fun l3 h30 h34 h35 h312 h313 =>
                addNode_stage4_eq h30 h34 h35 h312 h313 he4 fun l4 _ _ h45 h415 h416 =>
                  addNode_stage5_eq h45 h415 h416 he5
        refine ⟨f + 13, locs', ?_⟩
        simp only [List.lookup, heq]
        rw [addNode_stage0_cons locs jh hp addr cls elems hl1 hget h0]
        exact hsuf
      · have hne : (k == hk) = false := Bool.eq_false_of_ne_true heq
        have hrec := fun l h0r h1r => ih tlVal l h0r h1r htl
        simp only [List.lookup, hne] at hrec ⊢
        have hsuf : ∃ f locs',
            runJvmResFast f progAN 28 (progAN.drop 28) ⟨28, [], locs, jh, hp⟩ =
              some (.heapRef jh.objects.size, ⟨
                match tl.lookup k with | none => 27 | some _ => 344,
                [.heapRef jh.objects.size], locs',
                (jh.alloc (match tl.lookup k with
                  | none => .objArray "java/lang/Object" #[.boxedInt 0]
                  | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v])).2,
                hp⟩) := by
          by_cases h1eq : k.1 == hk.1
          · have he1 : k.1 = hk.1 := beq_iff_eq.mp h1eq
            refine addNode_stage1_eq hl0 hl1 hget h1 h2 he1 fun l1 h10 h14 h15 h16 h17 => ?_
            by_cases h2eq : k.2.1 == hk.2.1
            · have he2 : k.2.1 = hk.2.1 := beq_iff_eq.mp h2eq
              refine addNode_stage2_eq h10 h14 h15 h16 h17 he2 fun l2 h20 h24 h25 h29 h210 => ?_
              by_cases h3eq : k.2.2.1 == hk.2.2.1
              · have he3 : k.2.2.1 = hk.2.2.1 := beq_iff_eq.mp h3eq
                refine addNode_stage3_eq h20 h24 h25 h29 h210 he3
                  fun l3 h30 h34 h35 h312 h313 => ?_
                by_cases h4eq : k.2.2.2.1 == hk.2.2.2.1
                · have he4 : k.2.2.2.1 = hk.2.2.2.1 := beq_iff_eq.mp h4eq
                  refine addNode_stage4_eq h30 h34 h35 h312 h313 he4
                    fun l4 h40 h44 _ h415 h416 => ?_
                  have h5ne : (k.2.2.2.2 == hk.2.2.2.2) = false := by
                    by_cases h5eq : k.2.2.2.2 == hk.2.2.2.2
                    · have he5 := beq_iff_eq.mp h5eq
                      have : (k == hk) = true := nodeKey_beq_true_iff.mpr ⟨he1, he2, he3, he4, he5⟩
                      rw [this] at hne
                      cases hne
                    · exact Bool.eq_false_of_ne_true h5eq
                  exact addNode_stage5_ne h40 h44 h415 h416 h5ne hrec
                · exact addNode_stage4_ne h30 h34 h312 h313 (Bool.eq_false_of_ne_true h4eq) hrec
              · exact addNode_stage3_ne h20 h24 h29 h210 (Bool.eq_false_of_ne_true h3eq) hrec
            · exact addNode_stage2_ne h10 h14 h16 h17 (Bool.eq_false_of_ne_true h2eq) hrec
          · exact addNode_stage1_ne hl0 hl1 hget h1 h2 (Bool.eq_false_of_ne_true h1eq) hrec
        obtain ⟨f, locs', hrun⟩ := hsuf
        refine ⟨f + 13, locs', ?_⟩
        rw [addNode_stage0_cons locs jh hp addr cls elems hl1 hget h0]
        exact hrun
    all_goals exact False.elim hrep

theorem list_lookup_addNode_equiv
    (xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32))
    (k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (listVal : JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hrep : NodeBucketListRep jh xs listVal) :
    let retObj : Jvm.HeapObj AlgExt := match xs.lookup k with
      | none => .objArray "java/lang/Object" #[.boxedInt 0]
      | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v]
    ∃ f st',
      runJvmRes f f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (encodeNodeKey k)) 1 listVal, jh, hp⟩ =
        some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap = (jh.alloc retObj).2 ∧ st'.heap = hp := by
  let locs0 := setLocal (setLocal (fun _ => .null) 0 (encodeNodeKey k)) 1 listVal
  obtain ⟨f, locs', hres⟩ := list_lookup_addNode_aux xs k listVal locs0 jh hp
    (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) hrep
  suffices hs : ∃ locs',
      runJvmResFast (f + 3) progAN 0 (progAN.drop 0)
        ⟨0, [], locs0, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨match xs.lookup k with | none => 27 | some _ => 344,
          [.heapRef jh.objects.size], locs',
          (jh.alloc (match xs.lookup k with
            | none => .objArray "java/lang/Object" #[.boxedInt 0]
            | some v => .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt v])).2, hp⟩) by
    obtain ⟨locs', hrun⟩ := hs
    exact ⟨f + 3, _, runJvmRes_of_runJvmResFast0 (f + 3) _ _ _ rfl hrun, rfl, rfl⟩
  refine ⟨locs', ?_⟩
  conv => lhs; arg 4; rw [show progAN = progAN.drop 0 from rfl]
  step_drop_at 3
  step1_load 0 (encodeNodeKey k), (by simp [locs0, setLocal])
  step1
  rw [runJvmResFast_checkNotNullParameter rfl]
  exact hres

/-! ### Part 4: `DagWriter.addLeafAt` and `DagWriter.addNodeAt` -/

private theorem foldlM_list_push_prefix {α β : Type} (f : α → Option β) (xs : List α)
    (init res : Array β)
    (h : xs.foldlM (fun acc x => (f x).map acc.push) init = some res) :
    ∀ j, j < init.size → res[j]? = init[j]? := by
  induction xs generalizing init with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact fun _ _ => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      simp only [hx, Option.map_some] at h
      intro j hj
      rw [ih (init.push b) h j (by simp; omega), Array.getElem?_push]
      simp [Nat.ne_of_lt hj]

private theorem foldlM_list_map_push {α β : Type} (f : α → Option β) (xs : List α)
    (init res : Array β)
    (h : xs.foldlM (fun acc x => (f x).map acc.push) init = some res) :
    res.size = init.size + xs.length ∧
      ∀ (i : Nat) (hi : i < xs.length),
        ∃ b, f xs[i] = some b ∧ res[init.size + i]? = some b := by
  induction xs generalizing init with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨by simp, fun i hi => by simp at hi⟩
  | cons x xs ih =>
    simp only [List.foldlM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      simp only [hx, Option.map_some] at h
      obtain ⟨hsz, hget⟩ := ih (init.push b) h
      refine ⟨by simp only [Array.size_push] at hsz; simp only [List.length_cons]; omega,
        fun i hi => ?_⟩
      cases i with
      | zero =>
        refine ⟨b, hx, ?_⟩
        rw [Nat.add_zero]
        have hpref := foldlM_list_push_prefix f xs (init.push b) res h init.size (by simp)
        rw [hpref, Array.getElem?_push]
        simp
      | succ i' =>
        have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
        obtain ⟨b', hb', hr⟩ := hget i' hi'
        refine ⟨b', hb', ?_⟩
        rw [show init.size + (i' + 1) = (init.push b).size + i' by simp; omega]
        exact hr

private theorem foldlM_array_map_push {α β : Type} (f : α → Option β) (xs : Array α)
    (res : Array β)
    (h : xs.foldlM (fun acc x => (f x).map acc.push) #[] = some res) :
    res.size = xs.size ∧
      ∀ (i : Nat) (hi : i < xs.size), ∃ (hlt : i < res.size), f xs[i] = some (res[i]'hlt) := by
  rw [← Array.foldlM_toList] at h
  obtain ⟨hsz, hget⟩ := foldlM_list_map_push f xs.toList #[] res h
  have hsz' : res.size = xs.size := by
    rw [hsz, Array.size_empty, Nat.zero_add, Array.length_toList]
  refine ⟨hsz', fun i hi => ⟨by omega, ?_⟩⟩
  have hiList : i < xs.toList.length := by rw [← Array.size_eq_length_toList]; exact hi
  obtain ⟨b, hb, hr⟩ := hget i hiList
  simp only [Array.size_empty, Nat.zero_add] at hr
  have hrb : res[i]'(by omega) = b := by
    rw [getElem?_pos res i (by omega), Option.some.injEq] at hr
    exact hr
  rw [hrb]
  simpa using hb

private theorem decodeDagWriter_unpack {jh : Jvm.JvmHeap AlgExt} {wAddr : Nat}
    {w : Algorithm.DagWriter} (hdec : decodeDagWriter jh (.heapRef wAddr) = some w) :
    ∃ wCls wElems lAddr lCls lBuckets nAddr nCls nBuckets,
      jh.get? wAddr = some (.objArray wCls wElems) ∧
      wElems[1]? = some (.ext (.strGrowBuf w.lines)) ∧
      wElems[2]? = some (.heapRef lAddr) ∧
      wElems[3]? = some (.heapRef nAddr) ∧
      jh.get? lAddr = some (.objArray lCls lBuckets) ∧
      jh.get? nAddr = some (.objArray nCls nBuckets) ∧
      lBuckets.size = w.leafT.size ∧
      nBuckets.size = w.nodeT.size ∧
      (∀ (i : Nat) (hi : i < lBuckets.size),
        ∃ (hlt : i < w.leafT.size),
          decodeLeafBucketList jh (jh.objects.size + 2) lBuckets[i] = some (w.leafT[i]'hlt)) ∧
      (∀ (i : Nat) (hi : i < nBuckets.size),
        ∃ (hlt : i < w.nodeT.size),
          decodeNodeBucketList jh (jh.objects.size + 2) nBuckets[i] = some (w.nodeT[i]'hlt)) := by
  dsimp [decodeDagWriter] at hdec
  obtain ⟨wObj, hgw⟩ : ∃ wObj, jh.get? wAddr = some wObj := by
    cases h : jh.get? wAddr <;> simp_all
  simp only [hgw] at hdec
  obtain ⟨wCls, wElems, rfl⟩ : ∃ c e, wObj = .objArray c e := by
    cases wObj <;> simp_all
  obtain ⟨v1, he1⟩ : ∃ v1, wElems[1]? = some v1 := by
    cases h : wElems[1]? <;> simp_all
  obtain ⟨v2, he2⟩ : ∃ v2, wElems[2]? = some v2 := by
    cases h : wElems[2]? <;> simp_all
  obtain ⟨v3, he3⟩ : ∃ v3, wElems[3]? = some v3 := by
    cases h : wElems[3]? <;> simp_all
  simp only [he1, he2, he3] at hdec
  obtain ⟨lines, rfl⟩ : ∃ lines, v1 = .ext (.strGrowBuf lines) := by
    cases v1 with
    | ext ex => cases ex <;> simp_all
    | _ => simp_all
  obtain ⟨lAddr, rfl⟩ : ∃ lAddr, v2 = .heapRef lAddr := by
    cases v2 <;> simp_all
  obtain ⟨nAddr, rfl⟩ : ∃ nAddr, v3 = .heapRef nAddr := by
    cases v3 <;> simp_all
  dsimp only at hdec
  obtain ⟨lObj, hgl⟩ : ∃ lObj, jh.get? lAddr = some lObj := by
    cases h : jh.get? lAddr <;> simp_all
  obtain ⟨lCls, lBuckets, rfl⟩ : ∃ c e, lObj = .objArray c e := by
    cases lObj <;> simp_all
  obtain ⟨nObj, hgn⟩ : ∃ nObj, jh.get? nAddr = some nObj := by
    cases h : jh.get? nAddr <;> simp_all
  obtain ⟨nCls, nBuckets, rfl⟩ : ∃ c e, nObj = .objArray c e := by
    cases nObj <;> simp_all
  simp only [hgl, hgn] at hdec
  obtain ⟨leafT, hlbt⟩ : ∃ leafT,
      lBuckets.foldlM
        (fun acc v => (decodeLeafBucketList jh (jh.objects.size + 2) v).map acc.push) #[] =
        some leafT := by
    cases h : lBuckets.foldlM
      (fun acc v => (decodeLeafBucketList jh (jh.objects.size + 2) v).map acc.push) #[] <;>
      simp_all
  simp only [hlbt, Option.bind_some] at hdec
  obtain ⟨nodeT, hnbt⟩ : ∃ nodeT,
      nBuckets.foldlM
        (fun acc v => (decodeNodeBucketList jh (jh.objects.size + 2) v).map acc.push) #[] =
        some nodeT := by
    cases h : nBuckets.foldlM
      (fun acc v => (decodeNodeBucketList jh (jh.objects.size + 2) v).map acc.push) #[] <;>
      simp_all
  simp only [hnbt, Option.bind_some, Option.some.injEq] at hdec
  subst hdec
  obtain ⟨hlSz, hlGet⟩ := foldlM_array_map_push
    (fun v => decodeLeafBucketList jh (jh.objects.size + 2) v) lBuckets leafT hlbt
  obtain ⟨hnSz, hnGet⟩ := foldlM_array_map_push
    (fun v => decodeNodeBucketList jh (jh.objects.size + 2) v) nBuckets nodeT hnbt
  exact ⟨wCls, wElems, lAddr, lCls, lBuckets, nAddr, nCls, nBuckets,
    hgw, he1, he2, he3, hgl, hgn, hlSz.symm, hnSz.symm, hlGet, hnGet⟩

private theorem stepStatic_listLookup_addLeaf
    {pc : Nat} {leaf : UInt64} {listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {xs : List (UInt64 × UInt32)}
    (hlist : decodeLeafBucketList jh (jh.objects.size + 2) listVal = some xs) :
    stepInvokeStatic ⟨pc, listVal :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg-4PLdz1A"
      "(JLjava/lang/Object;)Ljava/lang/Object;" =
      match xs.lookup leaf with
      | none => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩)
      | some id => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, listVal :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg-4PLdz1A"
      "(JLjava/lang/Object;)Ljava/lang/Object;" =
      match decodeLeafBucketList jh (jh.objects.size + 2) listVal with
      | some xs =>
        match xs.lookup leaf with
        | none => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
            (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩)
        | some id => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
            (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩)
      | none => .inr none := rfl
  rw [h0, hlist]

private theorem stepStatic_listLookup_addLeaf_hit
    {pc : Nat} {leaf : UInt64} {listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {xs : List (UInt64 × UInt32)} {id : UInt32}
    (hlist : decodeLeafBucketList jh (jh.objects.size + 2) listVal = some xs)
    (hhit : xs.lookup leaf = some id) :
    stepInvokeStatic ⟨pc, listVal :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg-4PLdz1A"
      "(JLjava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩) := by
  rw [stepStatic_listLookup_addLeaf hlist, hhit]

private theorem stepStatic_listLookup_addLeaf_miss
    {pc : Nat} {leaf : UInt64} {listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {xs : List (UInt64 × UInt32)}
    (hlist : decodeLeafBucketList jh (jh.objects.size + 2) listVal = some xs)
    (hmiss : xs.lookup leaf = none) :
    stepInvokeStatic ⟨pc, listVal :: .i64 leaf :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addLeaf_spec__0___redArg-4PLdz1A"
      "(JLjava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩) := by
  rw [stepStatic_listLookup_addLeaf hlist, hmiss]

private theorem stepStatic_listLookup_addNode
    {pc : Nat} {kVal listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)}
    (hk : decodeNodeKey kVal = some k)
    (hlist : decodeNodeBucketList jh (jh.objects.size + 2) listVal = some xs) :
    stepInvokeStatic ⟨pc, listVal :: kVal :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg"
      "(Lkotlin/Pair;Ljava/lang/Object;)Ljava/lang/Object;" =
      match xs.lookup k with
      | none => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩)
      | some id => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
          (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, listVal :: kVal :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg"
      "(Lkotlin/Pair;Ljava/lang/Object;)Ljava/lang/Object;" =
      match decodeNodeKey kVal, decodeNodeBucketList jh (jh.objects.size + 2) listVal with
      | some k, some xs =>
        match xs.lookup k with
        | none => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
            (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩)
        | some id => .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
            (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩)
      | _, _ => .inr none := rfl
  rw [h0, hk, hlist]

private theorem stepStatic_listLookup_addNode_hit
    {pc : Nat} {kVal listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)} {id : UInt32}
    (hk : decodeNodeKey kVal = some k)
    (hlist : decodeNodeBucketList jh (jh.objects.size + 2) listVal = some xs)
    (hhit : xs.lookup k = some id) :
    stepInvokeStatic ⟨pc, listVal :: kVal :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg"
      "(Lkotlin/Pair;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2, hp⟩) := by
  have h := stepStatic_listLookup_addNode (pc := pc) (rest := rest) (locs := locs) (hp := hp) hk hlist
  simp only [hhit] at h
  exact h

private theorem stepStatic_listLookup_addNode_miss
    {pc : Nat} {kVal listVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32}
    {xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)}
    (hk : decodeNodeKey kVal = some k)
    (hlist : decodeNodeBucketList jh (jh.objects.size + 2) listVal = some xs)
    (hmiss : xs.lookup k = none) :
    stepInvokeStatic ⟨pc, listVal :: kVal :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_List_lookup___at___00Algorithm_MacrocellWriterState_addNode_spec__0___redArg"
      "(Lkotlin/Pair;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩) := by
  have h := stepStatic_listLookup_addNode (pc := pc) (rest := rest) (locs := locs) (hp := hp) hk hlist
  simp only [hmiss] at h
  exact h

private abbrev progALAt : List JvmInstr := f_Algorithm_DagWriter_addLeafAt_prog

theorem dagWriter_addLeafAt_hit_equiv
    (w : Algorithm.DagWriter) (wAddr : Nat) (leaf : UInt64) (s id : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hs0 : s.toBitVec.slt 0#32 = false) (hs : s.toNat < w.leafT.size)
    (hhit : w.leafT[s.toNat].lookup leaf = some id) :
    ∃ f st',
      runJvmRes f f_Algorithm_DagWriter_addLeafAt_prog
          ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr))
            1 (.i64 leaf)) 3 (.i32 s), jh, hp⟩ =
        some (.pair (.boxedUInt id) (.heapRef wAddr), st') ∧
      w.addLeafAt leaf s = (id, w) ∧
      st'.jvmHeap = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2 ∧
      st'.heap = hp := by
  obtain ⟨wCls, wElems, lAddr, lCls, lBuckets, nAddr, nCls, nBuckets,
    hgw, he1, he2, he3, hgl, hgn, hlSz, _, hlGet, _⟩ := decodeDagWriter_unpack hdec
  have hadd : w.addLeafAt leaf s = (id, w) := by
    simp [Algorithm.DagWriter.addLeafAt, Algorithm.ChainTable.get, hs, hhit]
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef wAddr)) 1 (.i64 leaf)) 3 (.i32 s)
  let resObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id]
  let jh1 := (jh.alloc resObj).2
  have hgetRes : jh1.get? jh.objects.size = some resObj := jvmHeap_get?_alloc_self jh resObj
  have hlBucket : decodeLeafBucketList jh (jh.objects.size + 2) lBuckets[s.toNat] =
      some w.leafT[s.toNat] := (hlGet s.toNat (by omega)).2
  suffices hsuf : ∃ locs',
      runJvmResFast 69 progALAt 0 (progALAt.drop 0) ⟨0, [], locs0, jh, hp⟩ =
        some (.pair (.boxedUInt id) (.heapRef wAddr),
          ⟨158, [.pair (.boxedUInt id) (.heapRef wAddr)], locs', jh1, hp⟩) by
    obtain ⟨locs', hrun⟩ := hsuf
    exact ⟨69, _, runJvmRes_of_runJvmResFast0 69 progALAt _ _ rfl hrun, hadd, rfl, rfl⟩
  apply Exists.intro
  · conv => lhs; arg 4; rw [show progALAt = progALAt.drop 0 from rfl]
    rw [show (69 : Nat) = 36 + 33 from rfl]
    step_drop_at 33
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he1)]
    step1
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he2)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_objArray_any hgl]
    step1
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he3)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_objArray_any hgn]
    step1
    step1_load 5 (.heapRef lAddr), (by simp [setLocal])
    step1_load 3 (.i32 s), (by simp [locs0, setLocal])
    rw [runJvmResFast_aaload hgl hs0 (by omega)]
    step1
    step1_load 1 (.i64 leaf), (by simp [locs0, setLocal])
    step1_load 7 lBuckets[s.toNat], (by simp [setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_listLookup_addLeaf_hit hlBucket hhit)]
    rw [show (36 : Nat) = 22 + 14 from rfl]
    step_drop_at 14
    step1
    step1_load 8 (.heapRef jh.objects.size), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 8 (.heapRef jh.objects.size), (by simp [setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgetRes]
    step1
    rw [runJvmResFast_aaload_elem hgetRes (by decide)
      (show #[JvmVal.boxedInt 1, JvmVal.boxedUInt id][(0 : UInt32).toNat]? = some (.boxedInt 1) from rfl)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
    rw [runJvmResFast_tableswitch]
    rw [show Jvm.tableswitchTarget 1 0 [47, 132] 159 = 132 from by decide]
    dsimp only
    rw [show (22 : Nat) = 10 + 12 from rfl]
    step_drop_at 12
    rw [runJvmResFast_newClass_pair]
    step1
    step1_load 8 (.heapRef jh.objects.size), (by simp [setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgetRes]
    step1
    rw [runJvmResFast_aaload_elem hgetRes (by decide)
      (show #[JvmVal.boxedInt 1, JvmVal.boxedUInt id][(1 : UInt32).toNat]? = some (.boxedUInt id) from rfl)]
    step1; step1; step1
    step1_load 9 (.boxedUInt id), (by simp [setLocal])
    rw [runJvmResFast_instanceof_boxedUInt_int]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [show (10 : Nat) = 1 + 9 from rfl]
    step_drop_at 10
    step1_load 9 (.boxedUInt id), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 9 (.boxedUInt id), (by simp [setLocal])
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
    rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_invokespecial_pair_init]
    exact runJvmResFast_areturn

private def AllFuelNoneAt (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) : Prop :=
  st.pc = pc → prog.drop pc = instrs → ∀ f, runJvmRes f prog st = none

private theorem allFuelNoneAt_start {prog : List JvmInstr} {st : JvmState}
    (hpc0 : st.pc = 0) (h : AllFuelNoneAt prog 0 prog st) : ∀ f, runJvmRes f prog st = none :=
  h hpc0 List.drop_zero

private theorem allFuelNoneAt_step {prog rest : List JvmInstr} {pc : Nat} {instr : JvmInstr}
    {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hnbr : isBranchInstr instr = false)
    (hstep : stepInstr instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩))
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩) :
    AllFuelNoneAt prog pc (instr :: rest) ⟨pc, stk, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some instr := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    have hdrop1 : prog.drop (pc + 1) = rest := by
      have h1 : (prog.drop pc).drop 1 = prog.drop (pc + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      rw [← h1, hdrop]; rfl
    rw [runJvmRes_nonbranch f prog ⟨pc, stk, locs, jh, hp⟩ instr hg hnbr, hstep]
    exact hnext rfl hdrop1 f

private theorem allFuelNoneAt_checkcast_ext_objArr {prog rest : List JvmInstr} {pc : Nat}
    {e : AlgExt} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    AllFuelNoneAt prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
      ⟨pc, .ext e :: stkRest, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some (.checkcast "[Ljava/lang/Object;") := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    rw [runJvmRes_nonbranch f prog _ (.checkcast "[Ljava/lang/Object;") hg rfl]
    cases e <;> rfl

private theorem allFuelNoneAt_dup {prog rest : List JvmInstr} {pc : Nat}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, v :: v :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.dup :: rest) ⟨pc, v :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; rfl) hnext

private theorem allFuelNoneAt_ldcStr {prog rest : List JvmInstr} {pc : Nat}
    {s : String} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, .str s :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.ldcStr s :: rest) ⟨pc, stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; rfl) hnext

private theorem allFuelNoneAt_iconst {prog rest : List JvmInstr} {pc : Nat}
    {n : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, .i32 n :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.iconst n :: rest) ⟨pc, stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; rfl) hnext

private theorem allFuelNoneAt_astore {prog rest : List JvmInstr} {pc idx : Nat}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stkRest, setLocal locs idx v, jh, hp⟩) :
    AllFuelNoneAt prog pc (.astore idx :: rest) ⟨pc, v :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; rfl) hnext

private theorem allFuelNoneAt_aload {prog rest : List JvmInstr} {pc idx : Nat}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hloc : locs idx = v)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, v :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.aload idx :: rest) ⟨pc, stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; dsimp only; rw [hloc]) hnext

private theorem allFuelNoneAt_iload {prog rest : List JvmInstr} {pc idx : Nat}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hloc : locs idx = v)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, v :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.iload idx :: rest) ⟨pc, stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; dsimp only; rw [hloc]) hnext

private theorem allFuelNoneAt_lload {prog rest : List JvmInstr} {pc idx : Nat}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hloc : locs idx = v)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, v :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.lload idx :: rest) ⟨pc, stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr; dsimp only; rw [hloc]) hnext

private theorem allFuelNoneAt_checkcast_boxedInt {prog rest : List JvmInstr} {pc : Nat}
    {v : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.checkcast "java/lang/Integer" :: rest)
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr Jvm.evalCheckCast; rfl) hnext

private theorem allFuelNoneAt_checkcast_pair {prog rest : List JvmInstr} {pc : Nat}
    {a b : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.checkcast "kotlin/Pair" :: rest)
      ⟨pc, .pair a b :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by unfold stepInstr Jvm.stepInstr Jvm.evalCheckCast; rfl) hnext

private theorem allFuelNoneAt_tableswitch_next {prog rest : List JvmInstr} {pc : Nat}
    {low : Int32} {targets : List Nat} {defT : Nat} {key : UInt32}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (htgt : Jvm.tableswitchTarget key low targets defT = pc + 1)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.tableswitch low targets defT :: rest)
      ⟨pc, .i32 key :: stkRest, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some (.tableswitch low targets defT) := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    have hdrop1 : prog.drop (pc + 1) = rest := by
      have h1 : (prog.drop pc).drop 1 = prog.drop (pc + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      rw [← h1, hdrop]; rfl
    change runJvmRes (f + 1) prog ⟨pc, .i32 key :: stkRest, locs, jh, hp⟩ = none
    dsimp only [runJvmRes]
    rw [Jvm.runJvmRes.eq_def]
    simp only [hg, Jvm.JvmVal.asI32?, htgt]
    exact hnext rfl hdrop1 f

private theorem allFuelNoneAt_invokestatic_step {prog rest : List JvmInstr} {pc : Nat}
    {cls m desc : String} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ cls m desc =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩))
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩) :
    AllFuelNoneAt prog pc (.invokestatic cls m desc :: rest) ⟨pc, stk, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl hs hnext

private theorem allFuelNoneAt_invokevirtual_step {prog rest : List JvmInstr} {pc : Nat}
    {cls m desc : String} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeVirtual ⟨pc, stk, locs, jh, hp⟩ cls m desc =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩))
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩) :
    AllFuelNoneAt prog pc (.invokevirtual cls m desc :: rest) ⟨pc, stk, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl hs hnext

private theorem allFuelNoneAt_checkNotNullParameter {prog rest : List JvmInstr} {pc : Nat}
    {v : JvmVal} {param : String} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnn : v ≠ .null)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
      ⟨pc, .str param :: v :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by
    unfold stepInstr Jvm.stepInstr
    dsimp only
    have his : Jvm.JvmVal.isNull v = false := by cases v <;> simp_all [Jvm.JvmVal.isNull]
    exact Jvm.stepInvokeStatic_intrinsics_checkNotNullParam algHooks his) hnext

private theorem allFuelNoneAt_checkNotNull {prog rest : List JvmInstr} {pc : Nat}
    {v : JvmVal} {msg : String} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnn : v ≠ .null)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
      ⟨pc, .str msg :: v :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by
    unfold stepInstr Jvm.stepInstr
    dsimp only
    have his : Jvm.JvmVal.isNull v = false := by cases v <;> simp_all [Jvm.JvmVal.isNull]
    exact Jvm.stepInvokeStatic_intrinsics_checkNotNull algHooks his) hnext

private theorem allFuelNoneAt_checkcast_objArray {prog rest : List JvmInstr} {pc addr : Nat}
    {cls : String} {elems : Array JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
      ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by
    unfold stepInstr Jvm.stepInstr Jvm.evalCheckCast Jvm.JvmHeap.checkCast Jvm.JvmHeap.checkInstanceOf
    dsimp only
    rw [hget]
    simp [Jvm.HeapObj.matchesType]) hnext

private theorem allFuelNoneAt_aaload {prog rest : List JvmInstr} {pc addr : Nat}
    {cls : String} {elems : Array JvmVal} {idx : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size)
    (hnext : AllFuelNoneAt prog (pc + 1) rest
      ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.aaload :: rest) ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ :=
  allFuelNoneAt_step rfl (by
    simpa using Jvm.stepInstr_aaload algHooks (pc := pc) (stkRest := stkRest)
      (locs := locs) (hp := hp) hget hslt hlt) hnext

/-- Miss-branch conflict under frozen `JvmSemantics`: `decodeDagWriter` stores
`.ext (.strGrowBuf w.lines)` at `wVal[1]`, whereas Kotlin's bytecode at PC 50..53
expects an erased tuple `[0, linesGrowBuf, nextLeafId]` of type `[Ljava/lang/Object;`
before calling `GrowBuf_push` on `wVal[1]` at PC 77. -/
private theorem dagWriter_addLeafAt_miss_blocked
    (w : Algorithm.DagWriter) (wAddr : Nat) (leaf : UInt64) (s : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hs0 : s.toBitVec.slt 0#32 = false) (hs : s.toNat < w.leafT.size)
    (hmiss : w.leafT[s.toNat].lookup leaf = none) (f : Nat) :
    runJvmRes f progALAt
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr))
          1 (.i64 leaf)) 3 (.i32 s), jh, hp⟩ = none := by
  revert f
  obtain ⟨wCls, wElems, lAddr, lCls, lBuckets, nAddr, nCls, nBuckets,
    hgw, he1, he2, he3, hgl, hgn, hlSz, _, hlGet, _⟩ := decodeDagWriter_unpack hdec
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef wAddr)) 1 (.i64 leaf)) 3 (.i32 s)
  let resObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[.boxedInt 0]
  let jh1 := (jh.alloc resObj).2
  have hgetRes : jh1.get? jh.objects.size = some resObj := jvmHeap_get?_alloc_self jh resObj
  have hlBucket : decodeLeafBucketList jh (jh.objects.size + 2) lBuckets[s.toNat] =
      some w.leafT[s.toNat] := (hlGet s.toNat (by omega)).2
  have h1 : 1 < wElems.size := (Array.getElem?_eq_some_iff.mp he1).1
  have h2 : 2 < wElems.size := (Array.getElem?_eq_some_iff.mp he2).1
  have h3 : 3 < wElems.size := (Array.getElem?_eq_some_iff.mp he3).1
  have hw1 : wElems[(1 : UInt32).toNat] = .ext (.strGrowBuf w.lines) := by
    rw [getElem?_pos wElems 1 h1, Option.some.injEq] at he1; exact he1
  have hw2 : wElems[(2 : UInt32).toNat] = .heapRef lAddr := by
    rw [getElem?_pos wElems 2 h2, Option.some.injEq] at he2; exact he2
  have hw3 : wElems[(3 : UInt32).toNat] = .heapRef nAddr := by
    rw [getElem?_pos wElems 3 h3, Option.some.injEq] at he3; exact he3
  apply allFuelNoneAt_start rfl
  dsimp only [progALAt, f_Algorithm_DagWriter_addLeafAt_prog]
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h1 ?_
  rw [hw1]
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h2 ?_
  rw [hw2]
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_objArray hgl ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h3 ?_
  rw [hw3]
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_objArray hgn ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_iload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_aaload hgl hs0 (by omega) ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_lload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_invokestatic_step (stepStatic_listLookup_addLeaf_miss hlBucket hmiss) ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgetRes ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgetRes (by decide) (by decide) ?_
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_boxedInt ?_
  refine allFuelNoneAt_invokevirtual_step stepVirtual_integer_intValue ?_
  refine allFuelNoneAt_tableswitch_next (by decide) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  exact allFuelNoneAt_checkcast_ext_objArr

private abbrev progANAt : List JvmInstr := f_Algorithm_DagWriter_addNodeAt_prog

theorem dagWriter_addNodeAt_hit_equiv
    (w : Algorithm.DagWriter) (wAddr : Nat)
    (k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (s id : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hs0 : s.toBitVec.slt 0#32 = false) (hs : s.toNat < w.nodeT.size)
    (hhit : w.nodeT[s.toNat].lookup k = some id) :
    ∃ f st',
      runJvmRes f f_Algorithm_DagWriter_addNodeAt_prog
          ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr))
            1 (encodeNodeKey k)) 2 (.i32 s), jh, hp⟩ =
        some (.pair (.boxedUInt id) (.heapRef wAddr), st') ∧
      w.addNodeAt k s = (id, w) ∧
      st'.jvmHeap = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id])).2 ∧
      st'.heap = hp := by
  obtain ⟨wCls, wElems, lAddr, lCls, lBuckets, nAddr, nCls, nBuckets,
    hgw, he1, he2, he3, hgl, hgn, _, hnSz, _, hnGet⟩ := decodeDagWriter_unpack hdec
  have hadd : w.addNodeAt k s = (id, w) := by
    simp [Algorithm.DagWriter.addNodeAt, Algorithm.ChainTable.get, hs, hhit]
  let kVal := encodeNodeKey k
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef wAddr)) 1 kVal) 2 (.i32 s)
  let resObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[.boxedInt 1, .boxedUInt id]
  let jh1 := (jh.alloc resObj).2
  have hgetRes : jh1.get? jh.objects.size = some resObj := jvmHeap_get?_alloc_self jh resObj
  have hnBucket : decodeNodeBucketList jh (jh.objects.size + 2) nBuckets[s.toNat] =
      some w.nodeT[s.toNat] := (hnGet s.toNat (by omega)).2
  have hkDec : decodeNodeKey kVal = some k := by
    rcases k with ⟨l, nw, ne, sw, se⟩
    rfl
  suffices hsuf : ∃ locs',
      runJvmResFast 72 progANAt 0 (progANAt.drop 0) ⟨0, [], locs0, jh, hp⟩ =
        some (.pair (.boxedUInt id) (.heapRef wAddr),
          ⟨191, [.pair (.boxedUInt id) (.heapRef wAddr)], locs', jh1, hp⟩) by
    obtain ⟨locs', hrun⟩ := hsuf
    exact ⟨72, _, runJvmRes_of_runJvmResFast0 72 progANAt _ _ rfl hrun, hadd, rfl, rfl⟩
  apply Exists.intro
  · conv => lhs; arg 4; rw [show progANAt = progANAt.drop 0 from rfl]
    rw [show (72 : Nat) = 36 + 36 from rfl]
    step_drop_at 36
    step1_load 1 kVal, (by simp [locs0, setLocal])
    step1
    rw [runJvmResFast_checkNotNullParameter (by dsimp [kVal, encodeNodeKey]; rfl)]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he1)]
    step1
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he2)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_objArray_any hgl]
    step1
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he3)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_objArray_any hgn]
    step1
    step1_load 5 (.heapRef nAddr), (by simp [setLocal])
    step1_load 2 (.i32 s), (by simp [locs0, setLocal])
    rw [runJvmResFast_aaload hgn hs0 (by omega)]
    step1
    step1_load 1 kVal, (by simp [locs0, setLocal])
    step1_load 6 nBuckets[s.toNat], (by simp [setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_listLookup_addNode_hit hkDec hnBucket hhit)]
    rw [show (36 : Nat) = 22 + 14 from rfl]
    step_drop_at 14
    step1
    step1_load 7 (.heapRef jh.objects.size), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 7 (.heapRef jh.objects.size), (by simp [setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgetRes]
    step1
    rw [runJvmResFast_aaload_elem hgetRes (by decide)
      (show #[JvmVal.boxedInt 1, JvmVal.boxedUInt id][(0 : UInt32).toNat]? = some (.boxedInt 1) from rfl)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
    rw [runJvmResFast_tableswitch]
    rw [show Jvm.tableswitchTarget 1 0 [50, 165] 192 = 165 from by decide]
    dsimp only
    rw [show (22 : Nat) = 10 + 12 from rfl]
    step_drop_at 12
    rw [runJvmResFast_newClass_pair]
    step1
    step1_load 7 (.heapRef jh.objects.size), (by simp [setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgetRes]
    step1
    rw [runJvmResFast_aaload_elem hgetRes (by decide)
      (show #[JvmVal.boxedInt 1, JvmVal.boxedUInt id][(1 : UInt32).toNat]? = some (.boxedUInt id) from rfl)]
    step1; step1; step1
    step1_load 8 (.boxedUInt id), (by simp [setLocal])
    rw [runJvmResFast_instanceof_boxedUInt_int]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [show (10 : Nat) = 1 + 9 from rfl]
    step_drop_at 10
    step1_load 8 (.boxedUInt id), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 8 (.boxedUInt id), (by simp [setLocal])
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
    rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_invokespecial_pair_init]
    exact runJvmResFast_areturn

/-- Miss-branch conflict under frozen `JvmSemantics`: `decodeDagWriter` stores
`.ext (.strGrowBuf w.lines)` at `wVal[1]`, whereas Kotlin's bytecode at PC 65..68
expects an erased tuple `[0, linesGrowBuf, nextNodeId]` of type `[Ljava/lang/Object;`
before calling `GrowBuf_push` on `wVal[1]` at PC 111. -/
private theorem dagWriter_addNodeAt_miss_blocked
    (w : Algorithm.DagWriter) (wAddr : Nat)
    (k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (s : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hs0 : s.toBitVec.slt 0#32 = false) (hs : s.toNat < w.nodeT.size)
    (hmiss : w.nodeT[s.toNat].lookup k = none) (f : Nat) :
    runJvmRes f progANAt
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr))
          1 (encodeNodeKey k)) 2 (.i32 s), jh, hp⟩ = none := by
  revert f
  obtain ⟨wCls, wElems, lAddr, lCls, lBuckets, nAddr, nCls, nBuckets,
    hgw, he1, he2, he3, hgl, hgn, _, hnSz, _, hnGet⟩ := decodeDagWriter_unpack hdec
  let kVal := encodeNodeKey k
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef wAddr)) 1 kVal) 2 (.i32 s)
  let resObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[.boxedInt 0]
  let jh1 := (jh.alloc resObj).2
  have hgetRes : jh1.get? jh.objects.size = some resObj := jvmHeap_get?_alloc_self jh resObj
  have hnBucket : decodeNodeBucketList jh (jh.objects.size + 2) nBuckets[s.toNat] =
      some w.nodeT[s.toNat] := (hnGet s.toNat (by omega)).2
  have hkDec : decodeNodeKey kVal = some k := by
    rcases k with ⟨l, nw, ne, sw, se⟩; rfl
  have h1 : 1 < wElems.size := (Array.getElem?_eq_some_iff.mp he1).1
  have h2 : 2 < wElems.size := (Array.getElem?_eq_some_iff.mp he2).1
  have h3 : 3 < wElems.size := (Array.getElem?_eq_some_iff.mp he3).1
  have hw1 : wElems[(1 : UInt32).toNat] = .ext (.strGrowBuf w.lines) := by
    rw [getElem?_pos wElems 1 h1, Option.some.injEq] at he1; exact he1
  have hw2 : wElems[(2 : UInt32).toNat] = .heapRef lAddr := by
    rw [getElem?_pos wElems 2 h2, Option.some.injEq] at he2; exact he2
  have hw3 : wElems[(3 : UInt32).toNat] = .heapRef nAddr := by
    rw [getElem?_pos wElems 3 h3, Option.some.injEq] at he3; exact he3
  apply allFuelNoneAt_start rfl
  dsimp only [progANAt, f_Algorithm_DagWriter_addNodeAt_prog]
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNullParameter (by dsimp [kVal, encodeNodeKey]; intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h1 ?_
  rw [hw1]
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h2 ?_
  rw [hw2]
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_objArray hgl ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgw ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgw (by decide) h3 ?_
  rw [hw3]
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_objArray hgn ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_iload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_aaload hgn hs0 (by omega) ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_invokestatic_step (stepStatic_listLookup_addNode_miss hkDec hnBucket hmiss) ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_checkcast_objArray hgetRes ?_
  refine allFuelNoneAt_iconst ?_
  refine allFuelNoneAt_aaload hgetRes (by decide) (by decide) ?_
  refine allFuelNoneAt_dup ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_checkcast_boxedInt ?_
  refine allFuelNoneAt_invokevirtual_step stepVirtual_integer_intValue ?_
  refine allFuelNoneAt_tableswitch_next (by decide) ?_
  dsimp only [kVal, encodeNodeKey]
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_invokevirtual_step stepVirtual_pairGetSecond ?_
  refine allFuelNoneAt_checkcast_pair ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_invokevirtual_step stepVirtual_pairGetSecond ?_
  refine allFuelNoneAt_checkcast_pair ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_invokevirtual_step stepVirtual_pairGetSecond ?_
  refine allFuelNoneAt_checkcast_pair ?_
  refine allFuelNoneAt_astore ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  refine allFuelNoneAt_ldcStr ?_
  refine allFuelNoneAt_checkNotNull (by intro h; cases h) ?_
  refine allFuelNoneAt_aload (by simp [setLocal]; rfl) ?_
  exact allFuelNoneAt_checkcast_ext_objArr

/-! ### Part 5: `DagWriter.addLeaf` and `DagWriter.addNode` -/

private def HeapExtends (h1 h2 : Jvm.JvmHeap AlgExt) : Prop :=
  h1.objects.size ≤ h2.objects.size ∧ ∀ a, a < h1.objects.size → h2.get? a = h1.get? a

private theorem HeapExtends_refl (h : Jvm.JvmHeap AlgExt) : HeapExtends h h :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem HeapExtends_trans {h1 h2 h3 : Jvm.JvmHeap AlgExt}
    (h12 : HeapExtends h1 h2) (h23 : HeapExtends h2 h3) : HeapExtends h1 h3 :=
  ⟨Nat.le_trans h12.1 h23.1, fun a ha => by
    rw [h23.2 a (Nat.lt_of_lt_of_le ha h12.1), h12.2 a ha]⟩

private theorem HeapExtends_alloc (h : Jvm.JvmHeap AlgExt) (obj : Jvm.HeapObj AlgExt) :
    HeapExtends h (h.alloc obj).2 :=
  ⟨by simp [Jvm.JvmHeap.alloc], fun a ha => jvmHeap_get?_alloc_lt h obj ha⟩

private theorem decodeLeafBucketList_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {bound : Nat} {v : JvmVal} {xs : List (UInt64 × UInt32)}
    (hdec : decodeLeafBucketList h1 bound v = some xs) :
    decodeLeafBucketList h2 bound v = some xs := by
  induction bound generalizing v xs with
  | zero => simp [decodeLeafBucketList] at hdec
  | succ b ih =>
    cases v with
    | heapRef addr =>
      dsimp [decodeLeafBucketList] at hdec ⊢
      cases hget : h1.get? addr with
      | none => simp [hget] at hdec
      | some obj =>
        have hlt := jvmHeap_addr_lt_of_get? hget
        rw [hext.2 addr hlt, hget]
        rw [hget] at hdec
        cases obj with
        | objArray cls elems =>
          dsimp at hdec ⊢
          cases h0 : (elems[0]? : Option JvmVal) with
          | none => simp [h0] at hdec
          | some v0 =>
            simp only [h0] at hdec ⊢
            cases v0 with
            | boxedInt tag =>
              by_cases hzero : tag = 0
              · subst hzero; simpa using hdec
              · by_cases hone : tag = 1
                · subst hone
                  cases h1e : (elems[1]? : Option JvmVal) <;> cases h2e : (elems[2]? : Option JvmVal)
                  all_goals simp [h1e, h2e] at hdec ⊢
                  case some.some v1 tl =>
                  cases v1 with
                  | pair k v =>
                    dsimp at hdec ⊢
                    cases htl : decodeLeafBucketList h1 b tl with
                    | none => simp [htl] at hdec
                    | some tlXs =>
                      rw [ih htl]
                      simpa [htl] using hdec
                  | _ => simp at hdec
                · simp [hzero, hone] at hdec
            | _ => simp at hdec
        | _ => simp at hdec
    | _ => simp [decodeLeafBucketList] at hdec

private theorem decodeNodeBucketList_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {bound : Nat} {v : JvmVal}
    {xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)}
    (hdec : decodeNodeBucketList h1 bound v = some xs) :
    decodeNodeBucketList h2 bound v = some xs := by
  induction bound generalizing v xs with
  | zero => simp [decodeNodeBucketList] at hdec
  | succ b ih =>
    cases v with
    | heapRef addr =>
      dsimp [decodeNodeBucketList] at hdec ⊢
      cases hget : h1.get? addr with
      | none => simp [hget] at hdec
      | some obj =>
        have hlt := jvmHeap_addr_lt_of_get? hget
        rw [hext.2 addr hlt, hget]
        rw [hget] at hdec
        cases obj with
        | objArray cls elems =>
          dsimp at hdec ⊢
          cases h0 : (elems[0]? : Option JvmVal) with
          | none => simp [h0] at hdec
          | some v0 =>
            simp only [h0] at hdec ⊢
            cases v0 with
            | boxedInt tag =>
              by_cases hzero : tag = 0
              · subst hzero; simpa using hdec
              · by_cases hone : tag = 1
                · subst hone
                  cases h1e : (elems[1]? : Option JvmVal) <;> cases h2e : (elems[2]? : Option JvmVal)
                  all_goals simp [h1e, h2e] at hdec ⊢
                  case some.some v1 tl =>
                  cases v1 with
                  | pair kVal v =>
                    dsimp at hdec ⊢
                    cases hk : decodeNodeKey kVal with
                    | none => simp [hk] at hdec
                    | some k =>
                      simp only [hk] at hdec ⊢
                      cases htl : decodeNodeBucketList h1 b tl with
                      | none => simp [htl] at hdec
                      | some tlXs =>
                        rw [ih htl]
                        simpa [htl] using hdec
                  | _ => simp at hdec
                · simp [hzero, hone] at hdec
            | _ => simp at hdec
        | _ => simp at hdec
    | _ => simp [decodeNodeBucketList] at hdec

private theorem jvmHeap_get?_alloc_fst (jh : Jvm.JvmHeap AlgExt) (obj : Jvm.HeapObj AlgExt) :
    (jh.alloc obj).2.get? (jh.alloc obj).1 = some obj :=
  jvmHeap_get?_alloc_self jh obj

private theorem encodeLeafBucketList_spec (jh : Jvm.JvmHeap AlgExt)
    (xs : List (UInt64 × UInt32)) :
    (encodeLeafBucketList jh xs).2.objects.size = jh.objects.size + xs.length + 1 ∧
      HeapExtends jh (encodeLeafBucketList jh xs).2 ∧
      ∀ bound, xs.length < bound →
        decodeLeafBucketList (encodeLeafBucketList jh xs).2 bound
          (encodeLeafBucketList jh xs).1 = some xs := by
  induction xs with
  | nil =>
    dsimp [encodeLeafBucketList]
    refine ⟨by simp [Jvm.JvmHeap.alloc], HeapExtends_alloc _ _, fun bound hb => ?_⟩
    cases bound with
    | zero => omega
    | succ b =>
      dsimp only [decodeLeafBucketList]
      rw [jvmHeap_get?_alloc_fst]
      rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    obtain ⟨hsz, hext, hdec⟩ := ih
    dsimp only [encodeLeafBucketList]
    let obj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
      #[.boxedInt 1, .pair (.boxedULong k) (.boxedUInt v), (encodeLeafBucketList jh tl).1]
    have hsz1 : ((encodeLeafBucketList jh tl).2.alloc obj).2.objects.size =
        jh.objects.size + (tl.length + 1) + 1 := by
      simp [Jvm.JvmHeap.alloc, hsz]; omega
    have hext1 : HeapExtends jh ((encodeLeafBucketList jh tl).2.alloc obj).2 :=
      HeapExtends_trans hext (HeapExtends_alloc _ _)
    refine ⟨hsz1, hext1, fun bound hb => ?_⟩
    cases bound with
    | zero => omega
    | succ b =>
      dsimp only [decodeLeafBucketList]
      rw [jvmHeap_get?_alloc_fst]
      have htl := decodeLeafBucketList_mono (HeapExtends_alloc (encodeLeafBucketList jh tl).2 obj)
        (hdec b (by simp at hb; omega))
      dsimp only [obj] at htl
      simp [htl, unboxI64?, unboxI32?]

private theorem encodeNodeBucketList_spec (jh : Jvm.JvmHeap AlgExt)
    (xs : List ((UInt32 × UInt32 × UInt32 × UInt32 × UInt32) × UInt32)) :
    (encodeNodeBucketList jh xs).2.objects.size = jh.objects.size + xs.length + 1 ∧
      HeapExtends jh (encodeNodeBucketList jh xs).2 ∧
      ∀ bound, xs.length < bound →
        decodeNodeBucketList (encodeNodeBucketList jh xs).2 bound
          (encodeNodeBucketList jh xs).1 = some xs := by
  induction xs with
  | nil =>
    dsimp [encodeNodeBucketList]
    refine ⟨by simp [Jvm.JvmHeap.alloc], HeapExtends_alloc _ _, fun bound hb => ?_⟩
    cases bound with
    | zero => omega
    | succ b =>
      dsimp only [decodeNodeBucketList]
      rw [jvmHeap_get?_alloc_fst]
      rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    obtain ⟨hsz, hext, hdec⟩ := ih
    dsimp only [encodeNodeBucketList]
    let obj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
      #[.boxedInt 1, .pair (encodeNodeKey k) (.boxedUInt v), (encodeNodeBucketList jh tl).1]
    have hsz1 : ((encodeNodeBucketList jh tl).2.alloc obj).2.objects.size =
        jh.objects.size + (tl.length + 1) + 1 := by
      simp [Jvm.JvmHeap.alloc, hsz]; omega
    have hext1 : HeapExtends jh ((encodeNodeBucketList jh tl).2.alloc obj).2 :=
      HeapExtends_trans hext (HeapExtends_alloc _ _)
    refine ⟨hsz1, hext1, fun bound hb => ?_⟩
    cases bound with
    | zero => omega
    | succ b =>
      dsimp only [decodeNodeBucketList]
      rw [jvmHeap_get?_alloc_fst]
      have htl := decodeNodeBucketList_mono (HeapExtends_alloc (encodeNodeBucketList jh tl).2 obj)
        (hdec b (by simp at hb; omega))
      have hk : decodeNodeKey (encodeNodeKey k) = some k := by
        rcases k with ⟨l, nw, ne, sw, se⟩; rfl
      dsimp only [obj] at htl
      simp [hk, htl, unboxI32?]

private theorem foldl_encodeBuckets_list {α : Type}
    (enc : Jvm.JvmHeap AlgExt → α → JvmVal × Jvm.JvmHeap AlgExt)
    (dec : Jvm.JvmHeap AlgExt → Nat → JvmVal → Option α)
    (lenFn : α → Nat)
    (hspec : ∀ h x, (enc h x).2.objects.size = h.objects.size + lenFn x + 1 ∧
      HeapExtends h (enc h x).2 ∧
      ∀ bound, lenFn x < bound → dec (enc h x).2 bound (enc h x).1 = some x)
    (hmono : ∀ h1 h2, HeapExtends h1 h2 → ∀ bound v x,
      dec h1 bound v = some x → dec h2 bound v = some x)
    (bs : List α) (initAcc : Array JvmVal) (initVals : List α)
    (curH : Jvm.JvmHeap AlgExt)
    (hInitSz : initAcc.size = initVals.length)
    (hInitOk : ∀ (i : Nat) (hi : i < initAcc.size),
      ∀ bound, lenFn (initVals[i]'(hInitSz ▸ hi)) < bound →
        dec curH bound initAcc[i] = some (initVals[i]'(hInitSz ▸ hi)))
    (hInitBound : ∀ (i : Nat) (hi : i < initVals.length),
      lenFn initVals[i] < curH.objects.size) :
    let res := bs.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
      let r := enc p.2 b; (p.1.push r.1, r.2)) (initAcc, curH)
    HeapExtends curH res.2 ∧
      res.1.size = (initVals ++ bs).length ∧
      (∀ (i : Nat) (hi : i < (initVals ++ bs).length),
        lenFn (initVals ++ bs)[i] < res.2.objects.size) ∧
      (∀ (i : Nat) (hi1 : i < res.1.size) (hi2 : i < (initVals ++ bs).length),
        ∀ bound, lenFn (initVals ++ bs)[i] < bound →
          dec res.2 bound res.1[i] = some (initVals ++ bs)[i]) := by
  induction bs generalizing initAcc initVals curH with
  | nil =>
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨HeapExtends_refl _, hInitSz, hInitBound, fun i hi1 _ => hInitOk i hi1⟩
  | cons b bs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hsz, hext, hdec⟩ := hspec curH b
    have hBoundNew : ∀ (i : Nat) (hi : i < (initVals ++ [b]).length),
        lenFn (initVals ++ [b])[i] < (enc curH b).2.objects.size := by
      intro i hi
      by_cases hil : i < initVals.length
      · rw [List.getElem_append_left hil]
        exact Nat.lt_of_lt_of_le (hInitBound i hil) hext.1
      · have hiEq : i = initVals.length := by simp at hi; omega
        subst hiEq
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
        omega
    have hOkNew : ∀ (i : Nat) (hi : i < (initAcc.push (enc curH b).1).size),
        ∀ bound, lenFn ((initVals ++ [b])[i]'(by simp at hi ⊢; omega)) < bound →
          dec (enc curH b).2 bound (initAcc.push (enc curH b).1)[i] =
            some ((initVals ++ [b])[i]'(by simp at hi ⊢; omega)) := by
      intro i hi bound hbnd
      by_cases hil : i < initAcc.size
      · rw [Array.getElem_push_lt hil]
        have heq : (initVals ++ [b])[i]'(by simp at hi ⊢; omega) = initVals[i]'(hInitSz ▸ hil) := by
          rw [List.getElem_append_left (hInitSz ▸ hil)]
        rw [heq] at hbnd ⊢
        exact hmono curH (enc curH b).2 hext bound initAcc[i] _ (hInitOk i hil bound hbnd)
      · have hiEq : i = initAcc.size := by simp at hi; omega
        subst hiEq
        rw [Array.getElem_push_eq]
        have heq : (initVals ++ [b])[initAcc.size]'(by simp; omega) = b := by
          simp [hInitSz]
        rw [heq] at hbnd ⊢
        exact hdec bound hbnd
    obtain ⟨hextRec, hszRec, hboundRec, hokRec⟩ := ih (initAcc.push (enc curH b).1)
      (initVals ++ [b]) (enc curH b).2 (by simp [hInitSz]) hOkNew hBoundNew
    refine ⟨HeapExtends_trans hext hextRec, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hszRec
    · simpa [List.append_assoc] using hboundRec
    · intro i hi1 hi2 bound hbnd
      simpa [List.append_assoc] using hokRec i (by simpa [List.append_assoc] using hi1)
        (by simpa [List.append_assoc] using hi2) bound (by simpa [List.append_assoc] using hbnd)

private theorem foldlM_array_eq_some_of_forall {α β : Type} (f : α → Option β)
    (xs : Array α) (ys : Array β) (hsz : xs.size = ys.size)
    (hok : ∀ (i : Nat) (hi : i < xs.size), f xs[i] = some (ys[i]'(hsz ▸ hi))) :
    xs.foldlM (fun acc x => (f x).map acc.push) #[] = some ys := by
  rw [← Array.foldlM_toList]
  have aux : ∀ (k : Nat) (hk : k ≤ xs.size) (init : Array β),
      init.size = k → (∀ (i : Nat) (hi : i < k), init[i]? = ys[i]?) →
      (xs.toList.drop k).foldlM (fun acc x => (f x).map acc.push) init = some ys := by
    intro k hk init hiSz hiPref
    induction n : xs.size - k generalizing k init with
    | zero =>
      have hkeq : k = xs.size := by omega
      subst hkeq
      rw [List.drop_of_length_le (by simp), List.foldlM_nil]
      congr 1
      apply Array.ext (by omega)
      intro i hi1 hi2
      have hpr := hiPref i (by omega)
      simpa [getElem?_pos init i hi1, getElem?_pos ys i hi2] using hpr
    | succ m ih =>
      have hkl : k < xs.size := by omega
      have hdrop : xs.toList.drop k = xs[k] :: xs.toList.drop (k + 1) := by
        rw [← Array.getElem_toList hkl]
        exact List.drop_eq_getElem_cons (by simpa using hkl)
      rw [hdrop, List.foldlM_cons, hok k hkl, Option.map_some]
      exact ih (k + 1) (by omega) (init.push (ys[k]'(hsz ▸ hkl)))
        (by simp [hiSz]) (fun i hi => by
          by_cases hik : i < k
          · rw [Array.getElem?_push_lt (by rw [hiSz]; exact hik)]
            simpa [getElem?_pos init i (by omega)] using hiPref i hik
          · have hieq : i = k := by omega
            subst hieq
            have hp : (init.push (ys[i]'(hsz ▸ hkl)))[i]? = some (ys[i]'(hsz ▸ hkl)) := by
              simp [hiSz, Array.getElem_push]
            rw [hp, getElem?_pos ys i (by omega)]) (by omega)
  exact aux 0 (Nat.zero_le _) #[] rfl (fun i hi => by omega)

private theorem decodeDagWriter_encode (jh : Jvm.JvmHeap AlgExt) (w : Algorithm.DagWriter) :
    decodeDagWriter (encodeDagWriter jh w).2 (encodeDagWriter jh w).1 = some w := by
  dsimp only [encodeDagWriter]
  have hlFold := foldl_encodeBuckets_list encodeLeafBucketList decodeLeafBucketList List.length
    encodeLeafBucketList_spec (fun _ _ => decodeLeafBucketList_mono)
    w.leafT.toList #[] [] jh rfl (fun i hi => by simp at hi) (fun i hi => by simp at hi)
  rw [Array.foldl_toList] at hlFold
  let lRes := w.leafT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeLeafBucketList p.2 b; (p.1.push r.1, r.2)) (#[], jh)
  change HeapExtends jh lRes.2 ∧ lRes.1.size = ([] ++ w.leafT.toList).length ∧ _ at hlFold
  obtain ⟨_, hlSz, hlBnd, hlOk⟩ := hlFold
  simp only [List.nil_append] at hlSz hlBnd hlOk
  have hnFold := foldl_encodeBuckets_list encodeNodeBucketList decodeNodeBucketList List.length
    encodeNodeBucketList_spec (fun _ _ => decodeNodeBucketList_mono)
    w.nodeT.toList #[] [] lRes.2 rfl (fun i hi => by simp at hi) (fun i hi => by simp at hi)
  rw [Array.foldl_toList] at hnFold
  let nRes := w.nodeT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeNodeBucketList p.2 b; (p.1.push r.1, r.2)) (#[], lRes.2)
  change HeapExtends lRes.2 nRes.2 ∧ nRes.1.size = ([] ++ w.nodeT.toList).length ∧ _ at hnFold
  obtain ⟨hnExt, hnSz, hnBnd, hnOk⟩ := hnFold
  simp only [List.nil_append] at hnSz hnBnd hnOk
  let h3 := (nRes.2.alloc (.objArray "java/lang/Object" lRes.1)).2
  let h4 := (h3.alloc (.objArray "java/lang/Object" nRes.1)).2
  let h5 := (h4.alloc (.objArray "java/lang/Object"
    #[.boxedInt 0, .ext (.strGrowBuf w.lines), .heapRef nRes.2.objects.size,
      .heapRef h3.objects.size])).2
  have hext23 : HeapExtends nRes.2 h3 := HeapExtends_alloc _ _
  have hext34 : HeapExtends h3 h4 := HeapExtends_alloc _ _
  have hext45 : HeapExtends h4 h5 := HeapExtends_alloc _ _
  have hext25 : HeapExtends nRes.2 h5 := HeapExtends_trans hext23 (HeapExtends_trans hext34 hext45)
  have hext15 : HeapExtends lRes.2 h5 := HeapExtends_trans hnExt hext25
  have hget5 : h5.get? h4.objects.size = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .ext (.strGrowBuf w.lines), .heapRef nRes.2.objects.size,
        .heapRef h3.objects.size]) := jvmHeap_get?_alloc_self _ _
  have hgetL5 : h5.get? nRes.2.objects.size = some (.objArray "java/lang/Object" lRes.1) := by
    have hlt34 : nRes.2.objects.size < h3.objects.size := by simp [h3, Jvm.JvmHeap.alloc]
    have hlt45 : nRes.2.objects.size < h4.objects.size := Nat.lt_trans hlt34 (by simp [h4, Jvm.JvmHeap.alloc])
    rw [hext45.2 _ hlt45, hext34.2 _ hlt34]
    exact jvmHeap_get?_alloc_self _ _
  have hgetN5 : h5.get? h3.objects.size = some (.objArray "java/lang/Object" nRes.1) := by
    rw [hext45.2 _ (by simp [h4, Jvm.JvmHeap.alloc])]
    exact jvmHeap_get?_alloc_self _ _
  have hlFoldM : lRes.1.foldlM (fun acc v =>
      (decodeLeafBucketList h5 (h5.objects.size + 2) v).map acc.push) #[] = some w.leafT := by
    apply foldlM_array_eq_some_of_forall _ lRes.1 w.leafT (by simpa using hlSz)
    intro i hi
    have hiw : i < w.leafT.toList.length := by rw [← hlSz]; exact hi
    have hlt : w.leafT.toList[i].length < h5.objects.size + 2 :=
      Nat.lt_of_lt_of_le (hlBnd i hiw) (Nat.le_trans hext15.1 (by omega))
    have h1 := decodeLeafBucketList_mono hext15 (hlOk i hi hiw (h5.objects.size + 2) hlt)
    simpa [Array.getElem_toList] using h1
  have hnFoldM : nRes.1.foldlM (fun acc v =>
      (decodeNodeBucketList h5 (h5.objects.size + 2) v).map acc.push) #[] = some w.nodeT := by
    apply foldlM_array_eq_some_of_forall _ nRes.1 w.nodeT (by simpa using hnSz)
    intro i hi
    have hiw : i < w.nodeT.toList.length := by rw [← hnSz]; exact hi
    have hlt : w.nodeT.toList[i].length < h5.objects.size + 2 :=
      Nat.lt_of_lt_of_le (hnBnd i hiw) (Nat.le_trans hext25.1 (by omega))
    have h1 := decodeNodeBucketList_mono hext25 (hnOk i hi hiw (h5.objects.size + 2) hlt)
    simpa [Array.getElem_toList] using h1
  have hae1 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf w.lines),
      Jvm.JvmVal.heapRef nRes.2.objects.size, Jvm.JvmVal.heapRef h3.objects.size])[1]? =
      some (Jvm.JvmVal.ext (AlgExt.strGrowBuf w.lines)) := rfl
  have hae2 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf w.lines),
      Jvm.JvmVal.heapRef nRes.2.objects.size, Jvm.JvmVal.heapRef h3.objects.size])[2]? =
      some (Jvm.JvmVal.heapRef nRes.2.objects.size) := rfl
  have hae3 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf w.lines),
      Jvm.JvmVal.heapRef nRes.2.objects.size, Jvm.JvmVal.heapRef h3.objects.size])[3]? =
      some (Jvm.JvmVal.heapRef h3.objects.size) := rfl
  change decodeDagWriter h5 (.heapRef h4.objects.size) = some w
  unfold decodeDagWriter
  dsimp only
  rw [hget5]
  dsimp only
  rw [hae1, hae2, hae3]
  dsimp only
  rw [hgetL5, hgetN5]
  simp only [hlFoldM, hnFoldM]
  rfl

private theorem runJvmResFast_i2l_mask32 {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 3) prog pc (.i2l :: .lconst 4294967295 :: .land :: rest)
        ⟨pc0, .i32 x :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 3) rest ⟨pc + 3, .i64 x.toUInt64 :: stkRest, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast]

private theorem stepStatic_ulongCtor5b {pc : Nat} {v : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, v :: rest, locs, jh, hp⟩
      "kotlin/ULong" "constructor-impl" "(J)J" =
      .inl (some ⟨pc + 1, v :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_uintCtor5b {pc : Nat} {v : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, v :: rest, locs, jh, hp⟩) := rfl

private theorem dagWriter_pair_finish
    (f pc : Nat) (prog : List JvmInstr) (st0 : JvmState)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (res : UInt32 × Algorithm.DagWriter)
    (hpc0 : st0.pc = 0)
    (hrun : runJvmResFast f prog 0 (prog.drop 0) st0 =
      some (.pair (.boxedUInt res.1) (encodeDagWriter jh res.2).1,
        ⟨pc, [.pair (.boxedUInt res.1) (encodeDagWriter jh res.2).1],
          locs, (encodeDagWriter jh res.2).2, hp⟩)) :
    ∃ f' w' st',
      runJvmRes f' prog st0 = some (.pair (.boxedUInt res.1) w', st') ∧
      decodeDagWriter st'.jvmHeap w' = some res.2 ∧
      st'.heap = hp :=
  ⟨f, (encodeDagWriter jh res.2).1, _, runJvmRes_of_runJvmResFast0 f prog _ _ hpc0 hrun,
    decodeDagWriter_encode jh res.2, rfl⟩

private theorem stepStatic_dagWriter_addLeafAt
    {pc wAddr : Nat} {slot : UInt32} {leaf : UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {w : Algorithm.DagWriter}
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w) :
    stepInvokeStatic ⟨pc, .i32 slot :: .i64 leaf :: .heapRef wAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addLeafAt-7pzH9BY" "(Ljava/lang/Object;JI)Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedUInt (w.addLeafAt leaf slot).1)
          (encodeDagWriter jh (w.addLeafAt leaf slot).2).1 :: rest,
        locs, (encodeDagWriter jh (w.addLeafAt leaf slot).2).2, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, .i32 slot :: .i64 leaf :: .heapRef wAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addLeafAt-7pzH9BY" "(Ljava/lang/Object;JI)Lkotlin/Pair;" =
      match decodeDagWriter jh (.heapRef wAddr) with
      | some w =>
        let r := w.addLeafAt leaf slot
        let enc := encodeDagWriter jh r.2
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) enc.1 :: rest, locs, enc.2, hp⟩)
      | none => .inr none := rfl
  rw [h0, hdec]

private theorem stepStatic_dagWriter_addNodeAt
    {pc wAddr : Nat} {slot : UInt32} {kVal : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32} {w : Algorithm.DagWriter}
    (hk : decodeNodeKey kVal = some k)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w) :
    stepInvokeStatic ⟨pc, .i32 slot :: kVal :: .heapRef wAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addNodeAt-jXDDuk8"
      "(Ljava/lang/Object;Lkotlin/Pair;I)Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedUInt (w.addNodeAt k slot).1)
          (encodeDagWriter jh (w.addNodeAt k slot).2).1 :: rest,
        locs, (encodeDagWriter jh (w.addNodeAt k slot).2).2, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, .i32 slot :: kVal :: .heapRef wAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addNodeAt-jXDDuk8"
      "(Ljava/lang/Object;Lkotlin/Pair;I)Lkotlin/Pair;" =
      match decodeNodeKey kVal, decodeDagWriter jh (.heapRef wAddr) with
      | some k, some w =>
        let r := w.addNodeAt k slot
        let enc := encodeDagWriter jh r.2
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) enc.1 :: rest, locs, enc.2, hp⟩)
      | _, _ => .inr none := rfl
  rw [h0, hk, hdec]

private abbrev progALF : List JvmInstr := f_Algorithm_DagWriter_addLeaf_prog

theorem dagWriter_addLeaf_equiv
    (w : Algorithm.DagWriter) (wAddr : Nat) (leaf : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hsize : leaf ≠ 0 → w.leafT.size.toUInt32 ≠ 0) :
    ∃ f w' st',
      runJvmRes f f_Algorithm_DagWriter_addLeaf_prog
          ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr)) 1 (.i64 leaf),
            jh, hp⟩ =
        some (.pair (.boxedUInt (w.addLeaf leaf).1) w', st') ∧
      decodeDagWriter st'.jvmHeap w' = some (w.addLeaf leaf).2 ∧
      st'.heap = hp := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (fun _ => .null) 0 (.heapRef wAddr)) 1 (.i64 leaf)
  by_cases hzero : leaf = 0
  · subst hzero
    have hadd : w.addLeaf 0 = (0, w) := by simp [Algorithm.DagWriter.addLeaf]
    rw [hadd]
    suffices hsuf : ∃ locs',
        runJvmResFast 11 progALF 0 (progALF.drop 0) ⟨0, [], locs0, jh, hp⟩ =
          some (.pair (.boxedUInt 0) (.heapRef wAddr),
            ⟨37, [.pair (.boxedUInt 0) (.heapRef wAddr)], locs', jh, hp⟩) by
      obtain ⟨locs', hrun⟩ := hsuf
      exact ⟨11, .heapRef wAddr, _, runJvmRes_of_runJvmResFast0 11 progALF _ _ rfl hrun, hdec, rfl⟩
    refine ⟨locs0, ?_⟩
    conv => lhs; arg 4; rw [show progALF = progALF.drop 0 from rfl]
    rw [show (11 : Nat) = 7 + 4 from rfl]
    step_drop_at 4
    step1_load 1 (.i64 0), (by simp [locs0, setLocal])
    step1
    rw [runJvmResFast_lcmp]
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifeq_branch rfl]
    step_drop_at 7
    rw [runJvmResFast_newClass_pair]
    rw [show (6 : Nat) = 4 + 1 + 1 from rfl]
    step1; step1
    rw [show (4 : Nat) = 3 + 1 from rfl]
    rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
    rw [show (3 : Nat) = 2 + 1 from rfl]
    step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
    rw [runJvmResFast_invokespecial_pair_init]
    exact runJvmResFast_areturn
  · obtain ⟨_, _, lAddr, _, lBuckets, _, _, _,
      hgw, _, he2, _, hgl, _, hlSz, _, _, _⟩ := decodeDagWriter_unpack hdec
    have hne : (leaf == 0) = false := beq_false_of_ne hzero
    have hadd : w.addLeaf leaf =
        w.addLeafAt leaf (Algorithm.leafSlot leaf w.leafT.size.toUInt32) := by
      simp [Algorithm.DagWriter.addLeaf, hne]
    rw [hadd]
    let slot := Algorithm.leafSlot leaf w.leafT.size.toUInt32
    apply dagWriter_pair_finish 31 30 progALF _ locs0 jh hp (w.addLeafAt leaf slot) rfl
    conv => lhs; arg 4; rw [show progALF = progALF.drop 0 from rfl]
    rw [show (31 : Nat) = 27 + 4 from rfl]
    step_drop_at 4
    step1_load 1 (.i64 leaf), (by simp [setLocal])
    step1
    rw [runJvmResFast_lcmp]
    dsimp only
    rw [runJvmResFast_ifeq_fallthrough (by
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      split <;> decide)]
    rw [show (27 : Nat) = 16 + 11 from rfl]
    step_drop_at 11
    step1_load 0 (.heapRef wAddr), (by simp [setLocal])
    step1_load 1 (.i64 leaf), (by simp [setLocal])
    step1_load 1 (.i64 leaf), (by simp [setLocal])
    step1; step1
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
    step1; step1
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
    step1
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5b]
    rw [show (16 : Nat) = 3 + 13 from rfl]
    step_drop_at 13
    step1_load 0 (.heapRef wAddr), (by simp [setLocal])
    step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    step1_load 0 (.heapRef wAddr), (by simp [setLocal])
    rw [runJvmResFast_checkcast_objArray_any hgw]
    step1
    rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he2)]
    step1; step1
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [runJvmResFast_checkcast_objArray_any hgl]
    rw [runJvmResFast_arraylength_obj hgl]
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5b]
    rw [show (UInt32.ofNat lBuckets.size) = w.leafT.size.toUInt32 by simp [hlSz]]
    step_drop_at 3
    rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned (hsize hzero))]
    change runJvmResFast 2 progALF (24 + 1 + 1 + 1 + 1 + 1)
      (.invokestatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addLeafAt-7pzH9BY"
          "(Ljava/lang/Object;JI)Lkotlin/Pair;" ::
        .areturn :: List.drop 31 (List.drop 0 progALF))
      ⟨24 + 1 + 1 + 1 + 1 + 1, [.i32 slot, .i64 leaf, .heapRef wAddr], locs0, jh, hp⟩ =
      some (.pair (.boxedUInt (w.addLeafAt leaf slot).1)
          (encodeDagWriter jh (w.addLeafAt leaf slot).2).1,
        ⟨30, [.pair (.boxedUInt (w.addLeafAt leaf slot).1)
          (encodeDagWriter jh (w.addLeafAt leaf slot).2).1],
          locs0, (encodeDagWriter jh (w.addLeafAt leaf slot).2).2, hp⟩)
    rw [runJvmResFast_invokestatic_step (stepStatic_dagWriter_addLeafAt hdec)]
    exact runJvmResFast_areturn

private abbrev progANode : List JvmInstr := f_Algorithm_DagWriter_addNode_prog

theorem dagWriter_addNode_equiv
    (w : Algorithm.DagWriter) (wAddr : Nat) (level nw ne sw se : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hsize : w.nodeT.size.toUInt32 ≠ 0) :
    ∃ f w' st',
      runJvmRes f f_Algorithm_DagWriter_addNode_prog
          ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.heapRef wAddr)) 1 (.i32 level)) 2 (.i32 nw)) 3 (.i32 ne))
            4 (.i32 sw)) 5 (.i32 se), jh, hp⟩ =
        some (.pair (.boxedUInt (w.addNode level nw ne sw se).1) w', st') ∧
      decodeDagWriter st'.jvmHeap w' = some (w.addNode level nw ne sw se).2 ∧
      st'.heap = hp := by
  obtain ⟨_, _, _, _, _, nAddr, _, nBuckets,
    hgw, _, _, he3, _, hgn, _, hnSz, _, _⟩ := decodeDagWriter_unpack hdec
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (fun _ => .null) 0 (.heapRef wAddr)) 1 (.i32 level)) 2 (.i32 nw))
    3 (.i32 ne)) 4 (.i32 sw)) 5 (.i32 se)
  let k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 := (level, nw, ne, sw, se)
  let kVal := encodeNodeKey k
  let slot := Algorithm.nodeSlot k w.nodeT.size.toUInt32
  have hkDec : decodeNodeKey kVal = some k := rfl
  have hnode : w.addNode level nw ne sw se = w.addNodeAt k slot := rfl
  rw [hnode]
  apply dagWriter_pair_finish 96 95 progANode _ locs0 jh hp (w.addNodeAt k slot) rfl
  conv => lhs; arg 4; rw [show progANode = progANode.drop 0 from rfl]
  rw [show (96 : Nat) = 73 + 23 from rfl]
  step_drop_at 23
  step1_load 0 (.heapRef wAddr), (by simp [setLocal])
  rw [runJvmResFast_newClass_pair]
  step1
  step1_load 1 (.i32 level), (by simp [setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
  rw [runJvmResFast_newClass_pair]
  step1
  step1_load 2 (.i32 nw), (by simp [setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
  rw [runJvmResFast_newClass_pair]
  step1
  step1_load 3 (.i32 ne), (by simp [setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
  rw [runJvmResFast_newClass_pair]
  step1
  step1_load 4 (.i32 sw), (by simp [setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
  step1_load 5 (.i32 se), (by simp [setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
  rw [runJvmResFast_invokespecial_pair_init]
  rw [runJvmResFast_invokespecial_pair_init]
  rw [runJvmResFast_invokespecial_pair_init]
  rw [runJvmResFast_invokespecial_pair_init]
  change runJvmResFast 73 progANode 23 (progANode.drop 23)
    ⟨23, [kVal, .heapRef wAddr], locs0, jh, hp⟩ = _
  rw [show (73 : Nat) = 69 + 4 from rfl]
  step_drop_at 4
  step1; step1; step1; step1
  rw [show (69 : Nat) = 64 + 5 from rfl]
  step_drop_at 5
  step1_load 1 (.i32 level), (by simp [locs0, setLocal])
  rw [runJvmResFast_i2l_mask32]
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  rw [show (64 : Nat) = 56 + 8 from rfl]
  step_drop_at 8
  step1; step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1_load 2 (.i32 nw), (by simp [locs0, setLocal])
  rw [runJvmResFast_i2l_mask32]
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  rw [show (56 : Nat) = 46 + 10 from rfl]
  step_drop_at 10
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1_load 3 (.i32 ne), (by simp [locs0, setLocal])
  rw [runJvmResFast_i2l_mask32]
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  rw [show (46 : Nat) = 36 + 10 from rfl]
  step_drop_at 10
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1_load 4 (.i32 sw), (by simp [locs0, setLocal])
  rw [runJvmResFast_i2l_mask32]
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  rw [show (36 : Nat) = 26 + 10 from rfl]
  step_drop_at 10
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1_load 5 (.i32 se), (by simp [locs0, setLocal])
  rw [runJvmResFast_i2l_mask32]
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  rw [show (26 : Nat) = 16 + 10 from rfl]
  step_drop_at 10
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1; step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1; step1
  rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
  step1
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5b]
  rw [show (16 : Nat) = 3 + 13 from rfl]
  step_drop_at 13
  step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
  step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  step1_load 0 (.heapRef wAddr), (by simp [locs0, setLocal])
  rw [runJvmResFast_checkcast_objArray_any hgw]
  step1
  rw [runJvmResFast_aaload_elem hgw (by decide) (by simpa using he3)]
  step1; step1
  rw [runJvmResFast_checkNotNull (by intro h; cases h)]
  rw [runJvmResFast_checkcast_objArray_any hgn]
  rw [runJvmResFast_arraylength_obj hgn]
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5b]
  rw [show (UInt32.ofNat nBuckets.size) = w.nodeT.size.toUInt32 by simp [hnSz]]
  step_drop_at 3
  rw [runJvmResFast_invokestatic_step (stepStatic_remainderUnsigned hsize)]
  change runJvmResFast 2 progANode (89 + 1 + 1 + 1 + 1 + 1)
    (.invokestatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addNodeAt-jXDDuk8"
        "(Ljava/lang/Object;Lkotlin/Pair;I)Lkotlin/Pair;" ::
      .areturn :: List.drop 96 progANode)
    ⟨89 + 1 + 1 + 1 + 1 + 1, [.i32 slot, kVal, .heapRef wAddr], locs0, jh, hp⟩ =
    some (.pair (.boxedUInt (w.addNodeAt k slot).1)
        (encodeDagWriter jh (w.addNodeAt k slot).2).1,
      ⟨95, [.pair (.boxedUInt (w.addNodeAt k slot).1)
        (encodeDagWriter jh (w.addNodeAt k slot).2).1],
        locs0, (encodeDagWriter jh (w.addNodeAt k slot).2).2, hp⟩)
  rw [runJvmResFast_invokestatic_step (stepStatic_dagWriter_addNodeAt hkDec hdec)]
  exact runJvmResFast_areturn

/-! ### Part 6: writeDag & serializeMacrocellDag -/

private abbrev progWD : List JvmInstr := f_Algorithm_writeDag_prog
private abbrev progSMD : List JvmInstr := f_Algorithm_serializeMacrocellDag_prog

private theorem u32_shl2_eq_mul4 (k : UInt32) :
    k <<< ((2 : UInt32) &&& 31) = 4 * k := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  rw [show ((2 : UInt32) &&& 31) = 2 from by decide]
  change (k <<< 2).toNat = (4 * k).toNat
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]
  rw [show (2 : UInt32).toNat % 32 = 2 from by decide]
  rw [show (4 : UInt32).toNat = 4 from by decide]
  rw [Nat.shiftLeft_eq, show 2 ^ 2 = 4 from rfl, Nat.mul_comm]

private theorem u32_shl2_raw_eq_mul4 (k : UInt32) : k <<< 2 = 4 * k := by
  simpa using u32_shl2_eq_mul4 k

private theorem HeapExtends_set_of_ge {h0 h : Jvm.JvmHeap AlgExt} {a : Nat}
    {obj : Jvm.HeapObj AlgExt} (hext : HeapExtends h0 h) (hle : h0.objects.size ≤ a) :
    HeapExtends h0 (h.set a obj) := by
  refine ⟨?_, fun addr hlt => ?_⟩
  · rw [Jvm.JvmHeap.set]
    split <;> simp [Array.size_set, hext.1]
  · have hne : addr ≠ a := Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hle)
    rw [jvmHeap_get?_set_ne h obj hne, hext.2 addr hlt]

private theorem copyU64_size (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (Algorithm.copyU64 src n i dst).size = dst.size := by
  by_cases h : i < n
  · have hterm : n.toNat - (i + 1).toNat < n.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt n
        simp only [UInt32.toNat_one]
        omega
      omega
    rw [Algorithm.copyU64.eq_1]
    simp only [h, ↓reduceDIte]
    rw [copyU64_size src n (i + 1) (dst.set! i.toNat src[i.toNat]!)]
    exact Array.size_setIfInBounds
  · rw [Algorithm.copyU64.eq_1]
    simp [h]
termination_by n.toNat - i.toNat

private theorem u64Buf_push_inv (b : Array UInt64) (x : UInt64) (k : UInt32)
    (hkLt : k.toNat < 2 ^ 29) (hb1 : 0 < b.size) (hb2 : b.size < 2 ^ 31)
    (hb0 : b[0]!.toUInt32 = k) (hbk : k.toNat < b.size) :
    let b' := Algorithm.U64Buf.push b x
    0 < b'.size ∧ b'.size < 2 ^ 31 ∧ b'[0]!.toUInt32 = k + 1 ∧ (k + 1).toNat < b'.size := by
  dsimp only [Algorithm.U64Buf.push]
  rw [hb0]
  have hk1 : (k + 1).toNat = k.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
  have hbCap : b.size.toUInt32.toNat = b.size := by
    change (UInt32.ofNat b.size).toNat = b.size
    exact UInt32.toNat_ofNat_of_lt (Nat.lt_trans hb2 (by decide))
  have hcast : (k + 1).toUInt64.toUInt32 = k + 1 := by
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; simp
  by_cases hlt : k + 1 < b.size.toUInt32
  · simp only [hlt, ↓reduceIte]
    have hsz1 : ((b.set! (k + 1).toNat x).set! 0 (k + 1).toUInt64).size = b.size := by
      simp [Array.size_setIfInBounds]
    have hm : (k + 1).toNat < b.size := by
      have h := UInt32.lt_iff_toNat_lt.mp hlt
      rw [hbCap] at h
      exact h
    have h0' : ((b.set! (k + 1).toNat x).set! 0 (k + 1).toUInt64)[0]! = (k + 1).toUInt64 := by
      have h0lt : 0 < (b.set! (k + 1).toNat x).size := by simp [Array.size_setIfInBounds, hb1]
      rw [getElem!_pos _ _ (by simp [Array.size_setIfInBounds, hb1])]
      simp [Array.set!_eq_setIfInBounds]
    refine ⟨by omega, by omega, ?_, by omega⟩
    rw [h0', hcast]
  · simp only [hlt, ↓reduceIte]
    have hbSzLe : b.size ≤ k.toNat + 1 :=
      Nat.le_of_not_lt fun hgt =>
        hlt (UInt32.lt_iff_toNat_lt.mpr (by rw [hk1, hbCap]; exact hgt))
    let cap := b.size.toUInt32
    have h2cap : (2 * cap + 1).toNat = 2 * b.size + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, show (2 : UInt32).toNat = 2 from rfl,
        UInt32.toNat_one, show cap.toNat = b.size from hbCap]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hszC : ((Algorithm.copyU64 b cap 0 (Array.replicate (2 * cap + 1).toNat 0)).set!
        (k + 1).toNat x).size = 2 * b.size + 1 := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
        copyU64_size, Array.size_replicate, h2cap]
    have hszFinal : (((Algorithm.copyU64 b cap 0 (Array.replicate (2 * cap + 1).toNat 0)).set!
        (k + 1).toNat x).set! 0 (k + 1).toUInt64).size = 2 * b.size + 1 := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hszC]
    have h0' : (((Algorithm.copyU64 b cap 0 (Array.replicate (2 * cap + 1).toNat 0)).set!
        (k + 1).toNat x).set! 0 (k + 1).toUInt64)[0]! = (k + 1).toUInt64 := by
      have h0lt : 0 < ((Algorithm.copyU64 b cap 0 (Array.replicate (2 * cap + 1).toNat 0)).set!
          (k + 1).toNat x).size := by omega
      rw [getElem!_pos _ _ (by omega)]
      simp [Array.set!_eq_setIfInBounds]
    refine ⟨by rw [hszFinal]; omega, by rw [hszFinal]; omega, ?_, by rw [hszFinal]; omega⟩
    rw [h0', hcast]

private theorem encodeDagWriter_heapExtends (jh : Jvm.JvmHeap AlgExt) (w : Algorithm.DagWriter) :
    HeapExtends jh (encodeDagWriter jh w).2 := by
  dsimp only [encodeDagWriter]
  have hlFold := foldl_encodeBuckets_list encodeLeafBucketList decodeLeafBucketList List.length
    encodeLeafBucketList_spec (fun _ _ => decodeLeafBucketList_mono)
    w.leafT.toList #[] [] jh rfl (fun i hi => by simp at hi) (fun i hi => by simp at hi)
  rw [Array.foldl_toList] at hlFold
  let lRes := w.leafT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeLeafBucketList p.2 b; (p.1.push r.1, r.2)) (#[], jh)
  change HeapExtends jh lRes.2 ∧ _ at hlFold
  obtain ⟨hlExt, _⟩ := hlFold
  have hnFold := foldl_encodeBuckets_list encodeNodeBucketList decodeNodeBucketList List.length
    encodeNodeBucketList_spec (fun _ _ => decodeNodeBucketList_mono)
    w.nodeT.toList #[] [] lRes.2 rfl (fun i hi => by simp at hi) (fun i hi => by simp at hi)
  rw [Array.foldl_toList] at hnFold
  let nRes := w.nodeT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeNodeBucketList p.2 b; (p.1.push r.1, r.2)) (#[], lRes.2)
  change HeapExtends lRes.2 nRes.2 ∧ _ at hnFold
  obtain ⟨hnExt, _⟩ := hnFold
  let h3 := (nRes.2.alloc (.objArray "java/lang/Object" lRes.1)).2
  let h4 := (h3.alloc (.objArray "java/lang/Object" nRes.1)).2
  exact HeapExtends_trans hlExt (HeapExtends_trans hnExt
    (HeapExtends_trans (HeapExtends_alloc _ _)
      (HeapExtends_trans (HeapExtends_alloc _ _) (HeapExtends_alloc _ _))))

private theorem encodeDagWriter_fst_spec (jh : Jvm.JvmHeap AlgExt) (w : Algorithm.DagWriter) :
    ∃ a elems, (encodeDagWriter jh w).1 = .heapRef a ∧
      (encodeDagWriter jh w).2.get? a = some (.objArray "java/lang/Object" elems) ∧
      elems.size = 4 ∧
      elems[1]? = some (.ext (.strGrowBuf w.lines)) := by
  dsimp only [encodeDagWriter]
  let lRes := w.leafT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeLeafBucketList p.2 b; (p.1.push r.1, r.2)) (#[], jh)
  let nRes := w.nodeT.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) b =>
    let r := encodeNodeBucketList p.2 b; (p.1.push r.1, r.2)) (#[], lRes.2)
  let h3 := (nRes.2.alloc (.objArray "java/lang/Object" lRes.1)).2
  let h4 := (h3.alloc (.objArray "java/lang/Object" nRes.1)).2
  let elems : Array JvmVal := #[.boxedInt 0, .ext (.strGrowBuf w.lines),
    .heapRef nRes.2.objects.size, .heapRef h3.objects.size]
  refine ⟨h4.objects.size, elems, rfl, jvmHeap_get?_alloc_self h4 (.objArray "java/lang/Object" elems),
    rfl, rfl⟩

private theorem alloc_obj4_set (jh : Jvm.JvmHeap AlgExt) (v0 v1 v2 v3 : JvmVal) :
    let h1 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 4) .null))).2
    let a := jh.objects.size
    let h2 := h1.set a (.objArray "java/lang/Object"
      ((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) v0 (by decide)))
    let h3 := h2.set a (.objArray "java/lang/Object"
      (((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) v0 (by decide)).set
        (UInt32.toNat 1) v1 (by simp [Array.size_set])))
    let h4 := h3.set a (.objArray "java/lang/Object"
      ((((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) v0 (by decide)).set
        (UInt32.toNat 1) v1 (by simp [Array.size_set])).set
        (UInt32.toNat 2) v2 (by simp [Array.size_set])))
    h4.set a (.objArray "java/lang/Object"
      (((((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) v0 (by decide)).set
        (UInt32.toNat 1) v1 (by simp [Array.size_set])).set
        (UInt32.toNat 2) v2 (by simp [Array.size_set])).set
        (UInt32.toNat 3) v3 (by simp [Array.size_set]))) =
      (jh.alloc (.objArray "java/lang/Object" #[v0, v1, v2, v3])).2 := by
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.size_push,
    Nat.lt_succ_self, ↓reduceDIte, array_push_set_last]
  rfl

private theorem decodeDagWriter_init (jh : Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf String) (cap : Nat)
    (lAddr emptyL nAddr emptyN wAddr : Nat)
    (lArr nArr : Array JvmVal)
    (hlSz : lArr.size = cap) (hlElem : ∀ i (hi : i < lArr.size), lArr[i] = .heapRef emptyL)
    (hnSz : nArr.size = cap) (hnElem : ∀ i (hi : i < nArr.size), nArr[i] = .heapRef emptyN)
    (hgetW : jh.get? wAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .ext (.strGrowBuf b), .heapRef lAddr, .heapRef nAddr]))
    (hgetL : jh.get? lAddr = some (.objArray "java/lang/Object" lArr))
    (hgetN : jh.get? nAddr = some (.objArray "java/lang/Object" nArr))
    (hgetEL : jh.get? emptyL = some (.objArray "java/lang/Object" #[.boxedInt 0]))
    (hgetEN : jh.get? emptyN = some (.objArray "java/lang/Object" #[.boxedInt 0])) :
    decodeDagWriter jh (.heapRef wAddr) =
      some ⟨b, Array.replicate cap [], Array.replicate cap []⟩ := by
  have hdecEL : decodeLeafBucketList jh (jh.objects.size + 2) (.heapRef emptyL) = some [] := by
    unfold decodeLeafBucketList
    simp [hgetEL]
  have hdecEN : decodeNodeBucketList jh (jh.objects.size + 2) (.heapRef emptyN) = some [] := by
    unfold decodeNodeBucketList
    simp [hgetEN]
  have hlFoldM : lArr.foldlM (fun acc v =>
      (decodeLeafBucketList jh (jh.objects.size + 2) v).map acc.push) #[] =
      some (Array.replicate cap []) := by
    apply foldlM_array_eq_some_of_forall _ lArr (Array.replicate cap [])
      (by simp [hlSz, Array.size_replicate])
    intro i hi
    rw [hlElem i hi, hdecEL]
    simp [Array.getElem_replicate]
  have hnFoldM : nArr.foldlM (fun acc v =>
      (decodeNodeBucketList jh (jh.objects.size + 2) v).map acc.push) #[] =
      some (Array.replicate cap []) := by
    apply foldlM_array_eq_some_of_forall _ nArr (Array.replicate cap [])
      (by simp [hnSz, Array.size_replicate])
    intro i hi
    rw [hnElem i hi, hdecEN]
    simp [Array.getElem_replicate]
  have hae1 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf b),
      Jvm.JvmVal.heapRef lAddr, Jvm.JvmVal.heapRef nAddr])[1]? =
      some (Jvm.JvmVal.ext (AlgExt.strGrowBuf b)) := rfl
  have hae2 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf b),
      Jvm.JvmVal.heapRef lAddr, Jvm.JvmVal.heapRef nAddr])[2]? =
      some (Jvm.JvmVal.heapRef lAddr) := rfl
  have hae3 : (#[Jvm.JvmVal.boxedInt 0, Jvm.JvmVal.ext (AlgExt.strGrowBuf b),
      Jvm.JvmVal.heapRef lAddr, Jvm.JvmVal.heapRef nAddr])[3]? =
      some (Jvm.JvmVal.heapRef nAddr) := rfl
  unfold decodeDagWriter
  dsimp only
  rw [hgetW]
  dsimp only
  rw [hae1, hae2, hae3]
  dsimp only
  rw [hgetL, hgetN]
  simp only [hlFoldM, hnFoldM]
  rfl

private theorem decodeStrArray_objArray2 (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (cls s0 s1 : String) (locs : Nat → JvmVal)
    (hget : jh.get? addr = some (.objArray cls #[.str s0, .str s1])) :
    decodeStrArray ⟨0, [], locs, jh, hp⟩ (.heapRef addr) = some #[s0, s1] := by
  simp [decodeStrArray, hget]

private theorem stepStatic_uintArrayGet {pc addr : Nat} {elems : Array UInt32} {idx : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.intArray elems))
    (hs : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    stepInvokeStatic ⟨pc, .i32 idx :: .heapRef addr :: rest, locs, jh, hp⟩
      "kotlin/UIntArray" "get-pVg5ArA" "([II)I" =
      .inl (some ⟨pc + 1, .i32 elems[idx.toNat] :: rest, locs, jh, hp⟩) := by
  unfold stepInvokeStatic Jvm.stepInstr Jvm.stepInvokeStaticGeneric
  dsimp only
  simp [Jvm.JvmVal.asI32?, hs, hget, hlt]

private theorem stepStatic_u64BufGet {pc id : Nat} {arr : Array UInt64} {idx : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : hp.u64Arrays[id]? = some arr) :
    stepInvokeStatic ⟨pc, .i32 idx :: .ext (.u64Ref id) :: rest, locs, jh, hp⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 arr[idx.toNat]! :: rest, locs, jh, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, .i32 idx :: .ext (.u64Ref id) :: rest, locs, jh, hp⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match hp.u64Arrays[id]? with
      | some arr =>
        .inl (some ⟨pc + 1, .i64 (arr[idx.toNat]!) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [h0, hget]

private theorem stepStatic_u64BufEmpty_5b {pc : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩ "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_U64Buf_empty" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }⟩) := rfl

private theorem stepStatic_u64BufPush_5b {pc id : Nat} {arr : Array UInt64} {x : UInt64}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : hp.u64Arrays[id]? = some arr) :
    stepInvokeStatic ⟨pc, .i64 x :: .ext (.u64Ref id) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.push arr x] }⟩) := by
  have h0 : stepInvokeStatic ⟨pc, .i64 x :: .ext (.u64Ref id) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      match hp.u64Arrays[id]? with
      | some arr =>
        let pushed := Algorithm.U64Buf.push arr x
        let newId := hp.u64Arrays.length
        .inl (some ⟨pc + 1, .ext (.u64Ref newId) :: rest, locs, jh,
          { hp with u64Arrays := hp.u64Arrays ++ [pushed] }⟩)
      | none => .inr none := rfl
  rw [h0, hget]

private theorem stepStatic_dagWriter_addEntry
    {pc wAddr : Nat} {m : Algorithm.MacroCell} {c1 c2 c3 c4 : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {w : Algorithm.DagWriter}
    (hdec : decodeDagWriter jh (.heapRef wAddr) = some w) :
    stepInvokeStatic
      ⟨pc, .i32 c4 :: .i32 c3 :: .i32 c2 :: .i32 c1 :: .ext (.mc m) :: .heapRef wAddr :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addEntry-Z0ptBHY"
      "(Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;IIII)Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedUInt (w.addEntry m c1 c2 c3 c4).1)
          (encodeDagWriter jh (w.addEntry m c1 c2 c3 c4).2).1 :: rest,
        locs, (encodeDagWriter jh (w.addEntry m c1 c2 c3 c4).2).2, hp⟩) := by
  have h0 : stepInvokeStatic
      ⟨pc, .i32 c4 :: .i32 c3 :: .i32 c2 :: .i32 c1 :: .ext (.mc m) :: .heapRef wAddr :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_DagWriter_addEntry-Z0ptBHY"
      "(Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;IIII)Lkotlin/Pair;" =
      match decodeDagWriter jh (.heapRef wAddr) with
      | some w =>
        let r := w.addEntry m c1 c2 c3 c4
        let p := encodeDagWriter jh r.2
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) p.1 :: rest, locs, p.2, hp⟩)
      | none => .inr none := rfl
  rw [h0, hdec]

private def mcElemPush (acc : Array Algorithm.MacroCell) :
    JvmVal → Option (Array Algorithm.MacroCell)
  | .ext (.mc m) => some (acc.push m)
  | _ => none

private theorem stepStatic_writeDag_match
    {pc entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic
      ⟨pc, .heapRef wAddr :: .ext (.u64Ref idsId) :: .i32 n :: .i32 k ::
        .heapRef kidsAddr :: .heapRef entriesAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_writeDag-EGiNdXo"
      "([Ljava/lang/Object;[III[JLjava/lang/Object;)Ljava/lang/Object;" =
      match jh.get? entriesAddr, jh.get? kidsAddr, hp.u64Arrays[idsId]? with
      | some (.objArray _ eElems), some (.intArray kids), some ids =>
        let entriesOpt := eElems.foldlM mcElemPush #[]
        match entriesOpt with
        | some entries =>
          match decodeDagWriter jh (.heapRef wAddr) with
          | some w =>
            let w' := Algorithm.writeDag entries kids k n ids w
            let p := encodeDagWriter jh w'
            .inl (some ⟨pc + 1, p.1 :: rest, locs, p.2, hp⟩)
          | none => .inr none
        | none => .inr none
      | _, _, _ => .inr none := rfl

private theorem writeDag_step_match_elim
    {pc entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
    {clsE : String} {eElems : Array JvmVal} {kids : Array UInt32} {ids : Array UInt64}
    {entries : Array Algorithm.MacroCell} {w : Algorithm.DagWriter}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (wd : Array Algorithm.MacroCell → Array UInt32 → UInt32 → UInt32 →
      Array UInt64 → Algorithm.DagWriter → Algorithm.DagWriter)
    (enc : Jvm.JvmHeap AlgExt → Algorithm.DagWriter → JvmVal × Jvm.JvmHeap AlgExt)
    (h1 : jh.get? entriesAddr = some (.objArray clsE eElems))
    (h2 : jh.get? kidsAddr = some (.intArray kids))
    (h3 : hp.u64Arrays[idsId]? = some ids)
    (h4 : eElems.foldlM mcElemPush #[] = some entries)
    (h5 : decodeDagWriter jh (.heapRef wAddr) = some w) :
    (match jh.get? entriesAddr, jh.get? kidsAddr, hp.u64Arrays[idsId]? with
      | some (.objArray _ eElems), some (.intArray kids), some ids =>
        let entriesOpt := eElems.foldlM mcElemPush #[]
        match entriesOpt with
        | some entries =>
          match decodeDagWriter jh (.heapRef wAddr) with
          | some w =>
            let w' := wd entries kids k n ids w
            let p := enc jh w'
            .inl (some ⟨pc + 1, p.1 :: rest, locs, p.2, hp⟩)
          | none => .inr none
        | none => .inr none
      | _, _, _ => .inr none :
      Sum (Option JvmState) (Option JvmVal)) =
      .inl (some ⟨pc + 1, (enc jh (wd entries kids k n ids w)).1 :: rest,
        locs, (enc jh (wd entries kids k n ids w)).2, hp⟩) := by
  rw [h1, h2, h3]
  dsimp only
  rw [h4]
  dsimp only
  rw [h5]

private theorem stepStatic_writeDag_heap
    {pc entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
    {clsE : String} {eElems : Array JvmVal} {kids : Array UInt32} {ids : Array UInt64}
    {entries : Array Algorithm.MacroCell} {w : Algorithm.DagWriter}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h1 : jh.get? entriesAddr = some (.objArray clsE eElems))
    (h2 : jh.get? kidsAddr = some (.intArray kids))
    (h3 : hp.u64Arrays[idsId]? = some ids)
    (h4 : eElems.foldlM
      (fun acc v => match v with | .ext (.mc m) => some (acc.push m) | _ => none) #[] =
      some entries)
    (h5 : decodeDagWriter jh (.heapRef wAddr) = some w) :
    stepInvokeStatic
      ⟨pc, .heapRef wAddr :: .ext (.u64Ref idsId) :: .i32 n :: .i32 k ::
        .heapRef kidsAddr :: .heapRef entriesAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_writeDag-EGiNdXo"
      "([Ljava/lang/Object;[III[JLjava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1,
        (encodeDagWriter jh (Algorithm.writeDag entries kids k n ids w)).1 :: rest,
        locs, (encodeDagWriter jh (Algorithm.writeDag entries kids k n ids w)).2, hp⟩) :=
  Eq.trans stepStatic_writeDag_match
    (writeDag_step_match_elim Algorithm.writeDag encodeDagWriter h1 h2 h3 (by exact h4) h5)

private theorem stepStatic_growBufEmpty_5b {pc : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .null :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_GrowBuf_empty___redArg"
      "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩) :=
  rfl

private theorem stepStatic_growBufPush_str {pc : Nat} {s : String} {b : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .str s :: .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf (b.push s)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_growBufToArray_str {pc : Nat} {b : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
      "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strArr b.toArray :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_macrocellSingleLeaf {pc : Nat} {m : Algorithm.MacroCell}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.mc m) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_macrocellSingleLeaf"
      "(Lcom/alexvanyo/composelife/model/MacroCell;)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1,
        (match Algorithm.macrocellSingleLeaf m with | some v => .boxedULong v | none => .null) ::
          rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_formatLeafNode_5b {pc : Nat} {v : UInt64}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 v :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_formatLeafNode-VKZWuLQ" "(J)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.formatLeafNode v) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_serializeMacrocell___closed__2_5b {pc : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_serializeMacrocell___closed__2" "()[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"])).2, hp⟩) := rfl

private theorem stepStatic_checkNotNullExpressionValue_5b
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnn : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have h0 : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := rfl
  rw [h0, hnn]; rfl

private theorem stepStatic_arraysFillAll_5b {pc : Nat} {handler elem : JvmVal}
    {addr : Nat} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {cls : String} {elems : Array JvmVal} {desc : String}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hcompat : Jvm.isArrayElemCompat algHooks jh cls elem = true := by first | rfl | simp [Jvm.isArrayElemCompat]) :
    stepInvokeStatic ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest,
        locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "fill$default" desc =
      .inl (some (⟨pc + 1, stkRest, locs,
        jh.set addr (.objArray cls (Array.ofFn (n := elems.size) fun _ => elem)), hp⟩)) :=
  Jvm.stepInvokeStatic_arraysFillAll_obj algHooks (desc := desc) hcompat hget

private theorem writeDag_child_step {f pc : Nat} {rest : List JvmInstr}
    {kidsAddr idsId : Nat} {base off : UInt32}
    {kids : Array UInt32} {ids : Array UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl1 : locs 1 = .heapRef kidsAddr)
    (hl4 : locs 4 = .ext (.u64Ref idsId))
    (hl6 : locs 6 = .i32 base)
    (hKids : jh.get? kidsAddr = some (.intArray kids))
    (hIds : hp.u64Arrays[idsId]? = some ids)
    (hSlt : (base + off).toBitVec.slt 0#32 = false)
    (hLt : (base + off).toNat < kids.size) :
    let c := (ids[(kids[(base + off).toNat]! + 1).toNat]!).toUInt32
    runJvmResFast (f + 13) progWD pc
      (.aload 4 :: .aload 1 :: .iload 6 :: .iconst off :: .iadd ::
        .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
        .invokestatic "kotlin/UIntArray" "get-pVg5ArA" "([II)I" ::
        .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
        .invokestatic "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" ::
        .l2i :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: rest)
      ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f progWD (pc + 13) rest ⟨pc + 13, .i32 c :: stk, locs, jh, hp⟩ := by
  dsimp only
  rw [show f + 13 = (f + 12) + 1 from by omega]
  step1_load 4 (.ext (.u64Ref idsId)), hl4
  rw [show f + 12 = (f + 11) + 1 from by omega]
  step1_load 1 (.heapRef kidsAddr), hl1
  rw [show f + 11 = (f + 10) + 1 from by omega]
  step1_load 6 (.i32 base), hl6
  rw [show f + 10 = (f + 9) + 1 from by omega]; step1
  rw [show f + 9 = (f + 8) + 1 from by omega]; step1
  rw [show f + 8 = (f + 7) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
  rw [show f + 7 = (f + 6) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_uintArrayGet hKids hSlt hLt)]
  rw [show f + 6 = (f + 5) + 1 from by omega]; step1
  rw [show f + 5 = (f + 4) + 1 from by omega]; step1
  rw [show f + 4 = (f + 3) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
  rw [show f + 3 = (f + 2) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_u64BufGet hIds)]
  rw [show f + 2 = (f + 1) + 1 from by omega]; step1
  rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
  rw [← getElem!_pos kids (base + off).toNat hLt]

private theorem writeDag_body_step
    {entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
    {clsE : String} {eElems : Array JvmVal} {entries : Array Algorithm.MacroCell}
    {kids : Array UInt32} {ids : Array UInt64} {w : Algorithm.DagWriter}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .heapRef entriesAddr) (hl1 : locs 1 = .heapRef kidsAddr)
    (hl2 : locs 2 = .i32 k) (hl3 : locs 3 = .i32 n)
    (hl4 : locs 4 = .ext (.u64Ref idsId)) (hl5 : locs 5 = .heapRef wAddr)
    (hEnt : jh.get? entriesAddr = some (.objArray clsE eElems))
    (hESz : eElems.size = entries.size)
    (hEElem : ∀ (i : Nat) (hi : i < entries.size), eElems[i]'(hESz.symm ▸ hi) = .ext (.mc entries[i]))
    (hKids : jh.get? kidsAddr = some (.intArray kids))
    (hIds : hp.u64Arrays[idsId]? = some ids)
    (hw : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hkn : k < n) (hnBound : n.toNat < 2 ^ 29) (hnEnt : n.toNat ≤ entries.size)
    (hnKids : 4 * n.toNat ≤ kids.size) :
    let m := entries[k.toNat]!
    let c1 := (ids[(kids[(4 * k).toNat]! + 1).toNat]!).toUInt32
    let c2 := (ids[(kids[(4 * k + 1).toNat]! + 1).toNat]!).toUInt32
    let c3 := (ids[(kids[(4 * k + 2).toNat]! + 1).toNat]!).toUInt32
    let c4 := (ids[(kids[(4 * k + 3).toNat]! + 1).toNat]!).toUInt32
    let r := w.addEntry m c1 c2 c3 c4
    let enc := encodeDagWriter jh r.2
    let newIdsId := hp.u64Arrays.length
    let hp' := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.push ids r.1.toUInt64] }
    ∃ locs',
      (∀ fNext,
        runJvmResFast (fNext + 106) progWD 9 (progWD.drop 9) ⟨9, [], locs, jh, hp⟩ =
          runJvmResFast fNext progWD 9 (progWD.drop 9) ⟨9, [], locs', enc.2, hp'⟩) ∧
      locs' 0 = .heapRef entriesAddr ∧ locs' 1 = .heapRef kidsAddr ∧
      locs' 2 = .i32 (k + 1) ∧ locs' 3 = .i32 n ∧
      locs' 4 = .ext (.u64Ref newIdsId) ∧ locs' 5 = enc.1 := by
  dsimp only
  have hkLtN : k.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hkn
  have hk29 : k.toNat < 2 ^ 29 := Nat.lt_trans hkLtN hnBound
  have hkSlt : k.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hkEnt : k.toNat < entries.size := Nat.lt_of_lt_of_le hkLtN hnEnt
  have hkElems : k.toNat < eElems.size := hESz ▸ hkEnt
  have hBaseNat : (4 * k).toNat = 4 * k.toNat := by
    rw [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hSlt0 : (4 * k).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hSlt1 : (4 * k + 1).toBitVec.slt 0#32 = false := by
    apply u32_slt_zero_of_lt_2_31
    rw [UInt32.toNat_add, UInt32.toNat_one, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hSlt2 : (4 * k + 2).toBitVec.slt 0#32 = false := by
    apply u32_slt_zero_of_lt_2_31
    rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hSlt3 : (4 * k + 3).toBitVec.slt 0#32 = false := by
    apply u32_slt_zero_of_lt_2_31
    rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hLt0 : (4 * k).toNat < kids.size := by omega
  have hLt1 : (4 * k + 1).toNat < kids.size := by
    rw [UInt32.toNat_add, UInt32.toNat_one, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hLt2 : (4 * k + 2).toNat < kids.size := by
    rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hLt3 : (4 * k + 3).toNat < kids.size := by
    rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl, hBaseNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hbr : (if k == n then (0 : UInt32) else if k < n then 4294967295 else 1).toBitVec.slt 0#32 =
      true := by
    rw [compareUnsigned_slt_zero]; exact decide_eq_true hkn
  apply Exists.intro
  refine ⟨fun fNext => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · step_drop_at 4
    rw [show fNext + 106 = (fNext + 105) + 1 from by omega]
    step1_load 2 (.i32 k), hl2
    rw [show fNext + 105 = (fNext + 104) + 1 from by omega]
    step1_load 3 (.i32 n), hl3
    rw [show fNext + 104 = (fNext + 103) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    rw [show fNext + 103 = (fNext + 102) + 1 from by omega]
    rw [runJvmResFast_iflt_branch hbr]
    step_drop_at 13
    rw [show fNext + 102 = (fNext + 101) + 1 from by omega]
    step1_load 2 (.i32 k), hl2
    rw [show fNext + 101 = (fNext + 100) + 1 from by omega]; step1
    rw [show fNext + 100 = (fNext + 99) + 1 from by omega]; step1
    rw [u32_shl2_eq_mul4 k]
    rw [show fNext + 99 = (fNext + 98) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
    rw [show fNext + 98 = (fNext + 97) + 1 from by omega]; step1
    rw [show fNext + 97 = (fNext + 96) + 1 from by omega]
    step1_load 5 (.heapRef wAddr), (by simp [setLocal, hl5])
    rw [show fNext + 96 = (fNext + 95) + 1 from by omega]
    step1_load 0 (.heapRef entriesAddr), (by simp [setLocal, hl0])
    rw [show fNext + 95 = (fNext + 94) + 1 from by omega]
    step1_load 2 (.i32 k), (by simp [setLocal, hl2])
    rw [show fNext + 94 = (fNext + 93) + 1 from by omega]
    rw [runJvmResFast_aaload_elem hEnt hkSlt (getElem?_pos eElems k.toNat hkElems)]
    rw [hEElem k.toNat hkEnt]
    rw [show fNext + 93 = (fNext + 92) + 1 from by omega]; step1
    rw [show fNext + 92 = (fNext + 91) + 1 from by omega]; step1
    rw [show fNext + 91 = (fNext + 90) + 1 from by omega]
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [show fNext + 90 = (fNext + 89) + 1 from by omega]
    rw [runJvmResFast_checkcast_step rfl]
    step_drop_at 10
    rw [show fNext + 89 = (fNext + 88) + 1 from by omega]
    step1_load 4 (.ext (.u64Ref idsId)), (by simp [setLocal, hl4])
    rw [show fNext + 88 = (fNext + 87) + 1 from by omega]
    step1_load 1 (.heapRef kidsAddr), (by simp [setLocal, hl1])
    rw [show fNext + 87 = (fNext + 86) + 1 from by omega]
    step1_load 6 (.i32 (4 * k)), (by simp [setLocal])
    rw [show fNext + 86 = (fNext + 85) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step (stepStatic_uintArrayGet hKids hSlt0 hLt0)]
    rw [show fNext + 85 = (fNext + 84) + 1 from by omega]; step1
    rw [show fNext + 84 = (fNext + 83) + 1 from by omega]; step1
    rw [show fNext + 83 = (fNext + 82) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
    rw [show fNext + 82 = (fNext + 81) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step (stepStatic_u64BufGet hIds)]
    rw [show fNext + 81 = (fNext + 80) + 1 from by omega]; step1
    rw [show fNext + 80 = (fNext + 79) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
    rw [← getElem!_pos kids (4 * k).toNat hLt0]
    step_drop_at 13
    rw [show fNext + 79 = (fNext + 66) + 13 from by omega]
    rw [writeDag_child_step (off := 1) (by simp [setLocal, hl1])
      (by simp [setLocal, hl4]) (by simp [setLocal]) hKids hIds hSlt1 hLt1]
    step_drop_at 13
    rw [show fNext + 66 = (fNext + 53) + 13 from by omega]
    rw [writeDag_child_step (off := 2) (by simp [setLocal, hl1])
      (by simp [setLocal, hl4]) (by simp [setLocal]) hKids hIds hSlt2 hLt2]
    step_drop_at 13
    rw [show fNext + 53 = (fNext + 40) + 13 from by omega]
    rw [writeDag_child_step (off := 3) (by simp [setLocal, hl1])
      (by simp [setLocal, hl4]) (by simp [setLocal]) hKids hIds hSlt3 hLt3]
    step_drop_at 10
    rw [show fNext + 40 = (fNext + 39) + 1 from by omega]
    rw [← getElem!_pos entries k.toNat hkEnt]
    rw [runJvmResFast_invokestatic_step (stepStatic_dagWriter_addEntry hw)]
    rw [show fNext + 39 = (fNext + 38) + 1 from by omega]; step1
    rw [show fNext + 38 = (fNext + 37) + 1 from by omega]
    step1_load 7 _, (by simp [setLocal]; rfl)
    rw [show fNext + 37 = (fNext + 36) + 1 from by omega]
    rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]
    rw [show fNext + 36 = (fNext + 35) + 1 from by omega]; step1
    rw [show fNext + 35 = (fNext + 34) + 1 from by omega]
    step1_load 2 (.i32 k), (by simp [setLocal, hl2])
    rw [show fNext + 34 = (fNext + 33) + 1 from by omega]; step1
    rw [show fNext + 33 = (fNext + 32) + 1 from by omega]; step1
    rw [show fNext + 32 = (fNext + 31) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
    rw [show fNext + 31 = (fNext + 30) + 1 from by omega]; step1
    step_drop_at 11
    rw [show fNext + 30 = (fNext + 29) + 1 from by omega]
    step1_load 4 (.ext (.u64Ref idsId)), (by simp [setLocal, hl4])
    rw [show fNext + 29 = (fNext + 28) + 1 from by omega]
    step1_load 7 _, (by simp [setLocal]; rfl)
    rw [show fNext + 28 = (fNext + 27) + 1 from by omega]
    rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]
    rw [show fNext + 27 = (fNext + 26) + 1 from by omega]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    rw [show fNext + 26 = (fNext + 25) + 1 from by omega]
    rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox]
    rw [show fNext + 25 = (fNext + 22) + 3 from by omega]
    rw [runJvmResFast_i2l_mask32]
    rw [show fNext + 22 = (fNext + 21) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor5b]
    rw [show fNext + 21 = (fNext + 20) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step (stepStatic_u64BufPush_5b hIds)]
    rw [show fNext + 20 = (fNext + 19) + 1 from by omega]; step1
    step_drop_at 10
    rw [show fNext + 19 = (fNext + 18) + 1 from by omega]
    step1_load 0 (.heapRef entriesAddr), (by simp [setLocal, hl0])
    rw [show fNext + 18 = (fNext + 17) + 1 from by omega]; step1
    rw [show fNext + 17 = (fNext + 16) + 1 from by omega]
    step1_load 1 (.heapRef kidsAddr), (by simp [setLocal, hl1])
    rw [show fNext + 16 = (fNext + 15) + 1 from by omega]; step1
    rw [show fNext + 15 = (fNext + 14) + 1 from by omega]
    step1_load 3 (.i32 n), (by simp [setLocal, hl3])
    rw [show fNext + 14 = (fNext + 13) + 1 from by omega]; step1
    rw [show fNext + 13 = (fNext + 12) + 1 from by omega]
    step1_load 11 (.heapRef entriesAddr), (by simp [setLocal])
    rw [show fNext + 12 = (fNext + 11) + 1 from by omega]; step1
    rw [show fNext + 11 = (fNext + 10) + 1 from by omega]
    step1_load 12 (.heapRef kidsAddr), (by simp [setLocal])
    rw [show fNext + 10 = (fNext + 9) + 1 from by omega]; step1
    step_drop_at 9
    rw [show fNext + 9 = (fNext + 8) + 1 from by omega]
    step1_load 9 (.i32 (k + 1)), (by simp [setLocal])
    rw [show fNext + 8 = (fNext + 7) + 1 from by omega]; step1
    rw [show fNext + 7 = (fNext + 6) + 1 from by omega]
    step1_load 13 (.i32 n), (by simp [setLocal])
    rw [show fNext + 6 = (fNext + 5) + 1 from by omega]; step1
    rw [show fNext + 5 = (fNext + 4) + 1 from by omega]
    step1_load 10 (.ext (.u64Ref hp.u64Arrays.length)), (by simp [setLocal])
    rw [show fNext + 4 = (fNext + 3) + 1 from by omega]; step1
    rw [show fNext + 3 = (fNext + 2) + 1 from by omega]
    step1_load 8 _, (by simp [setLocal]; rfl)
    rw [show fNext + 2 = (fNext + 1) + 1 from by omega]; step1
    conv =>
      lhs; arg 5; arg 5
      simp only [Nat.mod_eq_of_lt (by omega : 4 * k.toNat < 4294967296)]
    conv =>
      rhs; arg 5; arg 5
      simp only [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
        UInt32.toNat_one, show (2 : UInt32).toNat = 2 from rfl,
        show (3 : UInt32).toNat = 3 from rfl]
      simp only [show (2 ^ 32 : Nat) = 4294967296 from rfl,
        Nat.mod_eq_of_lt (by omega : 4 * k.toNat < 4294967296)]
    exact runJvmResFast_goto
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]

private theorem runJvmResFast_writeDag_loop (m : Nat) :
    ∀ {entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
      {clsE : String} {eElems : Array JvmVal} {entries : Array Algorithm.MacroCell}
      {kids : Array UInt32} {ids : Array UInt64} {w : Algorithm.DagWriter}
      {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap},
      n.toNat - k.toNat = m →
      locs 0 = .heapRef entriesAddr →
      locs 1 = .heapRef kidsAddr →
      locs 2 = .i32 k →
      locs 3 = .i32 n →
      locs 4 = .ext (.u64Ref idsId) →
      locs 5 = .heapRef wAddr →
      jh.get? entriesAddr = some (.objArray clsE eElems) →
      ∀ (hESz : eElems.size = entries.size),
      (∀ (i : Nat) (hi : i < entries.size),
        eElems[i]'(hESz.symm ▸ hi) = .ext (.mc entries[i])) →
      jh.get? kidsAddr = some (.intArray kids) →
      hp.u64Arrays[idsId]? = some ids →
      decodeDagWriter jh (.heapRef wAddr) = some w →
      n.toNat < 2 ^ 29 →
      n.toNat ≤ entries.size →
      4 * n.toNat ≤ kids.size →
      0 < ids.size →
      ids.size < 2 ^ 31 →
      ids[0]!.toUInt32 = k →
      k.toNat < ids.size →
      ∃ f' wVal' locs' jh' hp',
        runJvmResFast f' progWD 9 (progWD.drop 9) ⟨9, [], locs, jh, hp⟩ =
          some (wVal', ⟨14, [wVal'], locs', jh', hp'⟩) ∧
        HeapExtends jh jh' ∧
        decodeDagWriter jh' wVal' = some (Algorithm.writeDag entries kids k n ids w) := by
  induction m with
  | zero =>
    intro entriesAddr kidsAddr idsId wAddr k n clsE eElems entries kids ids w locs jh hp
      hm hl0 hl1 hl2 hl3 hl4 hl5 _ _ _ _ _ hw _ _ _ _ _ _ _
    have hge : ¬ (k < n) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    have hbr : (if k == n then (0 : UInt32) else if k < n then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    refine ⟨6, .heapRef wAddr, locs, jh, hp, ?_, HeapExtends_refl jh, ?_⟩
    · step_drop_at 6
      rw [show (6 : Nat) = 5 + 1 from rfl]; step1_load 2 (.i32 k), hl2
      rw [show (5 : Nat) = 4 + 1 from rfl]; step1_load 3 (.i32 n), hl3
      rw [show (4 : Nat) = 3 + 1 from rfl]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      rw [show (3 : Nat) = 2 + 1 from rfl]
      rw [runJvmResFast_iflt_fallthrough hbr]
      rw [show (2 : Nat) = 1 + 1 from rfl]; step1_load 5 (.heapRef wAddr), hl5
      exact runJvmResFast_areturn
    · rw [Algorithm.writeDag.eq_1]; simp [hge, hw]
  | succ m ih =>
    intro entriesAddr kidsAddr idsId wAddr k n clsE eElems entries kids ids w locs jh hp
      hm hl0 hl1 hl2 hl3 hl4 hl5 hEnt hESz hEElem hKids hIds hw hnBound hnEnt hnKids
      hIds1 hIds2 hIds0 hIdsK
    by_cases hkn : k < n
    · have hkLtN : k.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hkn
      have hk29 : k.toNat < 2 ^ 29 := Nat.lt_trans hkLtN hnBound
      have hk1Nat : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
      have hextEnt : entriesAddr < jh.objects.size := jvmHeap_addr_lt_of_get? hEnt
      have hextKids : kidsAddr < jh.objects.size := jvmHeap_addr_lt_of_get? hKids
      let c1 := (ids[(kids[(4 * k).toNat]! + 1).toNat]!).toUInt32
      let c2 := (ids[(kids[(4 * k + 1).toNat]! + 1).toNat]!).toUInt32
      let c3 := (ids[(kids[(4 * k + 2).toNat]! + 1).toNat]!).toUInt32
      let c4 := (ids[(kids[(4 * k + 3).toNat]! + 1).toNat]!).toUInt32
      let r := w.addEntry entries[k.toNat]! c1 c2 c3 c4
      let enc := encodeDagWriter jh r.2
      let newIds := Algorithm.U64Buf.push ids r.1.toUInt64
      let hp' := { hp with u64Arrays := hp.u64Arrays ++ [newIds] }
      have hext1 : HeapExtends jh enc.2 := encodeDagWriter_heapExtends jh r.2
      have hEnt1 : enc.2.get? entriesAddr = some (.objArray clsE eElems) := by
        rw [hext1.2 _ hextEnt, hEnt]
      have hKids1 : enc.2.get? kidsAddr = some (.intArray kids) := by
        rw [hext1.2 _ hextKids, hKids]
      have hIds1' : hp'.u64Arrays[hp.u64Arrays.length]? = some newIds := by
        simp [hp']
      have hw1 : decodeDagWriter enc.2 enc.1 = some r.2 := decodeDagWriter_encode jh r.2
      obtain ⟨nextWAddr, _, hEncFst, _⟩ := encodeDagWriter_fst_spec jh r.2
      have hPushInv := u64Buf_push_inv ids r.1.toUInt64 k hk29 hIds1 hIds2 hIds0 hIdsK
      have hm1 : n.toNat - (k + 1).toNat = m := by omega
      obtain ⟨locs', hstep, hl0', hl1', hl2', hl3', hl4', hl5'⟩ :=
        writeDag_body_step hl0 hl1 hl2 hl3 hl4 hl5 hEnt hESz hEElem
          hKids hIds hw hkn hnBound hnEnt hnKids
      rw [hEncFst] at hl5'
      rw [hEncFst] at hw1
      obtain ⟨fNext, wVal', locs'', jh', hp'', hrun, hext2, hdec'⟩ :=
        ih hm1 hl0' hl1' hl2' hl3' hl4' hl5' hEnt1 hESz hEElem hKids1 hIds1' hw1
          hnBound hnEnt hnKids hPushInv.1 hPushInv.2.1 hPushInv.2.2.1 hPushInv.2.2.2
      refine ⟨fNext + 106, wVal', locs'', jh', hp'', ?_, HeapExtends_trans hext1 hext2, ?_⟩
      · change runJvmResFast (fNext + 106) progWD 9 (progWD.drop 9) ⟨9, [], locs, jh, hp⟩ = _
        rw [hstep fNext]
        exact hrun
      · rw [Algorithm.writeDag.eq_1]
        simp only [hkn, ↓reduceDIte]
        exact hdec'
    · have hbr : (if k == n then (0 : UInt32) else if k < n then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hkn
      refine ⟨6, .heapRef wAddr, locs, jh, hp, ?_, HeapExtends_refl jh, ?_⟩
      · step_drop_at 6
        rw [show (6 : Nat) = 5 + 1 from rfl]; step1_load 2 (.i32 k), hl2
        rw [show (5 : Nat) = 4 + 1 from rfl]; step1_load 3 (.i32 n), hl3
        rw [show (4 : Nat) = 3 + 1 from rfl]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
        rw [show (3 : Nat) = 2 + 1 from rfl]
        rw [runJvmResFast_iflt_fallthrough hbr]
        rw [show (2 : Nat) = 1 + 1 from rfl]; step1_load 5 (.heapRef wAddr), hl5
        exact runJvmResFast_areturn
      · rw [Algorithm.writeDag.eq_1]; simp [hkn, hw]

theorem writeDag_equiv
    {entriesAddr kidsAddr idsId wAddr : Nat} {k n : UInt32}
    {clsE : String} {eElems : Array JvmVal} {entries : Array Algorithm.MacroCell}
    {kids : Array UInt32} {ids : Array UInt64} {w : Algorithm.DagWriter}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hEnt : jh.get? entriesAddr = some (.objArray clsE eElems))
    (hESz : eElems.size = entries.size)
    (hEElem : ∀ (i : Nat) (hi : i < entries.size), eElems[i]'(hESz.symm ▸ hi) = .ext (.mc entries[i]))
    (hKids : jh.get? kidsAddr = some (.intArray kids))
    (hIds : hp.u64Arrays[idsId]? = some ids)
    (hw : decodeDagWriter jh (.heapRef wAddr) = some w)
    (hnBound : n.toNat < 2 ^ 29)
    (hnEnt : n.toNat ≤ entries.size)
    (hnKids : 4 * n.toNat ≤ kids.size)
    (hIds1 : 0 < ids.size) (hIds2 : ids.size < 2 ^ 31)
    (hIds0 : ids[0]!.toUInt32 = k) (hIdsK : k.toNat < ids.size)
    (hl0 : locs 0 = .heapRef entriesAddr) (hl1 : locs 1 = .heapRef kidsAddr)
    (hl2 : locs 2 = .i32 k) (hl3 : locs 3 = .i32 n)
    (hl4 : locs 4 = .ext (.u64Ref idsId)) (hl5 : locs 5 = .heapRef wAddr) :
    ∃ f' wVal' st',
      runJvmRes f' f_Algorithm_writeDag_prog ⟨0, [], locs, jh, hp⟩ = some (wVal', st') ∧
      HeapExtends jh st'.jvmHeap ∧
      decodeDagWriter st'.jvmHeap wVal' = some (Algorithm.writeDag entries kids k n ids w) := by
  obtain ⟨fLoop, wVal', locs', jh', hp', hLoop, hext, hdec⟩ :=
    runJvmResFast_writeDag_loop (n.toNat - k.toNat) rfl hl0 hl1 hl2 hl3 hl4 hl5
      hEnt hESz hEElem hKids hIds hw hnBound hnEnt hnKids hIds1 hIds2 hIds0 hIdsK
  refine ⟨fLoop + 9, wVal', ⟨14, [wVal'], locs', jh', hp'⟩, ?_, hext, hdec⟩
  apply runJvmRes_of_runJvmResFast0 (fLoop + 9) progWD _ _ rfl
  change runJvmResFast (fLoop + 9) progWD 0 (progWD.drop 0) ⟨0, [], locs, jh, hp⟩ = _
  step_drop_at 9
  rw [show fLoop + 9 = (fLoop + 8) + 1 from by omega]
  step1_load 0 (.heapRef entriesAddr), hl0
  rw [show fLoop + 8 = (fLoop + 7) + 1 from by omega]; step1
  rw [show fLoop + 7 = (fLoop + 6) + 1 from by omega]
  rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
  rw [show fLoop + 6 = (fLoop + 5) + 1 from by omega]
  step1_load 1 (.heapRef kidsAddr), hl1
  rw [show fLoop + 5 = (fLoop + 4) + 1 from by omega]; step1
  rw [show fLoop + 4 = (fLoop + 3) + 1 from by omega]
  rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
  rw [show fLoop + 3 = (fLoop + 2) + 1 from by omega]
  step1_load 4 (.ext (.u64Ref idsId)), hl4
  rw [show fLoop + 2 = (fLoop + 1) + 1 from by omega]; step1
  rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
  exact hLoop

private theorem serializeMacrocellDag_none_finish
    {f pc : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (w' : Algorithm.DagWriter)
    (hdrop : progSMD.drop pc =
      .astore 12 :: .aload 12 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 12 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .invokestatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
      .areturn :: List.drop (pc + 10) progSMD) :
    ∃ st',
      runJvmResFast (f + 10) progSMD pc (progSMD.drop pc)
        ⟨pc, (encodeDagWriter jh w').1 :: [], locs, (encodeDagWriter jh w').2, hp⟩ =
        some (.strArr w'.lines.toArray, st') ∧
      decodeStrArray st' (.strArr w'.lines.toArray) = some w'.lines.toArray := by
  obtain ⟨wOutAddr, wOutElems, hwFst, hwGet, hwSz, hwElem1⟩ :=
    encodeDagWriter_fst_spec jh w'
  have hrun : ∃ locs',
      runJvmResFast (f + 10) progSMD pc (progSMD.drop pc)
        ⟨pc, (encodeDagWriter jh w').1 :: [], locs, (encodeDagWriter jh w').2, hp⟩ =
        some (.strArr w'.lines.toArray,
          ⟨pc + 9, [.strArr w'.lines.toArray], locs', (encodeDagWriter jh w').2, hp⟩) := by
    apply Exists.intro
    rw [hdrop, hwFst]
    rw [show f + 10 = (f + 9) + 1 from by omega]; step1
    rw [show f + 9 = (f + 8) + 1 from by omega]
    step1_load 12 (.heapRef wOutAddr), (by simp [setLocal])
    rw [show f + 8 = (f + 7) + 1 from by omega]; step1
    rw [show f + 7 = (f + 6) + 1 from by omega]
    rw [runJvmResFast_checkNotNull (by intro h; cases h)]
    rw [show f + 6 = (f + 5) + 1 from by omega]
    step1_load 12 (.heapRef wOutAddr), (by simp [setLocal])
    rw [show f + 5 = (f + 4) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray_any hwGet]
    rw [show f + 4 = (f + 3) + 1 from by omega]; step1
    rw [show f + 3 = (f + 2) + 1 from by omega]
    rw [runJvmResFast_aaload_elem (idx := 1) hwGet (by decide) (by simpa using hwElem1)]
    rw [show f + 2 = (f + 1) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_str]
    exact runJvmResFast_areturn
  obtain ⟨locs', hrun⟩ := hrun
  exact ⟨_, hrun, rfl⟩

theorem serializeMacrocellDag_equiv
    {entriesAddr kidsAddr : Nat} {clsE : String} {eElems : Array JvmVal}
    {entries : Array Algorithm.MacroCell} {kids : Array UInt32}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .heapRef entriesAddr) (hl1 : locs 1 = .heapRef kidsAddr)
    (hEnt : jh.get? entriesAddr = some (.objArray clsE eElems))
    (hESz : eElems.size = entries.size)
    (hEElem : ∀ (i : Nat) (hi : i < entries.size), eElems[i]'(hESz.symm ▸ hi) = .ext (.mc entries[i]))
    (hKids : jh.get? kidsAddr = some (.intArray kids))
    (hNonempty : 0 < entries.size) (hBound : entries.size < 2 ^ 29) :
    ∃ f' ret st',
      runJvmRes f' f_Algorithm_serializeMacrocellDag_prog ⟨0, [], locs, jh, hp⟩ = some (ret, st') ∧
      decodeStrArray st' ret = some (Algorithm.serializeMacrocellDag entries kids) := by
  let n : UInt32 := entries.size.toUInt32
  have hnNat : n.toNat = entries.size := by
    change (UInt32.ofNat entries.size).toNat = entries.size
    exact UInt32.toNat_ofNat_of_lt (Nat.lt_trans hBound (by decide))
  have hle1 : (1 : UInt32) ≤ n :=
    UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_one, hnNat]; omega)
  have hnm1Nat : (n - 1).toNat = entries.size - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ hle1, UInt32.toNat_one, hnNat]
  have hnm1Slt : (n - 1).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hLastEnt : (n - 1).toNat < entries.size := by omega
  have hLastElems : (n - 1).toNat < eElems.size := by omega
  have hLastEq : eElems[(n - 1).toNat] = .ext (.mc entries[entries.size - 1]!) := by
    rw [getElem!_pos entries (entries.size - 1) (by omega)]
    simpa [hnm1Nat] using hEElem (entries.size - 1) (by omega)
  cases hSL : Algorithm.macrocellSingleLeaf entries[entries.size - 1]! with
  | some leaf =>
    let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
    let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"])).2
    let jh3 := (jh2.alloc (.objArray "java/lang/Object"
      #[.str "[M2] (ComposeLife 1.0)", .null])).2
    let closedAddr := jh1.objects.size
    let resAddr := jh2.objects.size
    have hClosedSz : jh2.get? closedAddr =
        some (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"]) :=
      jvmHeap_get?_alloc_self jh1 _
    have hResGet : jh3.get? resAddr =
        some (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)", .null]) :=
      jvmHeap_get?_alloc_self jh2 _
    have hClosedSz3 : jh3.get? closedAddr =
        some (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"]) := by
      have hlt : closedAddr < jh2.objects.size := by simp [closedAddr, jh2, Jvm.JvmHeap.alloc]
      rw [jvmHeap_get?_alloc_lt _ _ hlt, hClosedSz]
    let jh4 := jh3.set resAddr (.objArray "java/lang/Object"
      ((#[.str "[M2] (ComposeLife 1.0)", .null]).set (UInt32.toNat 1)
        (.str (Algorithm.formatLeafNode leaf)) (by decide)))
    have hResGet4 : jh4.get? resAddr = some (.objArray "java/lang/Object"
        #[.str "[M2] (ComposeLife 1.0)", .str (Algorithm.formatLeafNode leaf)]) := by
      simpa [jh4, resAddr] using jvmHeap_get?_set_self hResGet
    have hrun : ∀ (f : Nat), ∃ pc' locs', runJvmRes (f + 62) progSMD ⟨0, [], locs, jh, hp⟩ =
        some (.heapRef resAddr, ⟨pc', [.heapRef resAddr], locs', jh4, hp⟩) := by
      intro f
      apply Exists.intro
      apply Exists.intro
      apply runJvmRes_of_runJvmResFast0 (f + 62) progSMD _ _ rfl
      change runJvmResFast (f + 62) progSMD 0 (progSMD.drop 0) ⟨0, [], locs, jh, hp⟩ = _
      step_drop_at 12
      step1_load 0 (.heapRef entriesAddr), hl0
      step1
      rw [show f + 60 = (f + 59) + 1 from by omega]
      rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
      step1_load 1 (.heapRef kidsAddr), hl1
      step1
      rw [show f + 57 = (f + 56) + 1 from by omega]
      rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
      step1_load 0 (.heapRef entriesAddr), hl0
      rw [show f + 55 = (f + 54) + 1 from by omega]
      rw [runJvmResFast_arraylength_obj hEnt]
      rw [show UInt32.ofNat eElems.size = n by simp [n, hESz]]
      rw [show f + 54 = (f + 53) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      step1
      step1_load 0 (.heapRef entriesAddr), (by simp [setLocal, hl0])
      step1_load 2 (.i32 n), (by simp [setLocal])
      step_drop_at 12
      step1; step1
      rw [show f + 48 = (f + 47) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      rw [show f + 47 = (f + 46) + 1 from by omega]
      rw [runJvmResFast_aaload_elem hEnt hnm1Slt (getElem?_pos eElems (n - 1).toNat hLastElems)]
      rw [hLastEq]
      step1; step1
      rw [show f + 44 = (f + 43) + 1 from by omega]
      rw [runJvmResFast_checkNotNull (by intro h; cases h)]
      rw [show f + 43 = (f + 42) + 1 from by omega]
      rw [runJvmResFast_checkcast_step rfl]
      rw [show f + 42 = (f + 41) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_macrocellSingleLeaf]
      rw [hSL]
      dsimp only
      step1
      step1_load 3 (.boxedULong leaf), (by simp [setLocal])
      rw [show f + 39 = (f + 38) + 1 from by omega]
      rw [runJvmResFast_ifnonnull_branch (by simp [Jvm.JvmVal.isNull])]
      step_drop_at 12
      step1_load 3 (.boxedULong leaf), (by simp [setLocal])
      step1; step1; step1
      step1_load 5 (.boxedULong leaf), (by simp [setLocal])
      rw [show f + 33 = (f + 32) + 1 from by omega]
      rw [runJvmResFast_instanceof_boxedULong_long]
      rw [show f + 32 = (f + 31) + 1 from by omega]
      rw [runJvmResFast_ifeq_branch rfl]
      step_drop_at 14
      step1_load 5 (.boxedULong leaf), (by simp [setLocal])
      rw [show f + 30 = (f + 29) + 1 from by omega]
      rw [runJvmResFast_invokevirtual_step stepVirtual_ulong_unbox]
      rw [show f + 29 = (f + 28) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_formatLeafNode_5b]
      step1; step1
      rw [show f + 26 = (f + 25) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj (by decide)]
      step1
      rw [show Array.replicate (UInt32.toNat 0) (Jvm.JvmVal.null : JvmVal) = #[] from rfl]
      rw [show f + 24 = (f + 23) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_serializeMacrocell___closed__2_5b]
      step1
      rw [show (jh.alloc (.objArray "java/lang/Object" #[])).snd = jh1 from rfl]
      rw [show (jh1.alloc (.objArray "java/lang/Object" #[.str "[M2] (ComposeLife 1.0)"])).snd = jh2
        from rfl]
      step1_load 6 (.heapRef closedAddr), (by dsimp only [closedAddr, jh1]; simp [setLocal])
      step1_load 6 (.heapRef closedAddr), (by dsimp only [closedAddr, jh1]; simp [setLocal])
      rw [show f + 20 = (f + 19) + 1 from by omega]
      rw [runJvmResFast_arraylength_obj hClosedSz]
      step_drop_at 16
      step1; step1
      rw [show (UInt32.ofNat (#[Jvm.JvmVal.str "[M2] (ComposeLife 1.0)"]).size + 1) = 2 by rfl]
      rw [show f + 17 = (f + 16) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (newLen := 2) (by decide) hClosedSz)]
      step1; step1
      rw [show f + 14 = (f + 13) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullExpressionValue_5b rfl)]
      step1
      rw [show (Array.ofFn (n := (2 : UInt32).toNat) fun i =>
          if h : (i : Nat) < (#[Jvm.JvmVal.str "[M2] (ComposeLife 1.0)"] : Array JvmVal).size then
            (#[Jvm.JvmVal.str "[M2] (ComposeLife 1.0)"] : Array JvmVal)[(i : Nat)] else .null) =
          #[.str "[M2] (ComposeLife 1.0)", .null] from rfl]
      rw [show (jh2.alloc (.objArray "java/lang/Object"
        #[.str "[M2] (ComposeLife 1.0)", .null])).snd = jh3 from rfl]
      step1_load 7 (.heapRef resAddr), (by dsimp only [resAddr, jh2]; simp [setLocal])
      step1; step1; step1
      step1_load 8 (.heapRef resAddr), (by dsimp only [resAddr, jh2]; simp [setLocal])
      step1_load 6 (.heapRef closedAddr), (by dsimp only [closedAddr, jh1]; simp [setLocal])
      rw [show f + 6 = (f + 5) + 1 from by omega]
      rw [runJvmResFast_arraylength_obj hClosedSz3]
      step1_load 4 (.str (Algorithm.formatLeafNode leaf)), (by simp [setLocal])
      have hArrLen1 :
          UInt32.ofNat (#[(JvmVal.str "[M2] (ComposeLife 1.0)")] : Array JvmVal).size = 1 := rfl
      rw [hArrLen1]
      rw [show f + 4 = (f + 3) + 1 from by omega]
      rw [runJvmResFast_aastore hResGet (by decide) (by decide)]
      step1_load 7 (.heapRef resAddr), (by dsimp only [resAddr, jh2]; simp [setLocal])
      rw [show f + 2 = (f + 1) + 1 from by omega]
      exact runJvmResFast_areturn
    obtain ⟨pc', locs', hrun⟩ := hrun 0
    refine ⟨0 + 62, .heapRef resAddr, _, hrun, ?_⟩
    simp only [Algorithm.serializeMacrocellDag, Algorithm.macrocellHeader]
    rw [show (entries.size.toUInt32 - 1).toNat = entries.size - 1 from hnm1Nat, hSL]
    simp [decodeStrArray, hResGet4]
  | none =>
    have hCapSlt : (4 * n + 1).toBitVec.slt 0#32 = false := by
      apply u32_slt_zero_of_lt_2_31
      rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
        UInt32.toNat_one, hnNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    let b0 := Algorithm.GrowBuf.empty.push Algorithm.macrocellHeader
    let capNat := (4 * n + 1).toNat
    let jh1 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate capNat .null))).2
    let lAddr := jh.objects.size
    let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
    let emptyL := jh1.objects.size
    let lArr : Array JvmVal :=
      Array.ofFn (n := (Array.replicate capNat (JvmVal.null : JvmVal)).size)
        fun _ => Jvm.JvmVal.heapRef emptyL
    let jh3 := jh2.set lAddr (.objArray "java/lang/Object" lArr)
    let jh4 := (jh3.alloc (.objArray "java/lang/Object" (Array.replicate capNat .null))).2
    let nAddr := jh3.objects.size
    let jh5 := (jh4.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
    let emptyN := jh4.objects.size
    let nArr : Array JvmVal :=
      Array.ofFn (n := (Array.replicate capNat (JvmVal.null : JvmVal)).size)
        fun _ => Jvm.JvmVal.heapRef emptyN
    let jh6 := jh5.set nAddr (.objArray "java/lang/Object" nArr)
    let jh7 := (jh6.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .ext (.strGrowBuf b0), .heapRef lAddr, .heapRef nAddr])).2
    let wAddr := jh6.objects.size
    have hgetL2 : jh2.get? lAddr = some (.objArray "java/lang/Object" (Array.replicate capNat .null)) := by
      rw [jvmHeap_get?_alloc_lt _ _ (by simp [lAddr, jh1, Jvm.JvmHeap.alloc])]
      exact jvmHeap_get?_alloc_self _ _
    have hgetN5 : jh5.get? nAddr = some (.objArray "java/lang/Object" (Array.replicate capNat .null)) := by
      rw [jvmHeap_get?_alloc_lt _ _ (by simp [nAddr, jh4, Jvm.JvmHeap.alloc])]
      exact jvmHeap_get?_alloc_self _ _
    have hgetL3 : jh3.get? lAddr = some (.objArray "java/lang/Object" lArr) := by
      simpa [jh3, lAddr] using jvmHeap_get?_set_self hgetL2
    have hgetEL3 : jh3.get? emptyL = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
      rw [jvmHeap_get?_set_ne _ _ (by simp [emptyL, lAddr, jh1, Jvm.JvmHeap.alloc])]
      exact jvmHeap_get?_alloc_self _ _
    have hgetN6 : jh6.get? nAddr = some (.objArray "java/lang/Object" nArr) := by
      simpa [jh6, nAddr] using jvmHeap_get?_set_self hgetN5
    have hgetEN6 : jh6.get? emptyN = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
      rw [jvmHeap_get?_set_ne _ _ (by simp [emptyN, nAddr, jh4, Jvm.JvmHeap.alloc])]
      exact jvmHeap_get?_alloc_self _ _
    have hext36 : HeapExtends jh3 jh6 :=
      HeapExtends_set_of_ge (HeapExtends_trans (HeapExtends_alloc _ _) (HeapExtends_alloc _ _)) (Nat.le_refl _)
    have hext03 : HeapExtends jh jh3 :=
      HeapExtends_set_of_ge (HeapExtends_trans (HeapExtends_alloc _ _) (HeapExtends_alloc _ _)) (Nat.le_refl _)
    have hext07 : HeapExtends jh jh7 :=
      HeapExtends_trans hext03 (HeapExtends_trans hext36 (HeapExtends_alloc _ _))
    have hgetW7 : jh7.get? wAddr = some (.objArray "java/lang/Object"
        #[.boxedInt 0, .ext (.strGrowBuf b0), .heapRef lAddr, .heapRef nAddr]) :=
      jvmHeap_get?_alloc_self _ _
    have hgetL7 : jh7.get? lAddr = some (.objArray "java/lang/Object" lArr) := by
      have hlt : lAddr < jh3.objects.size := jvmHeap_addr_lt_of_get? hgetL3
      rw [jvmHeap_get?_alloc_lt _ _ (Nat.lt_of_lt_of_le hlt hext36.1), hext36.2 _ hlt, hgetL3]
    have hgetEL7 : jh7.get? emptyL = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
      have hlt : emptyL < jh3.objects.size := jvmHeap_addr_lt_of_get? hgetEL3
      rw [jvmHeap_get?_alloc_lt _ _ (Nat.lt_of_lt_of_le hlt hext36.1), hext36.2 _ hlt, hgetEL3]
    have hgetN7 : jh7.get? nAddr = some (.objArray "java/lang/Object" nArr) := by
      have hlt : nAddr < jh6.objects.size := jvmHeap_addr_lt_of_get? hgetN6
      rw [jvmHeap_get?_alloc_lt _ _ hlt, hgetN6]
    have hgetEN7 : jh7.get? emptyN = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
      have hlt : emptyN < jh6.objects.size := jvmHeap_addr_lt_of_get? hgetEN6
      rw [jvmHeap_get?_alloc_lt _ _ hlt, hgetEN6]
    have hwInit : decodeDagWriter jh7 (.heapRef wAddr) =
        some ⟨b0, Array.replicate capNat [], Array.replicate capNat []⟩ :=
      decodeDagWriter_init jh7 b0 capNat lAddr emptyL nAddr emptyN wAddr lArr nArr
        (by simp [lArr, Array.size_ofFn, Array.size_replicate])
        (fun i hi => by simp [lArr])
        (by simp [nArr, Array.size_ofFn, Array.size_replicate])
        (fun i hi => by simp [nArr])
        hgetW7 hgetL7 hgetN7 hgetEL7 hgetEN7
    have hEnt7 : jh7.get? entriesAddr = some (.objArray clsE eElems) := by
      rw [hext07.2 _ (jvmHeap_addr_lt_of_get? hEnt), hEnt]
    have hKids7 : jh7.get? kidsAddr = some (.intArray kids) := by
      rw [hext07.2 _ (jvmHeap_addr_lt_of_get? hKids), hKids]
    let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
    have hIds7 : hp1.u64Arrays[hp.u64Arrays.length]? = some Algorithm.U64Buf.empty := by
      simp [hp1]
    have hFoldEnt : eElems.foldlM
        (fun acc v => match v with | .ext (.mc m) => some (acc.push m) | _ => none) #[] =
        some entries := by
      have hStepFn :
          (fun (acc : Array Algorithm.MacroCell) (v : JvmVal) =>
            match v with | .ext (.mc m) => some (acc.push m) | _ => none) =
          (fun acc v => (match v with | .ext (.mc m) => some m | _ => none).map acc.push) := by
        funext acc v
        cases v with
        | ext e => cases e <;> rfl
        | _ => rfl
      rw [hStepFn]
      apply foldlM_array_eq_some_of_forall _ eElems entries hESz
      intro i hi
      rw [hEElem i (hESz ▸ hi)]
    let w0 : Algorithm.DagWriter := ⟨b0, Array.replicate capNat [], Array.replicate capNat []⟩
    let w' := Algorithm.writeDag entries kids 0 n Algorithm.U64Buf.empty w0
    have hPre : ∀ (f : Nat), ∃ locs120,
        runJvmResFast (f + 130) progSMD 0 (progSMD.drop 0) ⟨0, [], locs, jh, hp⟩ =
          runJvmResFast (f + 10) progSMD 120 (progSMD.drop 120)
            ⟨120, (encodeDagWriter jh7 w').1 :: [], locs120,
              (encodeDagWriter jh7 w').2, hp1⟩ := by
      intro f
      apply Exists.intro
      step_drop_at 12
      step1_load 0 (.heapRef entriesAddr), hl0
      step1
      rw [show f + 128 = (f + 127) + 1 from by omega]
      rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
      step1_load 1 (.heapRef kidsAddr), hl1
      step1
      rw [show f + 125 = (f + 124) + 1 from by omega]
      rw [runJvmResFast_checkNotNullParameter (by simp [Jvm.JvmVal.isNull])]
      step1_load 0 (.heapRef entriesAddr), hl0
      rw [show f + 123 = (f + 122) + 1 from by omega]
      rw [runJvmResFast_arraylength_obj hEnt]
      rw [show UInt32.ofNat eElems.size = n by simp [n, hESz]]
      rw [show f + 122 = (f + 121) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      step1
      step1_load 0 (.heapRef entriesAddr), (by simp [setLocal, hl0])
      step1_load 2 (.i32 n), (by simp [setLocal])
      step_drop_at 12
      step1; step1
      rw [show f + 116 = (f + 115) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      rw [show f + 115 = (f + 114) + 1 from by omega]
      rw [runJvmResFast_aaload_elem hEnt hnm1Slt (getElem?_pos eElems (n - 1).toNat hLastElems)]
      rw [hLastEq]
      step1; step1
      rw [show f + 112 = (f + 111) + 1 from by omega]
      rw [runJvmResFast_checkNotNull (by intro h; cases h)]
      rw [show f + 111 = (f + 110) + 1 from by omega]
      rw [runJvmResFast_checkcast_step rfl]
      rw [show f + 110 = (f + 109) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_macrocellSingleLeaf]
      rw [hSL]
      dsimp only
      step1
      step1_load 3 .null, (by simp [setLocal])
      rw [show f + 107 = (f + 106) + 1 from by omega]
      rw [runJvmResFast_ifnonnull_fallthrough]
      step_drop_at 17
      step1_load 2 (.i32 n), (by simp [setLocal])
      step1; step1
      rw [u32_shl2_eq_mul4 n]
      rw [show f + 103 = (f + 102) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      step1; step1
      rw [show f + 100 = (f + 99) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u32_constructor]
      step1; step1
      rw [show f + 97 = (f + 96) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_growBufEmpty_5b]
      step1; step1; step1
      step1_load 5 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)), (by simp [setLocal])
      step1_load 6 (.str "[M2] (ComposeLife 1.0)"), (by simp [setLocal])
      rw [show f + 91 = (f + 90) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_growBufPush_str]
      step1
      step_drop_at 16
      step1_load 4 (.i32 (4 * n + 1)), (by simp [setLocal])
      rw [show f + 88 = (f + 87) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj hCapSlt]
      step1
      step1_load 9 (.heapRef lAddr), (by dsimp only [lAddr]; simp [setLocal])
      step1; step1; step1
      step1_load 10 (.heapRef lAddr), (by dsimp only [lAddr]; simp [setLocal])
      step1
      rw [show f + 80 = (f + 79) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj (by decide)]
      step1
      step1_load 12 (.heapRef emptyL), (by dsimp only [emptyL, jh1, capNat]; simp [setLocal])
      step1; step1
      rw [show f + 75 = (f + 74) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
      rw [show f + 74 = (f + 73) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 0) (jvmHeap_get?_alloc_self jh1 _) (by decide) (by decide)]
      rw [alloc_obj1_set]
      step_drop_at 8
      step1_load 12 (.heapRef emptyL), (by dsimp only [emptyL, jh1, capNat]; simp [setLocal])
      step1; step1; step1; step1
      rw [show f + 68 = (f + 67) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step (stepStatic_arraysFillAll_5b hgetL2)]
      step1_load 9 (.heapRef lAddr), (by dsimp only [lAddr]; simp [setLocal])
      step1
      step_drop_at 16
      step1_load 4 (.i32 (4 * n + 1)), (by simp [setLocal])
      rw [show f + 64 = (f + 63) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj hCapSlt]
      step1
      step1_load 10 (.heapRef nAddr), (by dsimp only [nAddr, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      step1; step1; step1
      step1_load 11 (.heapRef nAddr), (by dsimp only [nAddr, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      step1
      rw [show f + 56 = (f + 55) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj (by decide)]
      step1
      step1_load 13 (.heapRef emptyN),
        (by dsimp only [emptyN, jh4, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      step1; step1
      rw [show f + 51 = (f + 50) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
      rw [show f + 50 = (f + 49) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 0) (jvmHeap_get?_alloc_self jh4 _) (by decide) (by decide)]
      rw [alloc_obj1_set]
      step_drop_at 8
      step1_load 13 (.heapRef emptyN),
        (by dsimp only [emptyN, jh4, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      step1; step1; step1; step1
      rw [show f + 44 = (f + 43) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step (stepStatic_arraysFillAll_5b hgetN5)]
      step1_load 10 (.heapRef nAddr), (by dsimp only [nAddr, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      step1
      step_drop_at 22
      step1
      rw [show f + 40 = (f + 39) + 1 from by omega]
      rw [runJvmResFast_anewarray_obj (by decide)]
      step1
      step1_load 11 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      step1; step1
      rw [show f + 35 = (f + 34) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intValueOf]
      have hgetW0 : ((jh6.alloc (.objArray "java/lang/Object"
          (Array.replicate (UInt32.toNat 4) .null))).2).get? wAddr =
          some (.objArray "java/lang/Object" (Array.replicate (UInt32.toNat 4) .null)) :=
        jvmHeap_get?_alloc_self _ _
      rw [show f + 34 = (f + 33) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 0) hgetW0 (by decide) (by decide)]
      step1_load 11 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      step1
      step1_load 7 (.ext (.strGrowBuf b0)),
        (by dsimp only [b0, Algorithm.macrocellHeader]; simp [setLocal])
      have hgetW1 := jvmHeap_get?_set_self hgetW0 (w := .objArray "java/lang/Object"
        ((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) (.boxedInt 0) (by decide)))
      rw [show f + 30 = (f + 29) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 1) hgetW1 (by decide) (by decide)]
      step1_load 11 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      step1
      step1_load 8 (.heapRef lAddr), (by dsimp only [lAddr]; simp [setLocal])
      have hgetW2 := jvmHeap_get?_set_self hgetW1 (w := .objArray "java/lang/Object"
        (((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) (.boxedInt 0) (by decide)).set
          (UInt32.toNat 1) (.ext (.strGrowBuf b0)) (by simp [Array.size_set])))
      rw [show f + 26 = (f + 25) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 2) hgetW2 (by decide) (by decide)]
      step1_load 11 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      step1
      step1_load 9 (.heapRef nAddr), (by dsimp only [nAddr, jh3, jh2, jh1, lArr, capNat]; simp [setLocal])
      have hgetW3 := jvmHeap_get?_set_self hgetW2 (w := .objArray "java/lang/Object"
        ((((Array.replicate (UInt32.toNat 4) .null).set (UInt32.toNat 0) (.boxedInt 0) (by decide)).set
          (UInt32.toNat 1) (.ext (.strGrowBuf b0)) (by simp [Array.size_set])).set
          (UInt32.toNat 2) (.heapRef lAddr) (by simp [Array.size_set])))
      rw [show f + 22 = (f + 21) + 1 from by omega]
      rw [runJvmResFast_aastore (idx := 3) hgetW3 (by decide) (by simp [Array.size_set])]
      rw [alloc_obj4_set]
      step1_load 11 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      step1
      step_drop_at 9
      rw [show f + 19 = (f + 18) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_u64BufEmpty_5b]
      step1
      step1_load 0 (.heapRef entriesAddr), (by simp [setLocal, hl0])
      step1_load 1 (.heapRef kidsAddr), (by simp [setLocal, hl1])
      step1
      step1_load 2 (.i32 n), (by simp [setLocal])
      step1_load 11 (.ext (.u64Ref hp.u64Arrays.length)), (by simp [setLocal])
      step1_load 10 (.heapRef wAddr),
        (by dsimp only [wAddr, jh6, jh5, jh4, jh3, jh2, jh1, lArr, nArr, capNat]; simp [setLocal])
      rw [show f + 11 = (f + 10) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step (stepStatic_writeDag_heap hEnt7 hKids7 hIds7 hFoldEnt hwInit)]
    obtain ⟨locs120, hStep120⟩ := hPre 0
    obtain ⟨st', hFin, hDecOut⟩ := serializeMacrocellDag_none_finish (f := 0) (pc := 120)
      (locs := locs120) (jh := jh7) (hp := hp1) w' rfl
    refine ⟨0 + 130, .strArr w'.lines.toArray, st', ?_, ?_⟩
    · apply runJvmRes_of_runJvmResFast0 (0 + 130) progSMD _ _ rfl
      change runJvmResFast (0 + 130) progSMD 0 (progSMD.drop 0) ⟨0, [], locs, jh, hp⟩ = _
      rw [hStep120]
      exact hFin
    · rw [Algorithm.serializeMacrocellDag]
      simp only [Algorithm.macrocellHeader]
      rw [show (entries.size.toUInt32 - 1).toNat = entries.size - 1 from hnm1Nat, hSL]
      exact hDecOut

end Algorithm.JvmVerification
