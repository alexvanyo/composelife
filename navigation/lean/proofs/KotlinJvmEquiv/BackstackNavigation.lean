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

import Jvm.Proofs
import Jvm.Tactics
import KotlinJvmBytecode

namespace Navigation.KotlinJvmVerification

open Navigation.JvmVerification
open Navigation.KotlinJvmBytecode
open Navigation.Model

/-! ### Program Lookup Table and Hooks -/

/-- Bytecode lookup table for all `BackstackNavigationKt` methods and lambdas. -/
def navProgLookup (fnTag : String) : Option (List JvmInstr) :=
  match fnTag with
  | "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_popUpTo_prog
  | "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_popUpTo_1_prog
  | "BackstackNavigationKt.popUpToValue:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_popUpToValue_prog
  | "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_navigate_prog
  | "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_navigate_1_prog
  | "BackstackNavigationKt.popBackstack:(Ljava/util/Map;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =>
    some BackstackNavigationKt_popBackstack_prog
  | "BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =>
    some BackstackNavigationKt_popUpTo_lambda_2_prog
  | "BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =>
    some BackstackNavigationKt_popUpTo_lambda_3_prog
  | "BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;" =>
    some BackstackNavigationKt_navigate_lambda_0_prog
  | _ => none

def ExtendsNavProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ fnTag prog, navProgLookup fnTag = some prog → resolveProg fnTag = some prog

theorem navProgLookup_extends : ExtendsNavProgs navProgLookup :=
  fun _ _ h => h

section ProgAndBsmLemmas
set_option maxRecDepth 4096

private theorem navProgLookup_popUpTo :
    navProgLookup
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_prog := rfl

private theorem navProgLookup_popUpTo1 :
    navProgLookup
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_1_prog := rfl

private theorem navProgLookup_popUpToValue :
    navProgLookup
      "BackstackNavigationKt.popUpToValue:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpToValue_prog := rfl

private theorem navProgLookup_navigate :
    navProgLookup
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_navigate_prog := rfl

private theorem navProgLookup_navigate1 :
    navProgLookup
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_navigate_1_prog := rfl

private theorem navProgLookup_lambda2 :
    navProgLookup
      "BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some BackstackNavigationKt_popUpTo_lambda_2_prog := rfl

private theorem navProgLookup_lambda3 :
    navProgLookup
      "BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some BackstackNavigationKt_popUpTo_lambda_3_prog := rfl

private theorem navProgLookup_lambda0 :
    navProgLookup
      "BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;" =
      some BackstackNavigationKt_navigate_lambda_0_prog := rfl

private theorem bsm_lambda0 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;" =
      some ("BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;", false) := by decide

private theorem bsm_lambda2 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some ("BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z", true) := by decide

private theorem bsm_lambda3 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some ("BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z", true) := by decide

private theorem tags_obj_len1 :
    (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Lkotlin/jvm/functions/Function1;").length = 1 := by decide

private theorem tags_uuid_len1 :
    (Jvm.parseMethodParamTags "(Lkotlin/uuid/Uuid;)Lkotlin/jvm/functions/Function1;").length = 1 := by decide

private theorem tags_fn1_len1 :
    (Jvm.parseMethodParamTags "(Lkotlin/jvm/functions/Function1;)Lkotlin/jvm/functions/Function1;").length = 1 := by decide

private theorem ptags_nav :
    Jvm.parseMethodParamTags
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      ['L', 'L', 'L', 'L'] := by decide

private theorem ptags_nav1 :
    Jvm.parseMethodParamTags
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      ['L', 'L', 'L', 'L'] := by decide

private theorem ptags_popUpTo :
    Jvm.parseMethodParamTags
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      ['L', 'L', 'L', 'Z'] := by decide

private theorem ptags_popUpTo1 :
    Jvm.parseMethodParamTags
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;" =
      ['L', 'L', 'L', 'Z'] := by decide

private theorem fntag_nav :
    ("BackstackNavigationKt" ++ "." ++ "navigate" ++ ":" ++
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;") =
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" := by decide

private theorem fntag_nav1 :
    ("BackstackNavigationKt" ++ "." ++ "navigate" ++ ":" ++
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;") =
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" := by decide

private theorem fntag_popUpTo :
    ("BackstackNavigationKt" ++ "." ++ "popUpTo" ++ ":" ++
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;") =
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" := by decide

private theorem fntag_popUpTo1 :
    ("BackstackNavigationKt" ++ "." ++ "popUpTo" ++ ":" ++
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;") =
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;" := by decide

private theorem fntag_popUpToValue :
    ("BackstackNavigationKt" ++ "." ++ "popUpToValue" ++ ":" ++
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;") =
      "BackstackNavigationKt.popUpToValue:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" := by decide

end ProgAndBsmLemmas

instance (resolveProg : String → Option (List JvmInstr)) (d fuel : Nat) :
    Jvm.HasDefaultIsZero (mkNavHooks resolveProg d fuel) where
  isZero?_eq := by cases d <;> rfl

/-! ### Equivalence of `runJvmRes` and `runJvmResFast` on `BackstackNavigationKt` Programs -/

def isNavAllowedInstr : JvmInstr → Bool
  | .i2l => false
  | .iflt _ | .ifle _ | .ifgt _ | .ifge _ | .ifnull _
  | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _ | .if_icmpge _ | .if_icmpgt _ | .if_icmple _
  | .if_acmpeq _ | .if_acmpne _ | .tableswitch _ _ _ | .lookupswitch _ _ => false
  | _ => true

private theorem branch_of_allowed {i : JvmInstr} (ha : isNavAllowedInstr i = true)
    (hb : Jvm.isBranchInstr i = true) :
    (∃ t, i = .goto t) ∨ (∃ t, i = .ifeq t) ∨ (∃ t, i = .ifne t) ∨ (∃ t, i = .ifnonnull t) := by
  cases i <;> simp_all [isNavAllowedInstr, Jvm.isBranchInstr]

private theorem navRunJvmRes_eq_fast {resolveProg : String → Option (List JvmInstr)}
    {d subFuel : Nat} (prog : List JvmInstr) (hallow : ∀ i ∈ prog, isNavAllowedInstr i = true)
    (fuel : Nat) (st : JvmState) :
    Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) fuel prog st =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) fuel prog st.pc (prog.drop st.pc) st := by
  let hooks := mkNavHooks resolveProg d subFuel
  refine Nat.strongRecOn (motive := fun f => ∀ st : JvmState,
      Jvm.runJvmRes hooks f prog st =
        Jvm.runJvmResFast hooks f prog st.pc (prog.drop st.pc) st) fuel (fun f ih st => ?_) st
  cases f with
  | zero => rfl
  | succ f1 =>
    cases hdrop : prog.drop st.pc with
    | nil =>
      have hge : prog.length ≤ st.pc := List.drop_eq_nil_iff.mp hdrop
      have hget : prog[st.pc]? = none := List.getElem?_eq_none hge
      simp [Jvm.runJvmRes, Jvm.runJvmResFast, hget]
    | cons instr rest =>
      have hget : prog[st.pc]? = some instr := by
        have h0 : (prog.drop st.pc)[0]? = prog[st.pc]? := by simp [List.getElem?_drop]
        rw [hdrop] at h0
        simpa using h0.symm
      have hall : isNavAllowedInstr instr = true := hallow instr (List.mem_of_getElem? hget)
      have hno_pat : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') := by
        intro ⟨h1, _⟩
        subst h1
        simp [isNavAllowedInstr] at hall
      cases hbr : Jvm.isBranchInstr instr with
      | false =>
        rw [Jvm.runJvmRes_nonbranch hooks f1 prog st instr hget hbr,
            Jvm.runJvmResFast_step_nonbranch hooks f1 prog st.pc instr rest st hbr hno_pat]
        have hst_pc : ({ st with pc := st.pc } : JvmState) = st := rfl
        rw [hst_pc]
        cases hs : Jvm.stepInstr hooks instr st with
        | inl opt =>
          cases opt with
          | none => rfl
          | some st' =>
            simp only
            split
            · next hpc =>
              have hdrop' : prog.drop (st.pc + 1) = rest := by
                rw [List.drop_add_one_eq_tail_drop, hdrop]; rfl
              have hih := ih f1 (Nat.lt_succ_self f1) st'
              rw [hpc, hdrop'] at hih
              exact hih
            · exact ih f1 (Nat.lt_succ_self f1) st'
        | inr res => cases res <;> rfl
      | true =>
        rw [Jvm.runJvmResFast_at_branch_cons hooks f1 prog st.pc instr rest st hbr]
        have hdrop1 : prog.drop (st.pc + 1) = rest := by
          rw [List.drop_add_one_eq_tail_drop, hdrop]; rfl
        rcases branch_of_allowed hall hbr with ⟨target, rfl⟩ | ⟨target, rfl⟩ | ⟨target, rfl⟩ | ⟨target, rfl⟩
        · rw [Jvm.runJvmRes, hget]
          dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
          exact ih f1 (Nat.lt_succ_self f1) { st with pc := target }
        · rw [Jvm.runJvmRes, hget]
          dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · cases hiz : hooks.isZero? v with
            | none => simp [hiz]
            | some b =>
              cases b <;> simp only [hiz, Bool.false_eq_true, ↓reduceIte, ← hdrop1]
              · exact ih f1 (Nat.lt_succ_self f1) { st with pc := st.pc + 1, stack := s }
              · exact ih f1 (Nat.lt_succ_self f1) { st with pc := target, stack := s }
        · rw [Jvm.runJvmRes, hget]
          dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · cases hiz : hooks.isZero? v with
            | none => simp [hiz]
            | some b =>
              cases b <;> simp only [hiz, Bool.false_eq_true, ↓reduceIte, ← hdrop1]
              · exact ih f1 (Nat.lt_succ_self f1) { st with pc := target, stack := s }
              · exact ih f1 (Nat.lt_succ_self f1) { st with pc := st.pc + 1, stack := s }
        · rw [Jvm.runJvmRes, hget]
          dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · cases hnull : v.isNull with
            | true =>
              simp only [hnull, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← hdrop1]
              exact ih f1 (Nat.lt_succ_self f1) { st with pc := st.pc + 1, stack := s }
            | false =>
              simp only [hnull, Bool.not_false, ↓reduceIte]
              exact ih f1 (Nat.lt_succ_self f1) { st with pc := target, stack := s }

/-! ### Generic Fast-Execution Step Helpers -/

private theorem runJvmResFast_athrow {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.athrow :: rest) ⟨pc0, stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .athrow rest ⟨pc0, stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runJvmResFast_areturn_nav {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.areturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkNavHooks resolveProg d subFuel) f prog pc .areturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  have hs : Jvm.stepInstr (mkNavHooks resolveProg d subFuel) .areturn ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inr (some v) := by
    dsimp only [Jvm.stepInstr]
  rw [hs]

private theorem runJvmResFast_ireturn_nav {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ireturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkNavHooks resolveProg d subFuel) f prog pc .ireturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  have hs : Jvm.stepInstr (mkNavHooks resolveProg d subFuel) .ireturn ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inr (some v) := by
    cases d <;> dsimp only [Jvm.stepInstr, mkNavHooks, id]
  rw [hs]

private theorem runJvmResFast_aload {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.aload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iload {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

elab "nav_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← Lean.instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr [``initNavJvmState, ``Jvm.initJvmState] (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "nav_aload" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_aload]; nav_norm_locals))

elab "nav_iload" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_iload]; nav_norm_locals))

private theorem runJvmResFast_astore {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {v : Jvm.JvmVal Ext} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.astore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_istore {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {v : Jvm.JvmVal Ext} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.istore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iconst {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {c : UInt32} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iconst c :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_ldcStr {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {s : String} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ldcStr s :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .str s :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_dup {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : Jvm.JvmVal Ext} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.dup :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_pop {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : Jvm.JvmVal Ext} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.pop :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iand {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {a b : UInt32} {prog rest : List JvmInstr} {stk : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iand :: rest) ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 (a &&& b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold Jvm.stepInstr; simp) rfl

private theorem runJvmResFast_newClass_nav {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {cls : String} (hnsb : (cls == "java/lang/StringBuilder") = false)
    {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.newClass cls :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkNavHooks resolveProg d subFuel) (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, mkNavHooks] <;> rw [Jvm.ite_bool_eq_true_right hnsb]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkNavHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_checkNotNullParam {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal} (hnn : v.isNull = false)
    {msg : String} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkNavHooks resolveProg d subFuel) ?_
  simp [Jvm.stepInvokeStaticGeneric, hnn]

private theorem runJvmResFast_areEqual {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (ha : a.equalsModeled jh = true := by rfl) (hb : b.equalsModeled jh = true := by rfl) :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual"
          "(Ljava/lang/Object;Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, b :: a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqNavExt a b) :: stk, locs, jh, hp⟩ := by
  cases d <;>
    exact Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (Jvm.stepInstr_areEqual _ ha hb) rfl

private theorem runJvmResFast_checkcast_entry {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "com/alexvanyo/composelife/navigation/BackstackEntry" :: rest)
        ⟨pc0, .ext (.entry e) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.entry e) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

private theorem runJvmResFast_checkcast_bool {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {b : Bool}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "java/lang/Boolean" :: rest)
        ⟨pc0, .boxedBool b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .boxedBool b :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

private theorem runJvmResFast_booleanValue {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {b : Bool}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "java/lang/Boolean" "booleanValue" "()Z" :: rest)
        ⟨pc0, .boxedBool b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if b then 1 else 0) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) rfl

private theorem runJvmResFast_getId {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/navigation/BackstackEntry" "getId" "()Lkotlin/uuid/Uuid;" :: rest)
        ⟨pc0, .ext (.entry e) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.uuid e.id) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) rfl

private theorem runJvmResFast_getPrevious {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/navigation/BackstackEntry" "getPrevious"
          "()Lcom/alexvanyo/composelife/navigation/BackstackEntry;" :: rest)
        ⟨pc0, .ext (.entry e) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, (match e.previous with | none => .null | some p => .ext (.entry p)) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) rfl

private theorem runJvmResFast_getValue {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/navigation/BackstackEntry" "getValue"
          "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.entry e) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, e.value.toJvmVal :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) rfl

private theorem runJvmResFast_mapsGetValue_some {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {mid : Nat} {m : BackstackMap NavValue}
    {keyId : EntryId} {e : BackstackEntry NavValue} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hm : hp.maps[mid]? = some m) (hlook : mapLookup m keyId = some e) :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/collections/MapsKt" "getValue"
          "(Ljava/util/Map;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.uuid keyId) :: .ext (.mapRef mid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.entry e) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkNavHooks resolveProg (d + 1) subFuel) ?_
  change (match hp.maps[mid]? with
    | some m =>
      match mapLookup m keyId with
      | some entry => Sum.inl (some (⟨pc + 1, .ext (.entry entry) :: stk, locs, jh, hp⟩ : JvmState))
      | none => Sum.inr none
    | none => Sum.inr none) = _
  rw [hm]
  dsimp only
  rw [hlook]

private theorem runJvmResFast_mapsGetValue_none {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {mid : Nat} {m : BackstackMap NavValue}
    {keyId : EntryId} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hm : hp.maps[mid]? = some m) (hlook : mapLookup m keyId = none) :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/collections/MapsKt" "getValue"
          "(Ljava/util/Map;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.uuid keyId) :: .ext (.mapRef mid) :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  have hs : Jvm.stepInstr (mkNavHooks resolveProg (d + 1) subFuel)
      (.invokestatic "kotlin/collections/MapsKt" "getValue"
        "(Ljava/util/Map;Ljava/lang/Object;)Ljava/lang/Object;")
      ⟨pc, .ext (.uuid keyId) :: .ext (.mapRef mid) :: stk, locs, jh, hp⟩ = .inr none := by
    change (match hp.maps[mid]? with
      | some m =>
        match mapLookup m keyId with
        | some entry => Sum.inl (some (⟨pc + 1, .ext (.entry entry) :: stk, locs, jh, hp⟩ : JvmState))
        | none => Sum.inr none
      | none => Sum.inr none) = Sum.inr none
    rw [hm]
    dsimp only
    rw [hlook]
  rw [hs]

private theorem runJvmResFast_mapPut {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {mid : Nat}
    {k : EntryId} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hlt : mid < hp.maps.size) :
    let m := hp.maps[mid]
    let prevVal : JvmVal := match mapLookup m k with | some p => .ext (.entry p) | none => .null
    let hp' := { hp with maps := hp.maps.set mid (mapPut m k e) hlt }
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "put"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.entry e) :: .ext (.uuid k) :: .ext (.mapRef mid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, prevVal :: stk, locs, jh, hp'⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel) ?_
  dsimp only [Jvm.stepInvokeInterfaceGeneric, mkNavHooks]
  simp [hlt]; rfl

private theorem runJvmResFast_mapRemove {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {mid : Nat}
    {k : EntryId}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hlt : mid < hp.maps.size) :
    let m := hp.maps[mid]
    let prevVal : JvmVal := match mapLookup m k with | some p => .ext (.entry p) | none => .null
    let hp' := { hp with maps := hp.maps.set mid (mapRemove m k) hlt }
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "remove"
          "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.uuid k) :: .ext (.mapRef mid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, prevVal :: stk, locs, jh, hp'⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel) ?_
  dsimp only [Jvm.stepInvokeInterfaceGeneric, mkNavHooks]
  simp [hlt]; rfl

private theorem runJvmResFast_entryInit {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {nv : NavValue} {prev : BackstackEntry NavValue} {id : EntryId} {cls : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/navigation/BackstackEntry" "<init>"
          "(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;Lkotlin/uuid/Uuid;)V" :: rest)
        ⟨pc0, .ext (.uuid id) :: .ext (.entry prev) :: nv.toJvmVal :: .allocRef cls :: .allocRef cls :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.entry (.node nv prev id)) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokespecial_step (mkNavHooks resolveProg (d + 1) subFuel) ?_
  dsimp only [Jvm.stepInvokeSpecialGeneric, mkNavHooks, normalizeNavClass]
  simp [NavValue.ofJvmVal?_toJvmVal, BackstackEntry.mk]

private theorem runJvmResFast_getstatic_uuidCompanion {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hc : jh.getStatic? "kotlin/uuid/Uuid" "Companion" = none) :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc
        (.getstatic "kotlin/uuid/Uuid" "Companion" "Lkotlin/uuid/Uuid$Companion;" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.companion "kotlin/uuid/Uuid$Companion") :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkNavHooks resolveProg d subFuel)
      (.getstatic "kotlin/uuid/Uuid" "Companion" "Lkotlin/uuid/Uuid$Companion;")
      ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.companion "kotlin/uuid/Uuid$Companion") :: stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, mkNavHooks] <;> rw [hc] <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkNavHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_uuidRandom {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "kotlin/uuid/Uuid$Companion" "random" "()Lkotlin/uuid/Uuid;" :: rest)
        ⟨pc0, .ext (.companion "kotlin/uuid/Uuid$Companion") :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.uuid hp.nextRandomId) :: stk, locs, jh,
          { hp with nextRandomId := hp.nextRandomId + 1 }⟩ :=
  Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) rfl

private theorem runJvmResFast_ifnonnull_some {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr} {e : BackstackEntry NavValue}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc, .ext (.entry e) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkNavHooks resolveProg d subFuel) (hbr := rfl)]
  rfl

private theorem runJvmResFast_ifnonnull_null {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkNavHooks resolveProg d subFuel) (hbr := rfl)]
  rfl

private theorem runJvmResFast_ifne_bool {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr} {b : Bool}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ifne target :: rest)
        ⟨pc, .i32 (if b then 1 else 0) :: stk, locs, jh, hp⟩ =
      if b then
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog target (prog.drop target)
          ⟨target, stk, locs, jh, hp⟩
      else
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
          ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkNavHooks resolveProg d subFuel) (hbr := rfl)]
  cases b <;> simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkNavHooks resolveProg d subFuel)]

private theorem runJvmResFast_ifeq_bool {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr} {b : Bool}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ifeq target :: rest)
        ⟨pc, .i32 (if b then 1 else 0) :: stk, locs, jh, hp⟩ =
      if b then
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
          ⟨pc + 1, stk, locs, jh, hp⟩
      else
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog target (prog.drop target)
          ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkNavHooks resolveProg d subFuel) (hbr := rfl)]
  cases b <;> simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkNavHooks resolveProg d subFuel)]

private theorem runJvmResFast_ifeq_mask {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap} :
    Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) (f + 1) prog pc (.ifeq target :: rest)
        ⟨pc, .i32 x :: stk, locs, jh, hp⟩ =
      if (x == 0) = true then
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog target (prog.drop target)
          ⟨target, stk, locs, jh, hp⟩
      else
        Jvm.runJvmResFast (mkNavHooks resolveProg d subFuel) f prog (pc + 1) rest
          ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkNavHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkNavHooks resolveProg d subFuel)]

private theorem runJvmResFast_invokedynamic_bsm {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {bsmArg desc fnTag : String} {boxBool : Bool} {cap : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    (hbsm : extractBsmTarget bsmArg = some (fnTag, boxBool))
    (htags : (Jvm.parseMethodParamTags desc).length = 1) :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg desc :: rest) ⟨pc0, cap :: stk, locs, jh, hp⟩ =
      let (cid, hp') := allocClosure hp (.bytecode fnTag [cap] boxBool)
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cid) :: stk, locs, jh, hp'⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr (mkNavHooks resolveProg (d + 1) subFuel) rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, mkNavHooks]
  simp [htags, hbsm, allocClosure]

private theorem stepInvokeStatic_backstack_eval (resolveProg : String → Option (List JvmInstr))
    (d subFuel pc : Nat) (method desc : String) (stkNow : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap NavExt) (hp : NavHeap) :
    Jvm.stepInvokeStaticGeneric (mkNavHooks resolveProg (d + 1) subFuel)
      ⟨pc, stkNow, locs, jh, hp⟩ "com/alexvanyo/composelife/navigation/BackstackNavigationKt" method desc =
    let nArgs := (Jvm.parseMethodParamTags desc).length
    if stkNow.length < nArgs then .inr none
    else
      let popped := stkNow.take nArgs
      let rest := stkNow.drop nArgs
      match
        match resolveProg ("BackstackNavigationKt" ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0 (Jvm.parseMethodParamTags desc) popped.reverse).foldl
                  (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) => some (res, (⟨pc, stkNow, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none with
      | some (res, st') => .inl (some ⟨pc + 1, res :: rest, st'.locals, st'.jvmHeap, st'.heap⟩)
      | none => .inr none := by
  rcases stkNow with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> rfl

private theorem runJvmResFast_invokeBackstackStatic_some {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    (method desc : String) {tags : List Char} {fnTag : String}
    {a0 a1 a2 a3 : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap NavExt} {hp hp' : NavHeap}
    {targetProg : List JvmInstr} {res : JvmVal} {endSt : JvmState}
    (htags : Jvm.parseMethodParamTags desc = tags)
    (hlen : tags.length = 4)
    (hassign : assignParamLocalsAux 0 tags [a3, a2, a1, a0] = [(0, a3), (1, a2), (2, a1), (3, a0)])
    (hftag : ("BackstackNavigationKt" ++ "." ++ method ++ ":" ++ desc) = fnTag)
    (hres : resolveProg fnTag = some targetProg)
    (hcall : Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel targetProg
      (initNavJvmState [(0, a3), (1, a2), (2, a1), (3, a0)] hp jh) = some (res, endSt))
    (hjh' : endSt.jvmHeap = jh') (hhp' : endSt.heap = hp') :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/navigation/BackstackNavigationKt" method desc :: rest)
        ⟨pc0, a0 :: a1 :: a2 :: a3 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, res :: stk, locs, jh', hp'⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkNavHooks resolveProg (d + 1) subFuel) ?_
  have hlt : ¬((a0 :: a1 :: a2 :: a3 :: stk).length < 4) := by simp
  have htake : (a0 :: a1 :: a2 :: a3 :: stk).take 4 = [a0, a1, a2, a3] := rfl
  have hdrop : (a0 :: a1 :: a2 :: a3 :: stk).drop 4 = stk := rfl
  have hrev : ([a0, a1, a2, a3] : List JvmVal).reverse = [a3, a2, a1, a0] := rfl
  rw [stepInvokeStatic_backstack_eval]
  simp only [htags, hftag, hlen, hlt, htake, hdrop, hrev, hassign, hres]
  change (match
      match Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel targetProg
          (initNavJvmState [(0, a3), (1, a2), (2, a1), (3, a0)] hp jh) with
      | some (res, endSt) => some (res, (⟨pc, a0 :: a1 :: a2 :: a3 :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
      | none => none with
    | some (res, st') => Sum.inl (some (⟨pc + 1, res :: stk, st'.locals, st'.jvmHeap, st'.heap⟩ : JvmState))
    | none => Sum.inr none) = _
  rw [hcall]
  dsimp only
  rw [hjh', hhp']

private theorem runJvmResFast_invokeBackstackStatic_none {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    (method desc : String) {tags : List Char} {fnTag : String}
    {a0 a1 a2 a3 : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap NavExt} {hp : NavHeap}
    {targetProg : List JvmInstr}
    (htags : Jvm.parseMethodParamTags desc = tags)
    (hlen : tags.length = 4)
    (hassign : assignParamLocalsAux 0 tags [a3, a2, a1, a0] = [(0, a3), (1, a2), (2, a1), (3, a0)])
    (hftag : ("BackstackNavigationKt" ++ "." ++ method ++ ":" ++ desc) = fnTag)
    (hres : resolveProg fnTag = some targetProg)
    (hcall : Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel targetProg
      (initNavJvmState [(0, a3), (1, a2), (2, a1), (3, a0)] hp jh) = none) :
    Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/navigation/BackstackNavigationKt" method desc :: rest)
        ⟨pc0, a0 :: a1 :: a2 :: a3 :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  have hlt : ¬((a0 :: a1 :: a2 :: a3 :: stk).length < 4) := by simp
  have htake : (a0 :: a1 :: a2 :: a3 :: stk).take 4 = [a0, a1, a2, a3] := rfl
  have hrev : ([a0, a1, a2, a3] : List JvmVal).reverse = [a3, a2, a1, a0] := rfl
  have hs : Jvm.stepInstr (mkNavHooks resolveProg (d + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/navigation/BackstackNavigationKt" method desc)
      ⟨pc, a0 :: a1 :: a2 :: a3 :: stk, locs, jh, hp⟩ = .inr none := by
    dsimp only [Jvm.stepInstr]
    rw [stepInvokeStatic_backstack_eval]
    simp only [htags, hftag, hlen, hlt, htake, hrev, hassign, hres]
    change (match
        match Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel targetProg
            (initNavJvmState [(0, a3), (1, a2), (2, a1), (3, a0)] hp jh) with
        | some (res, endSt) => some (res, (⟨pc, a0 :: a1 :: a2 :: a3 :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
        | none => none with
      | some (res, st') =>
        Sum.inl (some (⟨pc + 1, res :: (a0 :: a1 :: a2 :: a3 :: stk).drop 4, st'.locals, st'.jvmHeap, st'.heap⟩ : JvmState))
      | none => Sum.inr none) = .inr none
    rw [hcall]
  rw [hs]

private theorem stepInvokeInterface_function1 (resolveProg : String → Option (List JvmInstr))
    (d subFuel pc : Nat) (a0 : JvmVal) (cid : Nat) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap NavExt) (hp : NavHeap) :
    Jvm.stepInvokeInterfaceGeneric (mkNavHooks resolveProg (d + 1) subFuel)
      ⟨pc, a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
    match
      match hp.closures[cid]? with
      | some (.host fn) =>
        (fn a0).map (fun r => (r, (⟨pc, a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ : JvmState)))
      | some (.bytecode fnTag captures boxBool) =>
        match resolveProg fnTag with
        | some prog =>
          match Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) subFuel prog
              { pc := 0, stack := [],
                locals := (assignLinearLocals 0 (captures ++ [a0])).foldl
                  (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) =>
            match boxBoolIfNeeded boxBool res with
            | some res' =>
              some (res', (⟨pc, a0 :: .ext (.closureRef cid) :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
            | none => none
          | none => none
        | none => none
      | none => none with
    | some (res, st') => .inl (some ⟨pc + 1, res :: stk, st'.locals, st'.jvmHeap, st'.heap⟩)
    | none => .inr none := rfl

/-! ### Closure Predicates for Higher-Order Navigation Operations -/

/-- Specification of a `Function1<BackstackEntry<T>, Boolean>` closure at `cid`. -/
def IsEntryPredClosure (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    (closures : Array NavClosure) (cid : Nat) (pred : BackstackEntry NavValue → Bool) : Prop :=
  ∀ (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (maps : Array (BackstackMap NavValue)) (nextId : EntryId)
    (jh : Jvm.JvmHeap NavExt) (e : BackstackEntry NavValue),
    Jvm.stepInvokeInterfaceGeneric (mkNavHooks resolveProg (d + 1) subFuel)
      ⟨pc, .ext (.entry e) :: .ext (.closureRef cid) :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .boxedBool (pred e) :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩)

/-- Specification of a `Function1<T, Boolean>` closure at `cid`. -/
def IsValuePredClosure (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    (closures : Array NavClosure) (cid : Nat) (pred : NavValue → Bool) : Prop :=
  ∀ (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (maps : Array (BackstackMap NavValue)) (nextId : EntryId)
    (jh : Jvm.JvmHeap NavExt) (v : NavValue),
    Jvm.stepInvokeInterfaceGeneric (mkNavHooks resolveProg (d + 1) subFuel)
      ⟨pc, v.toJvmVal :: .ext (.closureRef cid) :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .boxedBool (pred v) :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩)

/-- Specification of a `Function1<BackstackEntry<T>, T>` closure at `cid`. -/
def IsValueFactoryClosure (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    (closures : Array NavClosure) (cid : Nat) (vf : BackstackEntry NavValue → NavValue) : Prop :=
  ∀ (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (maps : Array (BackstackMap NavValue)) (nextId : EntryId)
    (jh : Jvm.JvmHeap NavExt) (e : BackstackEntry NavValue),
    Jvm.stepInvokeInterfaceGeneric (mkNavHooks resolveProg (d + 1) subFuel)
      ⟨pc, .ext (.entry e) :: .ext (.closureRef cid) :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, (vf e).toJvmVal :: stk, locs, jh,
        { maps := maps, closures := closures, nextRandomId := nextId }⟩)

theorem host_entryPredClosure_spec (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    {closures : Array NavClosure} {cid : Nat} {pred : BackstackEntry NavValue → Bool}
    (hc : closures[cid]? = some (mkEntryPredClosure pred)) :
    IsEntryPredClosure resolveProg d subFuel closures cid pred := by
  intro pc stk locs maps nextId jh e
  rw [stepInvokeInterface_function1]
  rw [hc]
  rfl

theorem host_valuePredClosure_spec (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    {closures : Array NavClosure} {cid : Nat} {pred : NavValue → Bool}
    (hc : closures[cid]? = some (mkValuePredClosure pred)) :
    IsValuePredClosure resolveProg d subFuel closures cid pred := by
  intro pc stk locs maps nextId jh v
  rw [stepInvokeInterface_function1]
  rw [hc]
  simp [mkValuePredClosure]

theorem host_valueFactoryClosure_spec (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat)
    {closures : Array NavClosure} {cid : Nat} {vf : BackstackEntry NavValue → NavValue}
    (hc : closures[cid]? = some (mkValueFactoryClosure vf)) :
    IsValueFactoryClosure resolveProg d subFuel closures cid vf := by
  intro pc stk locs maps nextId jh e
  rw [stepInvokeInterface_function1]
  rw [hc]
  rfl

/-! ### 1. Lambda Helpers (`popUpTo_lambda_2`, `popUpTo_lambda_3`, `navigate_lambda_0`) -/

theorem popUpTo_lambda_2_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 10 ≤ fuel)
    (targetId : EntryId) (e : BackstackEntry NavValue)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) fuel BackstackNavigationKt_popUpTo_lambda_2_prog
        (initNavJvmState [(0, .ext (.uuid targetId)), (1, .ext (.entry e))] hp jh) =
        some (.bool (e.id == targetId), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_lambda_2_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_lambda_2_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.entry e)) rfl]
  nav_aload; rw [runJvmResFast_getId]; nav_aload; rw [runJvmResFast_areEqual]
  have hbeq : Jvm.JvmVal.beqVal beqNavExt (.ext (.uuid e.id)) (.ext (.uuid targetId)) = (e.id == targetId) := by
    by_cases h : e.id = targetId <;> simp [Jvm.JvmVal.beqVal, beqNavExt, h]
  rw [hbeq, runJvmResFast_ireturn_nav]
  exact ⟨_, rfl, rfl, rfl⟩

theorem popUpTo_lambda_3_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (_hd : 1 ≤ d) (hf : 12 ≤ fuel)
    (predCid : Nat) (pred : NavValue → Bool)
    (e : BackstackEntry NavValue) (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hc : IsValuePredClosure resolveProg d subFuel hp.closures predCid pred) :
    ∃ endSt,
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_popUpTo_lambda_3_prog
        (initNavJvmState [(0, .ext (.closureRef predCid)), (1, .ext (.entry e))] hp jh) =
        some (.i32 (if pred e.value then 1 else 0), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_lambda_3_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_lambda_3_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.entry e)) rfl]
  nav_aload; nav_aload; rw [runJvmResFast_getValue]
  rw [Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel)
    (hc 6 _ _ hp.maps hp.nextRandomId jh e.value)]
  rw [runJvmResFast_checkcast_bool, runJvmResFast_booleanValue, runJvmResFast_ireturn_nav]
  exact ⟨_, rfl, rfl, rfl⟩

theorem navigate_lambda_0_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hf : 10 ≤ fuel)
    (val : NavValue) (e : BackstackEntry NavValue)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) fuel BackstackNavigationKt_navigate_lambda_0_prog
        (initNavJvmState [(0, val.toJvmVal), (1, .ext (.entry e))] hp jh) =
        some (val.toJvmVal, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_navigate_lambda_0_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_navigate_lambda_0_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.entry e)) rfl]
  nav_aload; rw [runJvmResFast_areturn_nav]
  exact ⟨_, rfl, rfl, rfl⟩

private theorem bytecode_lambda2_closure_spec (resolveProg : String → Option (List JvmInstr))
    (d subFuel : Nat) (hd : 1 ≤ d) (hsf : 10 ≤ subFuel)
    (hExt : ExtendsNavProgs resolveProg) (closures : Array NavClosure) (cid : Nat) (targetId : EntryId)
    (hc : closures[cid]? = some (.bytecode
      "BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z"
      [.ext (.uuid targetId)] true)) :
    IsEntryPredClosure resolveProg d subFuel closures cid (fun e => e.id == targetId) := by
  intro pc stk locs maps nextId jh e
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some BackstackNavigationKt_popUpTo_lambda_2_prog := hExt _ _ navProgLookup_lambda2
  obtain ⟨endSt, hrun, hjh, hhp⟩ := popUpTo_lambda_2_equiv resolveProg d subFuel subFuel hd hsf
    targetId e { maps := maps, closures := closures, nextRandomId := nextId } jh
  rw [stepInvokeInterface_function1]
  rw [hc]
  dsimp only
  rw [hprog]
  dsimp only
  have hloc : assignLinearLocals 0 ([Jvm.JvmVal.ext (NavExt.uuid targetId)] ++ [Jvm.JvmVal.ext (NavExt.entry e)]) =
      [(0, .ext (.uuid targetId)), (1, .ext (.entry e))] := rfl
  rw [hloc]
  dsimp only [initNavJvmState, Jvm.initJvmState] at hrun
  rw [hrun]
  dsimp only
  rw [hjh, hhp]
  rfl

private theorem bytecode_lambda3_closure_spec (resolveProg : String → Option (List JvmInstr))
    (d subFuel : Nat) (hd : 1 ≤ d) (hsf : 12 ≤ subFuel)
    (hExt : ExtendsNavProgs resolveProg) (closures : Array NavClosure) (cid predCid : Nat)
    (pred : NavValue → Bool)
    (hpred : IsValuePredClosure resolveProg d subFuel closures predCid pred)
    (hc : closures[cid]? = some (.bytecode
      "BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z"
      [.ext (.closureRef predCid)] true)) :
    IsEntryPredClosure resolveProg (d + 1) subFuel closures cid (fun e => pred e.value) := by
  intro pc stk locs maps nextId jh e
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =
      some BackstackNavigationKt_popUpTo_lambda_3_prog := hExt _ _ navProgLookup_lambda3
  obtain ⟨endSt, hrun, hjh, hhp⟩ := popUpTo_lambda_3_equiv resolveProg d subFuel subFuel hd hsf
    predCid pred e { maps := maps, closures := closures, nextRandomId := nextId } jh hpred
  rw [stepInvokeInterface_function1]
  rw [hc]
  dsimp only
  rw [hprog]
  dsimp only
  have hloc : assignLinearLocals 0 ([Jvm.JvmVal.ext (NavExt.closureRef predCid)] ++ [Jvm.JvmVal.ext (NavExt.entry e)]) =
      [(0, .ext (.closureRef predCid)), (1, .ext (.entry e))] := rfl
  rw [hloc]
  dsimp only [initNavJvmState, Jvm.initJvmState] at hrun
  rw [hrun]
  dsimp only
  rw [hjh, hhp]
  cases h : pred e.value <;> rfl

private theorem bytecode_lambda0_closure_spec (resolveProg : String → Option (List JvmInstr))
    (d subFuel : Nat) (hsf : 10 ≤ subFuel)
    (hExt : ExtendsNavProgs resolveProg) (closures : Array NavClosure) (cid : Nat) (val : NavValue)
    (hc : closures[cid]? = some (.bytecode
      "BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;"
      [val.toJvmVal] false)) :
    IsValueFactoryClosure resolveProg d subFuel closures cid (fun _ => val) := by
  intro pc stk locs maps nextId jh e
  have hprog : resolveProg
      "BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;" =
      some BackstackNavigationKt_navigate_lambda_0_prog := hExt _ _ navProgLookup_lambda0
  obtain ⟨endSt, hrun, hjh, hhp⟩ := navigate_lambda_0_equiv resolveProg d subFuel subFuel hsf
    val e { maps := maps, closures := closures, nextRandomId := nextId } jh
  rw [stepInvokeInterface_function1]
  rw [hc]
  dsimp only
  rw [hprog]
  dsimp only
  have hloc : assignLinearLocals 0 ([val.toJvmVal] ++ [Jvm.JvmVal.ext (NavExt.entry e)]) =
      [(0, val.toJvmVal), (1, .ext (.entry e))] := rfl
  rw [hloc]
  dsimp only [initNavJvmState, Jvm.initJvmState] at hrun
  rw [hrun]
  dsimp only
  rw [hjh, hhp]
  rfl

/-! ### 2. `popBackstack` Equivalence -/

theorem popBackstack_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 40 ≤ fuel)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m) :
    let st0 := initNavJvmState [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId))] hp jh
    match popBackstackModel m curId with
    | .ok m' nextId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) fuel BackstackNavigationKt_popBackstack_prog st0 =
          some (.ext (.uuid nextId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = hp.closures ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg d subFuel) fuel BackstackNavigationKt_popBackstack_prog st0 = none := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hlt : mid < hp.maps.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hm_eq : hp.maps[mid] = m := Array.getElem?_eq_some_iff.mp hm |>.2
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popBackstack_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popBackstack_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; nav_aload
  cases hlook : mapLookup m curId with
  | none =>
    simp only [popBackstackModel, hlook]
    rw [runJvmResFast_mapsGetValue_none hm hlook]
  | some cur =>
    rw [runJvmResFast_mapsGetValue_some hm hlook, runJvmResFast_checkcast_entry,
        runJvmResFast_astore]
    nav_aload; rw [runJvmResFast_getPrevious, runJvmResFast_dup]
    cases hprev : cur.previous with
    | none =>
      simp only [popBackstackModel, hlook, hprev]
      rw [runJvmResFast_ifnonnull_null, runJvmResFast_pop, runJvmResFast_iconst, runJvmResFast_istore,
          runJvmResFast_ldcStr, runJvmResFast_astore, runJvmResFast_newClass_nav (by decide),
          runJvmResFast_dup]
      nav_aload
      refine (Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d1 + 1) subFuel) (by rfl)).trans ?_
      refine (Jvm.runJvmResFast_invokespecial_step (mkNavHooks resolveProg (d1 + 1) subFuel) (by rfl)).trans ?_
      exact runJvmResFast_athrow (mkNavHooks resolveProg (d1 + 1) subFuel)
    | some prev =>
      simp only [popBackstackModel, hlook, hprev]
      rw [runJvmResFast_ifnonnull_some]
      dsimp only [BackstackNavigationKt_popBackstack_prog, List.drop]
      rw [runJvmResFast_astore]; nav_aload; nav_aload; rw [runJvmResFast_getId]
      rw [runJvmResFast_mapRemove (hlt := hlt), runJvmResFast_pop]; nav_aload
      rw [runJvmResFast_getId, runJvmResFast_areturn_nav]
      refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
      simp [hm_eq]

/-! ### 3. `navigate` Equivalence (`navigate`, `navigate$default`, `navigate_1`, `navigate_1$default`) -/

theorem navigate_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (_hd : 1 ≤ d) (hf : 45 ≤ fuel)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (vfCid : Nat) (vf : BackstackEntry NavValue → NavValue) (freshId : EntryId)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hvf : IsValueFactoryClosure resolveProg d subFuel hp.closures vfCid vf) :
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef vfCid)), (3, .ext (.uuid freshId))] hp jh
    match navigateModel m curId vf freshId with
    | .ok m' newId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_navigate_prog st0 =
          some (.ext (.uuid newId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = hp.closures ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_navigate_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hlt : mid < hp.maps.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hm_eq : hp.maps[mid] = m := Array.getElem?_eq_some_iff.mp hm |>.2
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_navigate_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_navigate_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.closureRef vfCid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid freshId)) rfl]
  nav_aload; nav_aload
  cases hlook : mapLookup m curId with
  | none =>
    simp only [navigateModel, hlook]
    rw [runJvmResFast_mapsGetValue_none hm hlook]
  | some prev =>
    simp only [navigateModel, hlook]
    rw [runJvmResFast_mapsGetValue_some hm hlook, runJvmResFast_checkcast_entry, runJvmResFast_astore]
    nav_aload; nav_aload
    rw [Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel)
      (hvf 19 _ _ hp.maps hp.nextRandomId jh prev), runJvmResFast_astore, runJvmResFast_newClass_nav (by decide), runJvmResFast_dup]
    nav_aload; nav_aload; nav_aload
    rw [runJvmResFast_entryInit, runJvmResFast_astore]
    nav_aload; nav_aload; rw [runJvmResFast_getId]; nav_aload
    rw [runJvmResFast_mapPut (hlt := hlt), runJvmResFast_pop]
    nav_aload; rw [runJvmResFast_getId, runJvmResFast_areturn_nav]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
    simp [hm_eq, BackstackEntry.id]

theorem navigate_default_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ subFuel) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (vfCid : Nat) (vf : BackstackEntry NavValue → NavValue) (argId : EntryId) (mask : UInt32)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hcStatic : jh.getStatic? "kotlin/uuid/Uuid" "Companion" = none)
    (hvf : IsValueFactoryClosure resolveProg d subFuel hp.closures vfCid vf) :
    let useDefault := (mask &&& 4) != 0
    let chosenId := if useDefault then hp.nextRandomId else argId
    let expectedNextId := if useDefault then hp.nextRandomId + 1 else hp.nextRandomId
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef vfCid)), (3, .ext (.uuid argId)),
       (4, .i32 mask), (5, .null)] hp jh
    match navigateModel m curId vf chosenId with
    | .ok m' newId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_navigate_default_prog st0 =
          some (.ext (.uuid newId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = hp.closures ∧
        endSt.heap.nextRandomId = expectedNextId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_navigate_default_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_navigate_prog := hExt _ _ navProgLookup_navigate
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_navigate_default_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_navigate_default_prog, List.drop]
  nav_iload; rw [runJvmResFast_iconst, runJvmResFast_iand, runJvmResFast_ifeq_mask]
  by_cases hmask : ((mask &&& 4) == 0) = true
  · have hud : ((mask &&& 4) != 0) = false := by simp [bne, hmask]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    dsimp only [BackstackNavigationKt_navigate_default_prog, List.drop]
    nav_aload; nav_aload; nav_aload; nav_aload
    have hsub := navigate_equiv resolveProg d subFuel subFuel hd hsf mid m curId vfCid vf argId hp jh hm hvf
    cases hnav : navigateModel m curId vf argId with
    | error err =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav rfl rfl fntag_nav hprog hsub]
    | ok m' newId =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubClo, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav rfl rfl fntag_nav hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubClo, hsubRand⟩
  · have hmaskf : ((mask &&& 4) == 0) = false := Bool.eq_false_iff.mpr hmask
    have hud : ((mask &&& 4) != 0) = true := by simp [bne, hmaskf]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    rw [runJvmResFast_getstatic_uuidCompanion hcStatic, runJvmResFast_uuidRandom, runJvmResFast_astore]
    nav_aload; nav_aload; nav_aload; nav_aload
    let hp1 := { hp with nextRandomId := hp.nextRandomId + 1 }
    have hm1 : hp1.maps[mid]? = some m := hm
    have hvf1 : IsValueFactoryClosure resolveProg d subFuel hp1.closures vfCid vf := hvf
    have hsub := navigate_equiv resolveProg d subFuel subFuel hd hsf mid m curId vfCid vf hp.nextRandomId
      hp1 jh hm1 hvf1
    cases hnav : navigateModel m curId vf hp.nextRandomId with
    | error err =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav rfl rfl fntag_nav hprog hsub]
    | ok m' newId =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubClo, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav rfl rfl fntag_nav hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubClo, hsubRand⟩

theorem navigate_1_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ subFuel) (hf : 25 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (val : NavValue) (freshId : EntryId)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m) :
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, val.toJvmVal), (3, .ext (.uuid freshId))] hp jh
    match navigateValueModel m curId val freshId with
    | .ok m' newId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_navigate_1_prog st0 =
          some (.ext (.uuid newId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_navigate_1_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_navigate_prog := hExt _ _ navProgLookup_navigate
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_navigate_1_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_navigate_1_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid freshId)) rfl]
  nav_aload; nav_aload; nav_aload
  rw [runJvmResFast_invokedynamic_bsm (hbsm := bsm_lambda0) (htags := tags_obj_len1)]
  dsimp only [allocClosure]
  nav_aload
  let lamTag :=
    "BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;"
  let hp1 := { hp with closures := hp.closures.push (.bytecode lamTag [val.toJvmVal] false) }
  have hcid : hp1.closures[hp.closures.size]? = some (.bytecode lamTag [val.toJvmVal] false) := by
    simp [hp1]
  have hvf : IsValueFactoryClosure resolveProg d subFuel hp1.closures hp.closures.size (fun _ => val) :=
    bytecode_lambda0_closure_spec resolveProg d subFuel (by omega) hExt hp1.closures hp.closures.size val hcid
  have hm1 : hp1.maps[mid]? = some m := hm
  have hsub := navigate_equiv resolveProg d subFuel subFuel hd hsf mid m curId hp.closures.size
    (fun _ => val) freshId hp1 jh hm1 hvf
  cases hnav : navigateValueModel m curId val freshId with
  | error err =>
    have hnav' : navigateModel m curId (fun _ => val) freshId = .error err := hnav
    rw [hnav'] at hsub
    dsimp only at hsub ⊢
    rw [runJvmResFast_invokeBackstackStatic_none "navigate"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
      ptags_nav rfl rfl fntag_nav hprog hsub]
  | ok m' newId =>
    have hnav' : navigateModel m curId (fun _ => val) freshId = .ok m' newId := hnav
    rw [hnav'] at hsub
    dsimp only at hsub ⊢
    obtain ⟨subEnd, hcall, hsubJh, hsubMaps, _, hsubRand⟩ := hsub
    rw [runJvmResFast_invokeBackstackStatic_some "navigate"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
      ptags_nav rfl rfl fntag_nav hprog hcall rfl rfl]
    rw [runJvmResFast_areturn_nav]
    exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

theorem navigate_default_1_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ subFuel) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (val : NavValue) (argId : EntryId) (mask : UInt32)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hcStatic : jh.getStatic? "kotlin/uuid/Uuid" "Companion" = none) :
    let useDefault := (mask &&& 4) != 0
    let chosenId := if useDefault then hp.nextRandomId else argId
    let expectedNextId := if useDefault then hp.nextRandomId + 1 else hp.nextRandomId
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, val.toJvmVal), (3, .ext (.uuid argId)),
       (4, .i32 mask), (5, .null)] hp jh
    match navigateValueModel m curId val chosenId with
    | .ok m' newId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_navigate_default_1_prog st0 =
          some (.ext (.uuid newId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = expectedNextId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_navigate_default_1_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.navigate:(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_navigate_1_prog := hExt _ _ navProgLookup_navigate1
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_navigate_default_1_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_navigate_default_1_prog, List.drop]
  nav_iload; rw [runJvmResFast_iconst, runJvmResFast_iand, runJvmResFast_ifeq_mask]
  by_cases hmask : ((mask &&& 4) == 0) = true
  · have hud : ((mask &&& 4) != 0) = false := by simp [bne, hmask]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    dsimp only [BackstackNavigationKt_navigate_default_1_prog, List.drop]
    nav_aload; nav_aload; nav_aload; nav_aload
    have hsub := navigate_1_equiv resolveProg d subFuel subFuel hd hsf (by omega) hExt mid m curId val argId hp jh hm
    cases hnav : navigateValueModel m curId val argId with
    | error err =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav1 rfl rfl fntag_nav1 hprog hsub]
    | ok m' newId =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav1 rfl rfl fntag_nav1 hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩
  · have hmaskf : ((mask &&& 4) == 0) = false := Bool.eq_false_iff.mpr hmask
    have hud : ((mask &&& 4) != 0) = true := by simp [bne, hmaskf]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    rw [runJvmResFast_getstatic_uuidCompanion hcStatic, runJvmResFast_uuidRandom, runJvmResFast_astore]
    nav_aload; nav_aload; nav_aload; nav_aload
    let hp1 := { hp with nextRandomId := hp.nextRandomId + 1 }
    have hm1 : hp1.maps[mid]? = some m := hm
    have hsub := navigate_1_equiv resolveProg d subFuel subFuel hd hsf (by omega) hExt mid m curId
      val hp.nextRandomId hp1 jh hm1
    cases hnav : navigateValueModel m curId val hp.nextRandomId with
    | error err =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav1 rfl rfl fntag_nav1 hprog hsub]
    | ok m' newId =>
      rw [hnav] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "navigate"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Ljava/lang/Object;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;"
        ptags_nav1 rfl rfl fntag_nav1 hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

/-! ### 4. `popUpTo` Equivalence (`popUpTo`, `popUpTo$default`, `popUpTo_1`, `popUpTo_1$default`, `popUpToValue`, `popUpToValue$default`) -/

private def popUpToTail {α : Type} (pred : BackstackEntry α → Bool) (inclusive : Bool)
    (m : BackstackMap α) (cur : BackstackEntry α) : Option (BackstackMap α × EntryId) :=
  match popUpToWalk pred m cur with
  | none => none
  | some (m1, target) =>
    if inclusive then
      match target.previous with
      | none => none
      | some prev => some (mapRemove m1 target.id, prev.id)
    else
      some (m1, target.id)

private theorem popUpTo_loop_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel : Nat) (mid predCid : Nat) (pred : BackstackEntry NavValue → Bool)
    (inclusive : Bool) (closures : Array NavClosure) (nextId : EntryId)
    (hpred : IsEntryPredClosure resolveProg d subFuel closures predCid pred)
    (cur : BackstackEntry NavValue) (m : BackstackMap NavValue)
    (maps0 : Array (BackstackMap NavValue)) (hlt : mid < maps0.size)
    (locs : Nat → JvmVal)
    (hl0 : locs 0 = .ext (.mapRef mid))
    (hl2 : locs 2 = .ext (.closureRef predCid))
    (hl3 : locs 3 = .i32 (if inclusive then 1 else 0))
    (hl4 : locs 4 = .ext (.entry cur))
    (jh : Jvm.JvmHeap NavExt) (fuel : Nat) (hf : 26 * cur.depth + 4 ≤ fuel) :
    let hp := { maps := maps0.set mid m hlt, closures := closures, nextRandomId := nextId }
    match popUpToTail pred inclusive m cur with
    | some (m', resId) =>
      ∃ endSt,
        Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_popUpTo_prog 14
          (List.drop 14 BackstackNavigationKt_popUpTo_prog) ⟨14, [], locs, jh, hp⟩ =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = closures ∧
        endSt.heap.nextRandomId = nextId
    | none =>
      Jvm.runJvmResFast (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_popUpTo_prog 14
        (List.drop 14 BackstackNavigationKt_popUpTo_prog) ⟨14, [], locs, jh, hp⟩ = none := by
  induction cur generalizing m locs fuel with
  | root v id =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    simp only [BackstackEntry.depth, Nat.mul_one] at k ⊢
    dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
    rw [runJvmResFast_aload, hl2, runJvmResFast_aload, hl4]
    rw [Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel)
      (hpred 16 _ locs (maps0.set mid m hlt) nextId jh (.root v id)),
      runJvmResFast_checkcast_bool, runJvmResFast_booleanValue, runJvmResFast_ifne_bool]
    cases hp_b : pred (.root v id) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, popUpToTail, popUpToWalk, hp_b]
      rw [runJvmResFast_aload, hl0, runJvmResFast_aload, hl4, runJvmResFast_getId,
          runJvmResFast_mapRemove (hlt := by simp [hlt]), runJvmResFast_pop,
          runJvmResFast_aload, hl4, runJvmResFast_getPrevious, runJvmResFast_dup]
      dsimp only [BackstackEntry.previous]
      rw [runJvmResFast_ifnonnull_null, runJvmResFast_pop, runJvmResFast_iconst, runJvmResFast_istore,
          runJvmResFast_ldcStr, runJvmResFast_astore, runJvmResFast_newClass_nav (by decide),
          runJvmResFast_dup, runJvmResFast_aload]
      refine (Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) (by rfl)).trans ?_
      refine (Jvm.runJvmResFast_invokespecial_step (mkNavHooks resolveProg (d + 1) subFuel) (by rfl)).trans ?_
      exact runJvmResFast_athrow (mkNavHooks resolveProg (d + 1) subFuel)
    | true =>
      simp only [↓reduceIte, popUpToTail, popUpToWalk, hp_b]
      dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
      rw [runJvmResFast_iload, hl3, runJvmResFast_ifeq_bool]
      cases inclusive with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
        rw [runJvmResFast_aload, hl4, runJvmResFast_getId, runJvmResFast_areturn_nav]
        refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
        simp [hlt]
      | true =>
        simp only [↓reduceIte, BackstackEntry.previous]
        rw [runJvmResFast_aload, hl0, runJvmResFast_aload, hl4, runJvmResFast_getId,
            runJvmResFast_mapRemove (hlt := by simp [hlt]), runJvmResFast_pop,
            runJvmResFast_aload, hl4, runJvmResFast_getPrevious, runJvmResFast_dup]
        dsimp only [BackstackEntry.previous]
        rw [runJvmResFast_ifnonnull_null, runJvmResFast_pop, runJvmResFast_iconst, runJvmResFast_istore,
            runJvmResFast_ldcStr, runJvmResFast_astore, runJvmResFast_newClass_nav (by decide),
            runJvmResFast_dup, runJvmResFast_aload]
        refine (Jvm.runJvmResFast_invokevirtual_step (mkNavHooks resolveProg (d + 1) subFuel) (by rfl)).trans ?_
        refine (Jvm.runJvmResFast_invokespecial_step (mkNavHooks resolveProg (d + 1) subFuel) (by rfl)).trans ?_
        exact runJvmResFast_athrow (mkNavHooks resolveProg (d + 1) subFuel)
  | node v prev id ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    have hfuel : k + (26 * (BackstackEntry.node v prev id).depth + 4) =
        (k + 26 * prev.depth + 9) + 21 := by
      simp only [BackstackEntry.depth]; omega
    rw [hfuel]
    dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
    rw [runJvmResFast_aload, hl2, runJvmResFast_aload, hl4]
    rw [Jvm.runJvmResFast_invokeinterface_step (mkNavHooks resolveProg (d + 1) subFuel)
      (hpred 16 _ locs (maps0.set mid m hlt) nextId jh (.node v prev id)),
      runJvmResFast_checkcast_bool, runJvmResFast_booleanValue, runJvmResFast_ifne_bool]
    cases hp_b : pred (.node v prev id) with
    | true =>
      simp only [↓reduceIte, popUpToTail, popUpToWalk, hp_b]
      dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
      rw [runJvmResFast_iload, hl3, runJvmResFast_ifeq_bool]
      cases inclusive with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
        rw [runJvmResFast_aload, hl4, runJvmResFast_getId, runJvmResFast_areturn_nav]
        refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
        simp [hlt]
      | true =>
        simp only [↓reduceIte, BackstackEntry.previous, BackstackEntry.id]
        rw [runJvmResFast_aload, hl0, runJvmResFast_aload, hl4, runJvmResFast_getId,
            runJvmResFast_mapRemove (hlt := by simp [hlt]), runJvmResFast_pop,
            runJvmResFast_aload, hl4, runJvmResFast_getPrevious, runJvmResFast_dup]
        dsimp only [BackstackEntry.previous]
        rw [runJvmResFast_ifnonnull_some]
        dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
        rw [runJvmResFast_astore, runJvmResFast_aload]
        simp only [setLocal, ↓reduceIte]
        rw [runJvmResFast_getId, runJvmResFast_areturn_nav]
        refine ⟨_, rfl, rfl, ?_, rfl, rfl⟩
        simp [hlt, BackstackEntry.id]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, popUpToTail, popUpToWalk, hp_b]
      rw [runJvmResFast_aload, hl0, runJvmResFast_aload, hl4, runJvmResFast_getId,
          runJvmResFast_mapRemove (hlt := by simp [hlt]), runJvmResFast_pop,
          runJvmResFast_aload, hl4, runJvmResFast_getPrevious, runJvmResFast_dup]
      dsimp only [BackstackEntry.previous]
      rw [runJvmResFast_ifnonnull_some]
      dsimp only [BackstackNavigationKt_popUpTo_prog, List.drop]
      rw [runJvmResFast_astore, Jvm.runJvmResFast_goto]
      have hf_rem : 26 * prev.depth + 4 ≤ (k + 26 * prev.depth + 9) + 4 := by omega
      simp only [BackstackEntry.id, Array.getElem_set_self, Array.set_set]
      exact ih (mapRemove m id) (setLocal locs 4 (.ext (.entry prev)))
        hl0 hl2 hl3 rfl ((k + 26 * prev.depth + 9) + 4) hf_rem

theorem popUpTo_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (_hd : 1 ≤ d)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (predCid : Nat) (pred : BackstackEntry NavValue → Bool) (inclusive : Bool)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hpred : IsEntryPredClosure resolveProg d subFuel hp.closures predCid pred)
    (hf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ fuel | none => 20 ≤ fuel) :
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef predCid)), (3, .i32 (if inclusive then 1 else 0))] hp jh
    match popUpToModel m curId pred inclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_popUpTo_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = hp.closures ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 1) subFuel) fuel BackstackNavigationKt_popUpTo_prog st0 = none := by
  have hlt : mid < hp.maps.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hm_eq : hp.maps[mid] = m := Array.getElem?_eq_some_iff.mp hm |>.2
  have hmin : 14 ≤ fuel := by
    cases hlook : mapLookup m curId with
    | none => simp [hlook] at hf; omega
    | some head =>
      simp [hlook] at hf
      have : 1 ≤ head.depth := by cases head <;> simp [BackstackEntry.depth] <;> omega
      omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hmin
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.closureRef predCid)) rfl]
  nav_aload; nav_aload
  cases hlook : mapLookup m curId with
  | none =>
    simp only [popUpToModel, hlook]
    rw [runJvmResFast_mapsGetValue_none hm hlook]
  | some head =>
    rw [runJvmResFast_mapsGetValue_some hm hlook, runJvmResFast_checkcast_entry, runJvmResFast_astore]
    simp only [hlook] at hf
    have hf_loop : 26 * head.depth + 4 ≤ k := by omega
    let locs1 := setLocal (List.foldl (fun loc (x : Nat × JvmVal) => setLocal loc x.1 x.2)
      (fun _ => .i32 0) [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
        (2, .ext (.closureRef predCid)), (3, .i32 (if inclusive then 1 else 0))])
      4 (.ext (.entry head))
    have hloop := popUpTo_loop_equiv resolveProg d subFuel mid predCid pred inclusive
      hp.closures hp.nextRandomId hpred head m hp.maps hlt locs1
      rfl rfl rfl rfl jh k hf_loop
    have hset_self : hp.maps.set mid m hlt = hp.maps := by simp [← hm_eq]
    have hhp_eq : (⟨hp.maps.set mid m hlt, hp.closures, hp.nextRandomId⟩ : NavHeap) = hp := by
      cases hp; simp only [hset_self]
    rw [hhp_eq] at hloop
    dsimp only at hloop
    simp only [popUpToModel, hlook]
    cases htail : popUpToTail pred inclusive m head with
    | none =>
      simp only [popUpToTail] at htail
      cases hw : popUpToWalk pred m head with
      | none =>
        simp only [popUpToTail, hw] at hloop
        exact hloop
      | some p =>
        rcases p with ⟨m1, target⟩
        simp only [hw] at htail
        cases inclusive with
        | false => simp at htail
        | true =>
          simp only [↓reduceIte] at htail ⊢
          cases hpv : target.previous with
          | none =>
            simp only [popUpToTail, hw, ↓reduceIte, hpv] at hloop
            exact hloop
          | some prev => simp [hpv] at htail
    | some p =>
      rcases p with ⟨m', resId⟩
      simp only [popUpToTail] at htail
      cases hw : popUpToWalk pred m head with
      | none => simp [hw] at htail
      | some p1 =>
        rcases p1 with ⟨m1, target⟩
        simp only [hw] at htail
        cases inclusive with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at htail ⊢
          rcases htail with ⟨rfl, rfl⟩
          simp only [popUpToTail, hw, Bool.false_eq_true, ↓reduceIte] at hloop
          exact hloop
        | true =>
          simp only [↓reduceIte] at htail ⊢
          cases hpv : target.previous with
          | none => simp [hpv] at htail
          | some prev =>
            simp only [hpv, Option.some.injEq, Prod.mk.injEq] at htail
            rcases htail with ⟨rfl, rfl⟩
            simp only [popUpToTail, hw, ↓reduceIte, hpv] at hloop
            exact hloop

theorem popUpTo_default_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (predCid : Nat) (pred : BackstackEntry NavValue → Bool)
    (inclusiveArg : Bool) (mask : UInt32)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hpred : IsEntryPredClosure resolveProg d subFuel hp.closures predCid pred)
    (hsf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ subFuel | none => 20 ≤ subFuel) :
    let effectiveInclusive := if (mask &&& 4) != 0 then false else inclusiveArg
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef predCid)), (3, .i32 (if inclusiveArg then 1 else 0)),
       (4, .i32 mask), (5, .null)] hp jh
    match popUpToModel m curId pred effectiveInclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_popUpTo_default_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.closures = hp.closures ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_popUpTo_default_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_prog := hExt _ _ navProgLookup_popUpTo
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_default_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_default_prog, List.drop]
  nav_iload; rw [runJvmResFast_iconst, runJvmResFast_iand, runJvmResFast_ifeq_mask]
  by_cases hmask : ((mask &&& 4) == 0) = true
  · have hud : ((mask &&& 4) != 0) = false := by simp [bne, hmask]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    dsimp only [BackstackNavigationKt_popUpTo_default_prog, List.drop]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpTo_equiv resolveProg d subFuel subFuel hd mid m curId predCid pred inclusiveArg
      hp jh hm hpred hsf
    cases hres : popUpToModel m curId pred inclusiveArg with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpTo hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubClo, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpTo hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubClo, hsubRand⟩
  · have hmaskf : ((mask &&& 4) == 0) = false := Bool.eq_false_iff.mpr hmask
    have hud : ((mask &&& 4) != 0) = true := by simp [bne, hmaskf]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    rw [runJvmResFast_iconst, runJvmResFast_istore]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpTo_equiv resolveProg d subFuel subFuel hd mid m curId predCid pred false
      hp jh hm hpred hsf
    cases hres : popUpToModel m curId pred false with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpTo hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubClo, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpTo hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubClo, hsubRand⟩

theorem popUpTo_1_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId targetId : EntryId) (inclusive : Bool)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hsf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ subFuel | none => 20 ≤ subFuel) :
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.uuid targetId)), (3, .i32 (if inclusive then 1 else 0))] hp jh
    match popUpToIdModel m curId targetId inclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_popUpTo_1_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 2) subFuel) fuel BackstackNavigationKt_popUpTo_1_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_prog := hExt _ _ navProgLookup_popUpTo
  have hsf10 : 10 ≤ subFuel := by
    cases hlook : mapLookup m curId with
    | none => simp [hlook] at hsf; omega
    | some head =>
      simp [hlook] at hsf
      have : 1 ≤ head.depth := by cases head <;> simp [BackstackEntry.depth] <;> omega
      omega
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_1_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_1_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid targetId)) rfl]
  nav_aload; nav_aload; nav_aload
  rw [runJvmResFast_invokedynamic_bsm (hbsm := bsm_lambda2) (htags := tags_uuid_len1)]
  dsimp only [allocClosure]
  nav_iload
  let lamTag :=
    "BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z"
  let hp1 := { hp with closures := hp.closures.push (.bytecode lamTag [.ext (.uuid targetId)] true) }
  have hcid : hp1.closures[hp.closures.size]? =
      some (.bytecode lamTag [.ext (.uuid targetId)] true) := by
    simp [hp1]
  have hpred := bytecode_lambda2_closure_spec resolveProg d subFuel hd hsf10 hExt hp1.closures
    hp.closures.size targetId hcid
  have hm1 : hp1.maps[mid]? = some m := hm
  have hsub := popUpTo_equiv resolveProg d subFuel subFuel hd mid m curId hp.closures.size
    (fun e => e.id == targetId) inclusive hp1 jh hm1 hpred hsf
  cases hres : popUpToIdModel m curId targetId inclusive with
  | error err =>
    have hres' : popUpToModel m curId (fun e => e.id == targetId) inclusive = .error err := hres
    rw [hres'] at hsub
    dsimp only at hsub ⊢
    rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
      ptags_popUpTo rfl rfl fntag_popUpTo hprog hsub]
  | ok m' resId =>
    have hres' : popUpToModel m curId (fun e => e.id == targetId) inclusive = .ok m' resId := hres
    rw [hres'] at hsub
    dsimp only at hsub ⊢
    obtain ⟨subEnd, hcall, hsubJh, hsubMaps, _, hsubRand⟩ := hsub
    rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
      ptags_popUpTo rfl rfl fntag_popUpTo hprog hcall rfl rfl]
    rw [runJvmResFast_areturn_nav]
    exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

theorem popUpTo_default_1_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId targetId : EntryId)
    (inclusiveArg : Bool) (mask : UInt32)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hsf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ subFuel | none => 20 ≤ subFuel) :
    let effectiveInclusive := if (mask &&& 4) != 0 then false else inclusiveArg
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.uuid targetId)), (3, .i32 (if inclusiveArg then 1 else 0)),
       (4, .i32 mask), (5, .null)] hp jh
    match popUpToIdModel m curId targetId effectiveInclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_popUpTo_default_1_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_popUpTo_default_1_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_1_prog := hExt _ _ navProgLookup_popUpTo1
  have hsf20 : 20 ≤ subFuel := by
    cases hlook : mapLookup m curId with
    | none => simp [hlook] at hsf; omega
    | some head =>
      simp [hlook] at hsf
      have : 1 ≤ head.depth := by cases head <;> simp [BackstackEntry.depth] <;> omega
      omega
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpTo_default_1_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpTo_default_1_prog, List.drop]
  nav_iload; rw [runJvmResFast_iconst, runJvmResFast_iand, runJvmResFast_ifeq_mask]
  by_cases hmask : ((mask &&& 4) == 0) = true
  · have hud : ((mask &&& 4) != 0) = false := by simp [bne, hmask]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    dsimp only [BackstackNavigationKt_popUpTo_default_1_prog, List.drop]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpTo_1_equiv resolveProg d subFuel subFuel hd hsf20 hExt mid m curId targetId
      inclusiveArg hp jh hm hsf
    cases hres : popUpToIdModel m curId targetId inclusiveArg with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo1 rfl rfl fntag_popUpTo1 hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo1 rfl rfl fntag_popUpTo1 hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩
  · have hmaskf : ((mask &&& 4) == 0) = false := Bool.eq_false_iff.mpr hmask
    have hud : ((mask &&& 4) != 0) = true := by simp [bne, hmaskf]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    rw [runJvmResFast_iconst, runJvmResFast_istore]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpTo_1_equiv resolveProg d subFuel subFuel hd hsf20 hExt mid m curId targetId
      false hp jh hm hsf
    cases hres : popUpToIdModel m curId targetId false with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo1 rfl rfl fntag_popUpTo1 hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo1 rfl rfl fntag_popUpTo1 hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

theorem popUpToValue_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (predCid : Nat) (pred : NavValue → Bool) (inclusive : Bool)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hpred : hp.closures[predCid]? = some (mkValuePredClosure pred))
    (hsf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ subFuel | none => 20 ≤ subFuel) :
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef predCid)), (3, .i32 (if inclusive then 1 else 0))] hp jh
    match popUpToValueModel m curId pred inclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_popUpToValue_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 3) subFuel) fuel BackstackNavigationKt_popUpToValue_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.popUpTo:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpTo_prog := hExt _ _ navProgLookup_popUpTo
  have hsf12 : 12 ≤ subFuel := by
    cases hlook : mapLookup m curId with
    | none => simp [hlook] at hsf; omega
    | some head =>
      simp [hlook] at hsf
      have : 1 ≤ head.depth := by cases head <;> simp [BackstackEntry.depth] <;> omega
      omega
  have hlt_pred : predCid < hp.closures.size := (Array.getElem?_eq_some_iff.mp hpred).1
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpToValue_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpToValue_prog, List.drop]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.mapRef mid)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.uuid curId)) rfl]
  nav_aload; rw [runJvmResFast_ldcStr, runJvmResFast_checkNotNullParam (v := .ext (.closureRef predCid)) rfl]
  nav_aload; nav_aload; nav_aload
  rw [runJvmResFast_invokedynamic_bsm (hbsm := bsm_lambda3) (htags := tags_fn1_len1)]
  dsimp only [allocClosure]
  nav_iload
  let lamTag :=
    "BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z"
  let hp1 := { hp with closures := hp.closures.push (.bytecode lamTag [.ext (.closureRef predCid)] true) }
  have hcid : hp1.closures[hp.closures.size]? =
      some (.bytecode lamTag [.ext (.closureRef predCid)] true) := by
    simp [hp1]
  have hpred1_clo : hp1.closures[predCid]? = some (mkValuePredClosure pred) := by
    simpa [hp1, Array.getElem?_push, Nat.ne_of_lt hlt_pred] using hpred
  have hpred1 : IsValuePredClosure resolveProg d subFuel hp1.closures predCid pred :=
    host_valuePredClosure_spec resolveProg d subFuel hpred1_clo
  have hlam3 := bytecode_lambda3_closure_spec resolveProg d subFuel hd hsf12 hExt hp1.closures
    hp.closures.size predCid pred hpred1 hcid
  have hm1 : hp1.maps[mid]? = some m := hm
  have hsub := popUpTo_equiv resolveProg (d + 1) subFuel subFuel (by omega) mid m curId
    hp.closures.size (fun e => pred e.value) inclusive hp1 jh hm1 hlam3 hsf
  cases hres : popUpToValueModel m curId pred inclusive with
  | error err =>
    have hres' : popUpToModel m curId (fun e => pred e.value) inclusive = .error err := hres
    rw [hres'] at hsub
    dsimp only at hsub ⊢
    rw [runJvmResFast_invokeBackstackStatic_none "popUpTo"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
      ptags_popUpTo rfl rfl fntag_popUpTo hprog hsub]
  | ok m' resId =>
    have hres' : popUpToModel m curId (fun e => pred e.value) inclusive = .ok m' resId := hres
    rw [hres'] at hsub
    dsimp only at hsub ⊢
    obtain ⟨subEnd, hcall, hsubJh, hsubMaps, _, hsubRand⟩ := hsub
    rw [runJvmResFast_invokeBackstackStatic_some "popUpTo"
      "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
      ptags_popUpTo rfl rfl fntag_popUpTo hprog hcall rfl rfl]
    rw [runJvmResFast_areturn_nav]
    exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

theorem popUpToValue_default_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (hExt : ExtendsNavProgs resolveProg)
    (mid : Nat) (m : BackstackMap NavValue) (curId : EntryId)
    (predCid : Nat) (pred : NavValue → Bool) (inclusiveArg : Bool) (mask : UInt32)
    (hp : NavHeap) (jh : Jvm.JvmHeap NavExt)
    (hm : hp.maps[mid]? = some m)
    (hpred : hp.closures[predCid]? = some (mkValuePredClosure pred))
    (hsf : match mapLookup m curId with | some head => 26 * head.depth + 20 ≤ subFuel | none => 20 ≤ subFuel) :
    let effectiveInclusive := if (mask &&& 4) != 0 then false else inclusiveArg
    let st0 := initNavJvmState
      [(0, .ext (.mapRef mid)), (1, .ext (.uuid curId)),
       (2, .ext (.closureRef predCid)), (3, .i32 (if inclusiveArg then 1 else 0)),
       (4, .i32 mask), (5, .null)] hp jh
    match popUpToValueModel m curId pred effectiveInclusive with
    | .ok m' resId =>
      ∃ endSt,
        Jvm.runJvmRes (mkNavHooks resolveProg (d + 4) subFuel) fuel BackstackNavigationKt_popUpToValue_default_prog st0 =
          some (.ext (.uuid resId), endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.maps[mid]? = some m' ∧
        endSt.heap.nextRandomId = hp.nextRandomId
    | .error _ =>
      Jvm.runJvmRes (mkNavHooks resolveProg (d + 4) subFuel) fuel BackstackNavigationKt_popUpToValue_default_prog st0 = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg
      "BackstackNavigationKt.popUpToValue:(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;" =
      some BackstackNavigationKt_popUpToValue_prog := hExt _ _ navProgLookup_popUpToValue
  have hsf20 : 20 ≤ subFuel := by
    cases hlook : mapLookup m curId with
    | none => simp [hlook] at hsf; omega
    | some head =>
      simp [hlook] at hsf
      have : 1 ≤ head.depth := by cases head <;> simp [BackstackEntry.depth] <;> omega
      omega
  dsimp only
  rw [navRunJvmRes_eq_fast BackstackNavigationKt_popUpToValue_default_prog (by decide)]
  dsimp only [initNavJvmState, Jvm.initJvmState, BackstackNavigationKt_popUpToValue_default_prog, List.drop]
  nav_iload; rw [runJvmResFast_iconst, runJvmResFast_iand, runJvmResFast_ifeq_mask]
  by_cases hmask : ((mask &&& 4) == 0) = true
  · have hud : ((mask &&& 4) != 0) = false := by simp [bne, hmask]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    dsimp only [BackstackNavigationKt_popUpToValue_default_prog, List.drop]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpToValue_equiv resolveProg d subFuel subFuel hd hsf20 hExt mid m curId
      predCid pred inclusiveArg hp jh hm hpred hsf
    cases hres : popUpToValueModel m curId pred inclusiveArg with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      rw [runJvmResFast_invokeBackstackStatic_none "popUpToValue"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpToValue hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpToValue"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpToValue hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩
  · have hmaskf : ((mask &&& 4) == 0) = false := Bool.eq_false_iff.mpr hmask
    have hud : ((mask &&& 4) != 0) = true := by simp [bne, hmaskf]
    simp only [hmask, ↓reduceIte, hud, Bool.false_eq_true]
    rw [runJvmResFast_iconst, runJvmResFast_istore]
    nav_aload; nav_aload; nav_aload; nav_iload
    have hsub := popUpToValue_equiv resolveProg d subFuel subFuel hd hsf20 hExt mid m curId
      predCid pred false hp jh hm hpred hsf
    cases hres : popUpToValueModel m curId pred false with
    | error err =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      rw [runJvmResFast_invokeBackstackStatic_none "popUpToValue"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpToValue hprog hsub]
    | ok m' resId =>
      rw [hres] at hsub
      dsimp only at hsub ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hsub
      obtain ⟨subEnd, hcall, hsubJh, hsubMaps, hsubRand⟩ := hsub
      rw [runJvmResFast_invokeBackstackStatic_some "popUpToValue"
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;"
        ptags_popUpTo rfl rfl fntag_popUpToValue hprog hcall rfl rfl]
      rw [runJvmResFast_areturn_nav]
      exact ⟨_, rfl, hsubJh, hsubMaps, hsubRand⟩

end Navigation.KotlinJvmVerification
