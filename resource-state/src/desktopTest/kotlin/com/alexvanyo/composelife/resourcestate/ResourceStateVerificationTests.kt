/*
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
 */

package com.alexvanyo.composelife.resourcestate

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `ResourceState.kt` by lifting the actual compiled
 * `ResourceStateKt.class` JVM bytecode from the test runtime classpath into Lean 4 and proving theorems about that
 * real bytecode with `lake env lean`.
 */
class ResourceStateVerificationTests {
    @Test
    fun predicates_bytecode_partition_resource_states() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_resourceState_predicates_partition",
            leanBody = """
                |theorem real_resourceState_predicates_partition
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
                |    (hd : 1 ≤ d) (hf : 30 ≤ fuel)
                |    (r : Model.ResourceState RsVal) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
                |    (hclean : HasRsStaticsClean jh) :
                |    ∃ l s f : UInt32,
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |            ResourceState.RealJvmBytecode.ResourceStateKt_isLoading_prog
                |            (initRsJvmState [(0, .ext (.res r))] hp jh) = some (.i32 l, endSt) ∧
                |          endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |            ResourceState.RealJvmBytecode.ResourceStateKt_isSuccess_prog
                |            (initRsJvmState [(0, .ext (.res r))] hp jh) = some (.i32 s, endSt) ∧
                |          endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |            ResourceState.RealJvmBytecode.ResourceStateKt_isFailure_prog
                |            (initRsJvmState [(0, .ext (.res r))] hp jh) = some (.i32 f, endSt) ∧
                |          endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      l + s + f = 1 ∧
                |      (l = 1 ↔ r = .loading) ∧
                |      (s = 1 ↔ ∃ v, r = .success v) ∧
                |      (f = 1 ↔ ∃ t, r = .failure t) := by
                |  have hL : ResourceState.RealJvmBytecode.ResourceStateKt_isLoading_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_isLoading_prog := rfl
                |  have hS : ResourceState.RealJvmBytecode.ResourceStateKt_isSuccess_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_isSuccess_prog := rfl
                |  have hF : ResourceState.RealJvmBytecode.ResourceStateKt_isFailure_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_isFailure_prog := rfl
                |  rw [hL, hS, hF]
                |  refine ⟨_, _, _,
                |    isLoading_equiv resolveProg d subFuel fuel hd hf r hp jh hclean,
                |    isSuccess_equiv resolveProg d subFuel fuel hd hf r hp jh hclean,
                |    isFailure_equiv resolveProg d subFuel fuel hd hf r hp jh hclean, ?_⟩
                |  cases r <;> simp [Model.ResourceState.isLoading, Model.ResourceState.isSuccess,
                |    Model.ResourceState.isFailure]
            """.trimMargin(),
        )
    }

    @Test
    fun map_and_flatMap_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_map_flatMap_implement_model",
            leanBody = """
                |theorem real_map_flatMap_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
                |    (hd : 1 ≤ d) (hf : 45 ≤ fuel)
                |    (r : Model.ResourceState RsVal) (f g : RsVal → RsVal)
                |    (k : RsVal → Model.ResourceState RsVal) (cidF cidG cidGF cidK : Nat)
                |    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) (hclean : HasRsStaticsClean jh)
                |    (hclF : hp.closures[cidF]? =
                |      some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => (f x).toJvmVal))))
                |    (hclG : hp.closures[cidG]? =
                |      some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => (g x).toJvmVal))))
                |    (hclGF : hp.closures[cidGF]? =
                |      some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => (g (f x)).toJvmVal))))
                |    (hclK : hp.closures[cidK]? =
                |      some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => .ext (.res (k x)))))) :
                |    (∃ e1 e2 e3,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceState.RealJvmBytecode.ResourceStateKt_map_prog
                |          (initRsJvmState [(0, .ext (.res r)), (1, .ext (.closureRef cidF))] hp jh) =
                |        some (.ext (.res (r.map f)), e1) ∧
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceState.RealJvmBytecode.ResourceStateKt_map_prog
                |          (initRsJvmState [(0, .ext (.res (r.map f))), (1, .ext (.closureRef cidG))]
                |            e1.heap e1.jvmHeap) =
                |        some (.ext (.res ((r.map f).map g)), e2) ∧
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceState.RealJvmBytecode.ResourceStateKt_map_prog
                |          (initRsJvmState [(0, .ext (.res r)), (1, .ext (.closureRef cidGF))] hp jh) =
                |        some (.ext (.res ((r.map f).map g)), e3)) ∧
                |    ∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceState.RealJvmBytecode.ResourceStateKt_flatMap_prog
                |          (initRsJvmState [(0, .ext (.res r)), (1, .ext (.closureRef cidK))] hp jh) =
                |        some (.ext (.res (r.flatMap k)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
                |  have hM : ResourceState.RealJvmBytecode.ResourceStateKt_map_prog = ResourceState.KotlinJvmBytecode.ResourceStateKt_map_prog := rfl
                |  have hFM : ResourceState.RealJvmBytecode.ResourceStateKt_flatMap_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_flatMap_prog := rfl
                |  rw [hM, hFM]
                |  obtain ⟨e1, h1, hj1, hh1⟩ := map_equiv resolveProg d subFuel fuel hd hf r f cidF hp jh hclean hclF
                |  obtain ⟨e2, h2, -, -⟩ := map_equiv resolveProg d subFuel fuel hd hf (r.map f) g cidG
                |    e1.heap e1.jvmHeap (hj1 ▸ hclean) (hh1 ▸ hclG)
                |  obtain ⟨e3, h3, -, -⟩ := map_equiv resolveProg d subFuel fuel hd hf r (fun x => g (f x)) cidGF
                |    hp jh hclean hclGF
                |  refine ⟨⟨e1, e2, e3, h1, h2, ?_⟩,
                |    flatMap_equiv resolveProg d subFuel fuel hd hf r k cidK hp jh hclean hclK⟩
                |  rw [Model.resourceState_map_comp]
                |  exact h3
            """.trimMargin(),
        )
    }

    @Test
    fun combine_bytecode_overloads_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_combine_overloads_implement_model",
            leanBody = """
                |theorem real_combine_overloads_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat) (hd : 1 ≤ d)
                |    (r1 r2 r3 : Model.ResourceState RsVal)
                |    (f2 : RsVal → RsVal → RsVal) (f3 : RsVal → RsVal → RsVal → RsVal)
                |    (cid2 cid3 : Nat) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
                |    (hclean : HasRsStaticsClean jh)
                |    (hcl2 : hp.closures[cid2]? = some (.fn2 fun a b =>
                |      match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b with
                |      | some va, some vb => some (f2 va vb).toJvmVal
                |      | _, _ => none))
                |    (hcl3 : hp.closures[cid3]? = some (.fn3 fun a b c =>
                |      match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b, RsVal.ofJvmVal? c with
                |      | some va, some vb, some vc => some (f3 va vb vc).toJvmVal
                |      | _, _, _ => none))
                |    (states : List (Model.ResourceState RsVal)) (hlen : states.length < 2 ^ 31)
                |    (fN : List RsVal → RsVal) (cidN arrAddr : Nat)
                |    (hArr : jh.get? arrAddr =
                |      some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
                |        (states.map fun r => (.ext (.res r) : JvmVal)).toArray))
                |    (hclN : hp.closures[cidN]? = some (.listFn1 fN)) :
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 400 ResourceState.RealJvmBytecode.ResourceStateKt_combine_prog
                |          (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.closureRef cid2))]
                |            hp jh) =
                |        some (.ext (.res (Model.combine2 r1 r2 f2)), endSt) ∧
                |      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 500 ResourceState.RealJvmBytecode.ResourceStateKt_combine_1_prog
                |          (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.res r3)),
                |            (3, .ext (.closureRef cid3))] hp jh) =
                |        some (.ext (.res (Model.combine3 r1 r2 r3 f3)), endSt) ∧
                |      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) (180 + 68 * states.length)
                |          ResourceState.RealJvmBytecode.ResourceStateKt_combine_2_prog
                |          (initRsJvmState [(0, .heapRef arrAddr), (1, .ext (.closureRef cidN))] hp jh) =
                |        some (.ext (.res (Model.combineMany states fN)), endSt) ∧
                |      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp) := by
                |  have hC2 : ResourceState.RealJvmBytecode.ResourceStateKt_combine_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_combine_prog := rfl
                |  have hC3 : ResourceState.RealJvmBytecode.ResourceStateKt_combine_1_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_combine_1_prog := rfl
                |  have hCN : ResourceState.RealJvmBytecode.ResourceStateKt_combine_2_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_combine_2_prog := rfl
                |  rw [hC2, hC3, hCN]
                |  exact ⟨combine2_equiv resolveProg d subFuel 400 hd (Nat.le_refl _) r1 r2 f2 cid2 hp jh hclean hcl2,
                |    combine3_equiv resolveProg d subFuel 500 hd (Nat.le_refl _) r1 r2 r3 f3 cid3 hp jh hclean hcl3,
                |    combineMany_equiv resolveProg d subFuel _ hd states hlen (Nat.le_refl _) fN cidN arrAddr hp jh
                |      hclean hArr hclN⟩
            """.trimMargin(),
        )
    }

    @Test
    fun combine_bytecode_two_arg_overload_agrees_with_vararg_overload() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_combine_two_arg_agrees_with_vararg",
            leanBody = """
                |theorem real_combine_two_arg_agrees_with_vararg
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat) (hd : 1 ≤ d)
                |    (r1 r2 : Model.ResourceState RsVal) (t : List RsVal → RsVal) (cid2 cidN arrAddr : Nat)
                |    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) (hclean : HasRsStaticsClean jh)
                |    (hArr : jh.get? arrAddr =
                |      some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
                |        #[.ext (.res r1), .ext (.res r2)]))
                |    (hcl2 : hp.closures[cid2]? = some (.fn2 fun a b =>
                |      match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b with
                |      | some va, some vb => some (t [va, vb]).toJvmVal
                |      | _, _ => none))
                |    (hclN : hp.closures[cidN]? = some (.listFn1 t)) :
                |    ∃ res e2 eN,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 400 ResourceState.RealJvmBytecode.ResourceStateKt_combine_prog
                |          (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.closureRef cid2))]
                |            hp jh) =
                |        some (.ext (.res res), e2) ∧
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 400 ResourceState.RealJvmBytecode.ResourceStateKt_combine_2_prog
                |          (initRsJvmState [(0, .heapRef arrAddr), (1, .ext (.closureRef cidN))] hp jh) =
                |        some (.ext (.res res), eN) ∧
                |      res = Model.combineMany [r1, r2] t := by
                |  have hC2 : ResourceState.RealJvmBytecode.ResourceStateKt_combine_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_combine_prog := rfl
                |  have hCN : ResourceState.RealJvmBytecode.ResourceStateKt_combine_2_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_combine_2_prog := rfl
                |  rw [hC2, hCN]
                |  obtain ⟨e2, h2, -, -⟩ := combine2_equiv resolveProg d subFuel 400 hd (Nat.le_refl _) r1 r2
                |    (fun a b => t [a, b]) cid2 hp jh hclean hcl2
                |  obtain ⟨eN, hN, -, -⟩ := combineMany_equiv resolveProg d subFuel 400 hd [r1, r2]
                |    (by simp) (by simp) t cidN arrAddr hp jh hclean hArr hclN
                |  rw [Model.combine2_matches_combineMany] at h2
                |  exact ⟨_, e2, eN, h2, hN, rfl⟩
            """.trimMargin(),
        )
    }

    @Test
    fun flow_operators_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_flow_operators_implement_model",
            leanBody = """
                |theorem real_flow_operators_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsRsProgs resolveProg)
                |    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsub : 20 ≤ subFuel) (hf : 40 ≤ fuel)
                |    (tr : Model.FlowTrace (Model.ResourceState RsVal)) (values : Model.FlowTrace RsVal)
                |    (changed : UInt32) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) (hclean : HasRsStaticsClean jh) :
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |          ResourceState.RealJvmBytecode.ResourceStateKt_successes_prog
                |          (initRsJvmState [(0, .ext (.resFlow tr))] hp jh) =
                |        some (.ext (.resFlow (Model.successesFlow tr)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∀ headRes, Model.firstSuccessModel tr = some headRes →
                |      ∃ endSt,
                |        Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |            ResourceState.RealJvmBytecode.ResourceStateKt_firstSuccess_prog
                |            (initRsJvmState [(0, .ext (.resFlow tr)), (1, .ext .continuation)] hp jh) =
                |          some (.ext (.res headRes), endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |          ResourceState.RealJvmBytecode.ResourceStateKt_asResourceState_prog
                |          (initRsJvmState [(0, .ext (.flow values))] hp jh) =
                |        some (.ext (.resFlow (Model.asResourceStateFlow values)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel
                |          ResourceState.RealJvmBytecode.ResourceStateKt_collectAsState_prog
                |          (initRsJvmState [(0, .ext (.resFlow tr)), (1, .ext .composer), (2, .i32 changed)] hp jh) =
                |        some (.ext (.composeState (Model.collectAsStateModel tr)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have hS : ResourceState.RealJvmBytecode.ResourceStateKt_successes_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_successes_prog := rfl
                |  have hFS : ResourceState.RealJvmBytecode.ResourceStateKt_firstSuccess_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_firstSuccess_prog := rfl
                |  have hA : ResourceState.RealJvmBytecode.ResourceStateKt_asResourceState_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_asResourceState_prog := rfl
                |  have hC : ResourceState.RealJvmBytecode.ResourceStateKt_collectAsState_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_collectAsState_prog := rfl
                |  rw [hS, hFS, hA, hC]
                |  exact ⟨successes_equiv resolveProg d subFuel fuel (by omega) (by omega) tr hp jh,
                |    fun headRes hhead => firstSuccess_equiv resolveProg hext d subFuel fuel hd hsub (by omega)
                |      tr headRes hhead hp jh,
                |    asResourceState_equiv resolveProg d subFuel fuel (by omega) (by omega) values hp jh,
                |    collectAsState_equiv resolveProg d subFuel fuel (by omega) hf tr changed hp jh hclean⟩
            """.trimMargin(),
        )
    }

    @Test
    fun asResourceState_then_collectAsState_bytecode_surfaces_terminal_failure() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_asResourceState_collectAsState_surfaces_failure",
            leanBody = """
                |theorem real_asResourceState_collectAsState_surfaces_failure
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat) (hd : 1 ≤ d)
                |    (elems : List RsVal) (t : Model.ThrowableModel) (changed : UInt32)
                |    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) (hclean : HasRsStaticsClean jh) :
                |    ∃ flow e1 e2,
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 30
                |          ResourceState.RealJvmBytecode.ResourceStateKt_asResourceState_prog
                |          (initRsJvmState [(0, .ext (.flow { emissions := elems, terminalFailure? := some t }))]
                |            hp jh) =
                |        some (.ext (.resFlow flow), e1) ∧
                |      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) 40
                |          ResourceState.RealJvmBytecode.ResourceStateKt_collectAsState_prog
                |          (initRsJvmState [(0, .ext (.resFlow flow)), (1, .ext .composer), (2, .i32 changed)]
                |            e1.heap e1.jvmHeap) =
                |        some (.ext (.composeState (.failure t)), e2) := by
                |  have hA : ResourceState.RealJvmBytecode.ResourceStateKt_asResourceState_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_asResourceState_prog := rfl
                |  have hC : ResourceState.RealJvmBytecode.ResourceStateKt_collectAsState_prog =
                |      ResourceState.KotlinJvmBytecode.ResourceStateKt_collectAsState_prog := rfl
                |  rw [hA, hC]
                |  obtain ⟨e1, h1, hj1, -⟩ := asResourceState_equiv resolveProg d subFuel 30 hd (Nat.le_refl _)
                |    { emissions := elems, terminalFailure? := some t } hp jh
                |  obtain ⟨e2, h2, -, -⟩ := collectAsState_equiv resolveProg d subFuel 40 hd (Nat.le_refl _)
                |    (Model.asResourceStateFlow { emissions := elems, terminalFailure? := some t }) changed
                |    e1.heap e1.jvmHeap (hj1 ▸ hclean)
                |  have hModel : Model.collectAsStateModel
                |      (Model.asResourceStateFlow { emissions := elems, terminalFailure? := some t }) =
                |      (.failure t : Model.ResourceState RsVal) := by
                |    rw [Model.asResourceStateFlow_catches_failure]
                |    simp [Model.collectAsStateModel]
                |  rw [hModel] at h2
                |  exact ⟨_, e1, e2, h1, h2⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "resource-state",
            classResourcePath = "com/alexvanyo/composelife/resourcestate/ResourceStateKt.class",
            realBytecodeNamespace = "ResourceState.RealJvmBytecode",
            instrType = "ResourceState.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "ResourceStateKt_isLoading_prog",
                "ResourceStateKt_isSuccess_prog",
                "ResourceStateKt_isFailure_prog",
                "ResourceStateKt_successes_prog",
                "ResourceStateKt_firstSuccess_prog",
                "ResourceStateKt_map_prog",
                "ResourceStateKt_flatMap_prog",
                "ResourceStateKt_combine_prog",
                "ResourceStateKt_combine_1_prog",
                "ResourceStateKt_combine_2_prog",
                "ResourceStateKt_asResourceState_prog",
                "ResourceStateKt_collectAsState_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.ResourceStateModel",
                "theorems.ResourceStateModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.ResourceState",
            ),
            defaultOpens = listOf(
                "ResourceState",
                "ResourceState.JvmVerification",
                "ResourceState.KotlinJvmVerification",
            ),
        )
    }
}
