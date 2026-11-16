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

package com.alexvanyo.composelife.navigation

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

class BackstackNavigationVerificationTests {
    private val verificationSpec = JvmBytecodeVerificationSpec(
        moduleDirName = "navigation",
        classResourcePath = "com/alexvanyo/composelife/navigation/BackstackNavigationKt.class",
        semanticsImport = "JvmSemantics",
        realBytecodeNamespace = "Navigation.RealJvmBytecode",
        instrType = "Navigation.JvmVerification.JvmInstr",
        requiredProgs = listOf(
            "BackstackNavigationKt_popUpTo_prog",
            "BackstackNavigationKt_popUpTo_default_prog",
            "BackstackNavigationKt_popUpTo_1_prog",
            "BackstackNavigationKt_popUpTo_default_1_prog",
            "BackstackNavigationKt_popUpToValue_prog",
            "BackstackNavigationKt_popUpToValue_default_prog",
            "BackstackNavigationKt_navigate_prog",
            "BackstackNavigationKt_navigate_default_prog",
            "BackstackNavigationKt_navigate_1_prog",
            "BackstackNavigationKt_navigate_default_1_prog",
            "BackstackNavigationKt_popBackstack_prog",
            "BackstackNavigationKt_popUpTo_lambda_2_prog",
            "BackstackNavigationKt_popUpTo_lambda_3_prog",
            "BackstackNavigationKt_navigate_lambda_0_prog",
        ),
        defaultImports = listOf(
            "models.BackstackNavigationModel",
            "proofs.KotlinJvmEquiv.BackstackNavigation",
        ),
        defaultOpens = listOf(
            "Navigation",
            "Navigation.Model",
            "Navigation.JvmVerification",
            "Navigation.KotlinJvmVerification",
        ),
    )

    @Test
    fun navigate_and_popBackstack_roundtrip_verified_against_live_bytecode() {
        verificationSpec.verifyTheorem(
            ownerClass = BackstackNavigationVerificationTests::class.java,
            theoremName = "live_navigate_popBackstack_roundtrip",
            leanBody = """
              theorem live_navigate_popBackstack_roundtrip :
                  (RealJvmBytecode.BackstackNavigationKt_navigate_prog = KotlinJvmBytecode.BackstackNavigationKt_navigate_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_navigate_default_prog = KotlinJvmBytecode.BackstackNavigationKt_navigate_default_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_navigate_1_prog = KotlinJvmBytecode.BackstackNavigationKt_navigate_1_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_navigate_default_1_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_navigate_default_1_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_navigate_lambda_0_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_navigate_lambda_0_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popBackstack_prog = KotlinJvmBytecode.BackstackNavigationKt_popBackstack_prog) ∧
                  (let rootEntry : BackstackEntry NavValue := .root (.int 10) 1
                   let m0 := mapPut ([] : BackstackMap NavValue) 1 rootEntry
                   let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 100 }
                   ∃ end1 end2,
                     Jvm.runJvmRes (mkNavHooks navProgLookup 3 45) 25
                         RealJvmBytecode.BackstackNavigationKt_navigate_1_prog
                         (initNavJvmState
                           [(0, .ext (.mapRef 0)), (1, .ext (.uuid 1)),
                            (2, (.int 20 : NavValue).toJvmVal), (3, .ext (.uuid 2))]
                           hp0 {}) =
                       some (.ext (.uuid 2), end1) ∧
                     Jvm.runJvmRes (mkNavHooks navProgLookup 1 45) 40
                         RealJvmBytecode.BackstackNavigationKt_popBackstack_prog
                         (initNavJvmState
                           [(0, .ext (.mapRef 0)), (1, .ext (.uuid 2))]
                           end1.heap end1.jvmHeap) =
                       some (.ext (.uuid 1), end2) ∧
                     end2.heap.maps[0]? = some m0 ∧
                     end2.heap.nextRandomId = 100) ∧
                  (let rootEntry : BackstackEntry NavValue := .root (.int 10) 1
                   let m0 := mapPut ([] : BackstackMap NavValue) 1 rootEntry
                   let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 100 }
                   ∃ end3,
                     Jvm.runJvmRes (mkNavHooks navProgLookup 4 45) 20
                         RealJvmBytecode.BackstackNavigationKt_navigate_default_1_prog
                         (initNavJvmState
                           [(0, .ext (.mapRef 0)), (1, .ext (.uuid 1)),
                            (2, (.int 20 : NavValue).toJvmVal), (3, .ext (.uuid 0)),
                            (4, .i32 4), (5, .null)]
                           hp0 {}) =
                       some (.ext (.uuid 100), end3) ∧
                     end3.heap.nextRandomId = 101) := by
                have hNavProg : RealJvmBytecode.BackstackNavigationKt_navigate_prog = KotlinJvmBytecode.BackstackNavigationKt_navigate_prog :=
                  rfl
                have hNavDefProg :
                    RealJvmBytecode.BackstackNavigationKt_navigate_default_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_navigate_default_prog := rfl
                have hNav1Prog :
                    RealJvmBytecode.BackstackNavigationKt_navigate_1_prog = KotlinJvmBytecode.BackstackNavigationKt_navigate_1_prog := rfl
                have hNavDef1Prog :
                    RealJvmBytecode.BackstackNavigationKt_navigate_default_1_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_navigate_default_1_prog := rfl
                have hNavLam0Prog :
                    RealJvmBytecode.BackstackNavigationKt_navigate_lambda_0_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_navigate_lambda_0_prog := rfl
                have hPopProg :
                    RealJvmBytecode.BackstackNavigationKt_popBackstack_prog = KotlinJvmBytecode.BackstackNavigationKt_popBackstack_prog := rfl
                refine ⟨hNavProg, hNavDefProg, hNav1Prog, hNavDef1Prog, hNavLam0Prog, hPopProg, ?_, ?_⟩
                · dsimp only
                  let rootEntry : BackstackEntry NavValue := .root (.int 10) 1
                  let m0 := mapPut ([] : BackstackMap NavValue) 1 rootEntry
                  let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 100 }
                  let m1 := mapPut m0 2 (.node (.int 20) rootEntry 2)
                  have hNavEq :
                      navigateValueModel m0 1 (.int 20) 2 = .ok m1 2 := rfl
                  have hNav := navigate_1_equiv navProgLookup 1 45 25 (by omega) (by omega) (by omega)
                    navProgLookup_extends 0 m0 1 (.int 20) 2 hp0 {} rfl
                  rw [hNavEq] at hNav
                  obtain ⟨end1, hrun1, hjh1, hm1, hrand1⟩ := hNav
                  have hPopEq : popBackstackModel m1 2 = .ok m0 1 := rfl
                  have hPop := popBackstack_equiv navProgLookup 1 45 40 (by omega) (by omega)
                    0 m1 2 end1.heap end1.jvmHeap hm1
                  rw [hPopEq] at hPop
                  obtain ⟨end2, hrun2, _, hm2, _, hrand2⟩ := hPop
                  rw [hNav1Prog, hPopProg]
                  refine ⟨end1, end2, hrun1, hrun2, hm2, ?_⟩
                  rw [hrand2, hrand1]
                · dsimp only
                  let rootEntry : BackstackEntry NavValue := .root (.int 10) 1
                  let m0 := mapPut ([] : BackstackMap NavValue) 1 rootEntry
                  let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 100 }
                  let m1 := mapPut m0 100 (.node (.int 20) rootEntry 100)
                  have hDef := navigate_default_1_equiv navProgLookup 1 45 20
                    (by omega) (by omega) (by omega) navProgLookup_extends
                    0 m0 1 (.int 20) 0 4 hp0 {} rfl rfl
                  have hEff : ((4 : UInt32) &&& 4 != 0) = true := by decide
                  have hModel : navigateValueModel m0 1 (.int 20) 100 = .ok m1 100 := rfl
                  simp only [hEff, ↓reduceIte] at hDef
                  rw [hModel] at hDef
                  obtain ⟨end3, hrun3, _, _, hrand3⟩ := hDef
                  rw [hNavDef1Prog]
                  exact ⟨end3, hrun3, hrand3⟩
            """.trimIndent(),
        )
    }

    @Test
    fun popBackstack_on_root_entry_traps_in_live_bytecode() {
        verificationSpec.verifyTheorem(
            ownerClass = BackstackNavigationVerificationTests::class.java,
            theoremName = "live_popBackstack_root_trap",
            leanBody = """
              theorem live_popBackstack_root_trap :
                  (RealJvmBytecode.BackstackNavigationKt_popBackstack_prog = KotlinJvmBytecode.BackstackNavigationKt_popBackstack_prog) ∧
                  (let m0 := mapPut ([] : BackstackMap NavValue) 1 (.root (.str "home") 1)
                   let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 10 }
                   Jvm.runJvmRes (mkNavHooks navProgLookup 1 45) 40
                       RealJvmBytecode.BackstackNavigationKt_popBackstack_prog
                       (initNavJvmState [(0, .ext (.mapRef 0)), (1, .ext (.uuid 1))] hp0 {}) =
                     none) ∧
                  (let m0 := mapPut ([] : BackstackMap NavValue) 1 (.root (.str "home") 1)
                   let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 10 }
                   Jvm.runJvmRes (mkNavHooks navProgLookup 1 45) 40
                       RealJvmBytecode.BackstackNavigationKt_popBackstack_prog
                       (initNavJvmState [(0, .ext (.mapRef 0)), (1, .ext (.uuid 99))] hp0 {}) =
                     none) := by
                have hPopProg :
                    RealJvmBytecode.BackstackNavigationKt_popBackstack_prog = KotlinJvmBytecode.BackstackNavigationKt_popBackstack_prog := rfl
                refine ⟨hPopProg, ?_, ?_⟩
                · dsimp only
                  let m0 := mapPut ([] : BackstackMap NavValue) 1 (.root (.str "home") 1)
                  let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 10 }
                  have hTrap := popBackstack_equiv navProgLookup 1 45 40 (by omega) (by omega)
                    0 m0 1 hp0 {} rfl
                  have hErr : popBackstackModel m0 1 = .error .popLastEntry := rfl
                  rw [hErr] at hTrap
                  rw [hPopProg]
                  exact hTrap
                · dsimp only
                  let m0 := mapPut ([] : BackstackMap NavValue) 1 (.root (.str "home") 1)
                  let hp0 : NavHeap := { maps := #[m0], closures := #[], nextRandomId := 10 }
                  have hTrap := popBackstack_equiv navProgLookup 1 45 40 (by omega) (by omega)
                    0 m0 99 hp0 {} rfl
                  have hErr : popBackstackModel m0 99 = .error .missingEntry := rfl
                  rw [hErr] at hTrap
                  rw [hPopProg]
                  exact hTrap
            """.trimIndent(),
        )
    }

    @Test
    fun popUpTo_slices_and_missing_target_trap_verified_against_live_bytecode() {
        verificationSpec.verifyTheorem(
            ownerClass = BackstackNavigationVerificationTests::class.java,
            theoremName = "live_popUpTo_slices_and_traps",
            leanBody = """
              theorem live_popUpTo_slices_and_traps :
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpTo_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_default_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpTo_default_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_1_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpTo_1_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_default_1_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_popUpTo_default_1_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpToValue_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpToValue_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpToValue_default_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_popUpToValue_default_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_lambda_2_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_popUpTo_lambda_2_prog) ∧
                  (RealJvmBytecode.BackstackNavigationKt_popUpTo_lambda_3_prog =
                    KotlinJvmBytecode.BackstackNavigationKt_popUpTo_lambda_3_prog) ∧
                  (let e1 : BackstackEntry NavValue := .root (.int 1) 1
                   let e2 : BackstackEntry NavValue := .node (.int 2) e1 2
                   let e3 : BackstackEntry NavValue := .node (.int 3) e2 3
                   let m3 := mapPut (mapPut (mapPut [] 1 e1) 2 e2) 3 e3
                   let m1 := mapPut [] 1 e1
                   let hp0 : NavHeap :=
                     { maps := #[m3], closures := #[mkValuePredClosure (fun v => v == .int 2)],
                       nextRandomId := 10 }
                   (∃ end1,
                     Jvm.runJvmRes (mkNavHooks navProgLookup 3 120) 20
                         RealJvmBytecode.BackstackNavigationKt_popUpTo_1_prog
                         (initNavJvmState
                           [(0, .ext (.mapRef 0)), (1, .ext (.uuid 3)),
                            (2, .ext (.uuid 1)), (3, .i32 0)]
                           hp0 {}) =
                       some (.ext (.uuid 1), end1) ∧
                     end1.heap.maps[0]? = some m1) ∧
                   (∃ end2,
                     Jvm.runJvmRes (mkNavHooks navProgLookup 4 120) 20
                         RealJvmBytecode.BackstackNavigationKt_popUpToValue_prog
                         (initNavJvmState
                           [(0, .ext (.mapRef 0)), (1, .ext (.uuid 3)),
                            (2, .ext (.closureRef 0)), (3, .i32 1)]
                           hp0 {}) =
                       some (.ext (.uuid 1), end2) ∧
                     end2.heap.maps[0]? = some m1) ∧
                   (Jvm.runJvmRes (mkNavHooks navProgLookup 3 120) 20
                       RealJvmBytecode.BackstackNavigationKt_popUpTo_1_prog
                       (initNavJvmState
                         [(0, .ext (.mapRef 0)), (1, .ext (.uuid 3)),
                          (2, .ext (.uuid 999)), (3, .i32 0)]
                         hp0 {}) = none) ∧
                   (Jvm.runJvmRes (mkNavHooks navProgLookup 3 120) 20
                       RealJvmBytecode.BackstackNavigationKt_popUpTo_1_prog
                       (initNavJvmState
                         [(0, .ext (.mapRef 0)), (1, .ext (.uuid 3)),
                          (2, .ext (.uuid 1)), (3, .i32 1)]
                         hp0 {}) = none)) := by
                have hP : RealJvmBytecode.BackstackNavigationKt_popUpTo_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpTo_prog := rfl
                have hPD :
                    RealJvmBytecode.BackstackNavigationKt_popUpTo_default_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_popUpTo_default_prog := rfl
                have hP1 : RealJvmBytecode.BackstackNavigationKt_popUpTo_1_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpTo_1_prog := rfl
                have hP1D :
                    RealJvmBytecode.BackstackNavigationKt_popUpTo_default_1_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_popUpTo_default_1_prog := rfl
                have hPV :
                    RealJvmBytecode.BackstackNavigationKt_popUpToValue_prog = KotlinJvmBytecode.BackstackNavigationKt_popUpToValue_prog := rfl
                have hPVD :
                    RealJvmBytecode.BackstackNavigationKt_popUpToValue_default_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_popUpToValue_default_prog := rfl
                have hL2 :
                    RealJvmBytecode.BackstackNavigationKt_popUpTo_lambda_2_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_popUpTo_lambda_2_prog := rfl
                have hL3 :
                    RealJvmBytecode.BackstackNavigationKt_popUpTo_lambda_3_prog =
                      KotlinJvmBytecode.BackstackNavigationKt_popUpTo_lambda_3_prog := rfl
                refine ⟨hP, hPD, hP1, hP1D, hPV, hPVD, hL2, hL3, ?_⟩
                dsimp only
                let e1 : BackstackEntry NavValue := .root (.int 1) 1
                let e2 : BackstackEntry NavValue := .node (.int 2) e1 2
                let e3 : BackstackEntry NavValue := .node (.int 3) e2 3
                let m3 := mapPut (mapPut (mapPut [] 1 e1) 2 e2) 3 e3
                let m1 := mapPut [] 1 e1
                let hp0 : NavHeap :=
                  { maps := #[m3], closures := #[mkValuePredClosure (fun v => v == .int 2)],
                    nextRandomId := 10 }
                have hLook3 : mapLookup m3 3 = some e3 := rfl
                have hsf :
                    (match mapLookup m3 3 with
                      | some head => 26 * head.depth + 20 ≤ 120
                      | none => 20 ≤ 120) := by
                  rw [hLook3]
                  dsimp only [e3, e2, e1, BackstackEntry.depth]
                  omega
                refine ⟨?_, ?_, ?_, ?_⟩
                · have hNonInc := popUpTo_1_equiv navProgLookup 1 120 20 (by omega) (by omega)
                    navProgLookup_extends 0 m3 3 1 false hp0 {} rfl hsf
                  have hMod1 : popUpToIdModel m3 3 1 false = .ok m1 1 := rfl
                  rw [hMod1] at hNonInc
                  obtain ⟨end1, hrun1, _, hm1, _⟩ := hNonInc
                  rw [hP1]
                  exact ⟨end1, hrun1, hm1⟩
                · have hInc := popUpToValue_equiv navProgLookup 1 120 20 (by omega) (by omega)
                    navProgLookup_extends 0 m3 3 0 (fun v => v == .int 2) true
                    hp0 {} rfl rfl hsf
                  have hMod2 : popUpToValueModel m3 3 (fun v => v == .int 2) true = .ok m1 1 :=
                    rfl
                  rw [hMod2] at hInc
                  obtain ⟨end2, hrun2, _, hm2, _⟩ := hInc
                  rw [hPV]
                  exact ⟨end2, hrun2, hm2⟩
                · have hMiss := popUpTo_1_equiv navProgLookup 1 120 20 (by omega) (by omega)
                    navProgLookup_extends 0 m3 3 999 false hp0 {} rfl hsf
                  have hErrMiss :
                      popUpToIdModel m3 3 999 false = .error .predicateNotFound := rfl
                  rw [hErrMiss] at hMiss
                  rw [hP1]
                  exact hMiss
                · have hRoot := popUpTo_1_equiv navProgLookup 1 120 20 (by omega) (by omega)
                    navProgLookup_extends 0 m3 3 1 true hp0 {} rfl hsf
                  have hErrRoot :
                      popUpToIdModel m3 3 1 true = .error .popLastEntry := rfl
                  rw [hErrRoot] at hRoot
                  rw [hP1]
                  exact hRoot
            """.trimIndent(),
        )
    }
}
