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

import Jvm

namespace UiCells.JvmVerification

export Jvm (JvmInstr setLocal)

abbrev JvmVal := Jvm.JvmVal Empty
abbrev JvmState := Jvm.JvmState Empty Unit

def initJvmState (slots : List (Nat × JvmVal))
    (jh : Jvm.JvmHeap Empty := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) () jh

end UiCells.JvmVerification
