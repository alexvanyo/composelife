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

import models.DeserializationResultModel
import proofs.DeserializationResultModelProofs

namespace Algorithm.KotlinModel

theorem reduceToSuccessfulStep_preserves_successful (a b : DeserResultModel)
    (h : a.isSuccessful = true ∨ b.isSuccessful = true) :
    (reduceToSuccessfulStep a b).isSuccessful = true :=
  reduceToSuccessfulStep_preserves_successful_Impl a b h

theorem reduceToSuccessfulStep_warningFree_dominates (id : Nat) (b : DeserResultModel) :
    reduceToSuccessfulStep (.successful true id) b = .successful true id :=
  reduceToSuccessfulStep_warningFree_dominates_Impl id b

theorem reduceToSuccessful_finds_successful (xs : List DeserResultModel)
    (h : ∃ x ∈ xs, x.isSuccessful = true) :
    ∃ r, reduceToSuccessfulModel xs = some r ∧ r.isSuccessful = true :=
  reduceToSuccessful_finds_successful_Impl xs h

theorem fromFileExtension_known :
    fromFileExtensionModel (some "cells") = .plaintext ∧
    fromFileExtensionModel (some "lif") = .life ∧
    fromFileExtensionModel (some "life") = .life ∧
    fromFileExtensionModel (some "rle") = .runLengthEncoding ∧
    fromFileExtensionModel (some "mc") = .macrocell ∧
    fromFileExtensionModel none = .unknown :=
  fromFileExtension_known_Impl

end Algorithm.KotlinModel
