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

import models.BackstackStateModel

namespace Navigation.KotlinModel

theorem withExpectedActorModel_none_Impl (cur : String) :
    withExpectedActorModel cur none = true := rfl

theorem withExpectedActorModel_some_iff_Impl (cur a : String) :
    withExpectedActorModel cur (some a) = true ↔ a = cur := by
  simp [withExpectedActorModel]

theorem isTopologicallyOrdered_pair_Impl (rootId childId v1 v2 : String) :
    isTopologicallyOrdered
      [{ id := rootId, previousId := none, value := v1 },
       { id := childId, previousId := some rootId, value := v2 }] = true := by
  simp [isTopologicallyOrdered, isTopologicallyOrdered.go]

end Navigation.KotlinModel
