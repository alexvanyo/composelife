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

namespace Navigation.KotlinModel

/-- Standalone model of `NavigationState.withExpectedActor(actorEntryId, block)`. -/
def withExpectedActorModel (currentEntryId : String) (actorEntryId : Option String) : Bool :=
  match actorEntryId with
  | none => true
  | some a => a == currentEntryId

/-- Surrogate entry emitted by `BackstackMapSerializer`. -/
structure SurrogateEntryModel where
  id : String
  previousId : Option String
  value : String
  deriving DecidableEq, Repr

/-- Predicate: every entry's `previousId` (if `some p`) appears strictly earlier in `xs`. -/
def isTopologicallyOrdered (xs : List SurrogateEntryModel) : Bool :=
  let rec go (seen : List String) : List SurrogateEntryModel → Bool
    | [] => true
    | e :: rest =>
      let ok := match e.previousId with | none => true | some p => seen.contains p
      ok && go (e.id :: seen) rest
  go [] xs

end Navigation.KotlinModel
