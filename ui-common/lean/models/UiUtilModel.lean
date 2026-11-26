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

namespace UiCommon.KotlinModel

/-- Standalone model of `NonNegativeLong.transformInput`: returns `true` iff changes are reverted. -/
def nonNegativeLongShouldRevert (isEmpty : Bool) (parsed : Option Int64) : Bool :=
  if isEmpty then false
  else match parsed with
  | none => true
  | some v => v < 0

/-- Standalone model of `NonNegativeDouble.transformInput`: returns `true` iff changes are reverted. -/
def nonNegativeDoubleShouldRevert (isEmpty : Bool) (parsed : Option Float) : Bool :=
  if isEmpty then false
  else match parsed with
  | none => true
  | some d => d.isNaN || d < 0.0

end UiCommon.KotlinModel
