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

import SessionValue.Basic
import SessionValue.StateMachine

namespace SessionValue

/--
The core inductive invariant of `SessionValueHolder`:
1. When inactive, `upstreamSessionIdBeforeLocalSession` strictly equals `upstreamSessionValue.sessionId`.
2. When active, `localSessionValue` is tagged with `localSessionId`.
-/
structure ValidState (st : State α) : Prop where
  inactive_sound : st.localSessionValue = none →
    st.upstreamSessionIdBeforeLocalSession = st.upstreamSessionValue.sessionId
  active_sound : ∀ lv, st.localSessionValue = some lv →
    lv.sessionId = st.localSessionId

end SessionValue
