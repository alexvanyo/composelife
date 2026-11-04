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

import Algorithm.Plaintext

namespace Algorithm.Proofs

open Algorithm

theorem deserializePlaintext_empty :
    deserializePlaintext #[] = ⟨#[], #[]⟩ := by
  decide +kernel

theorem deserializePlaintext_single_alive :
    deserializePlaintext #["O"] = ⟨#[], #[(0, 0)]⟩ := by
  decide +kernel

theorem deserializePlaintext_single_dead :
    deserializePlaintext #["."] = ⟨#[], #[]⟩ := by
  decide +kernel

theorem deserializePlaintext_comments_ignored :
    deserializePlaintext #["! comment", "O"] = ⟨#[], #[(0, 0)]⟩ := by
  decide +kernel

theorem serializePlaintext_empty :
    serializePlaintext #[] 0 0 0 0 = #["."] := by
  decide +kernel

theorem serializePlaintext_single :
    serializePlaintext #[(0, 0)] 0 0 0 0 = #["O"] := by
  decide +kernel

theorem plaintext_roundtrip_single :
    deserializePlaintext (serializePlaintext #[(0, 0)] 0 0 0 0) = ⟨#[], #[(0, 0)]⟩ := by
  decide +kernel

theorem plaintext_roundtrip_block :
    deserializePlaintext (serializePlaintext #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 1 0 1) =
    ⟨#[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ := by
  decide +kernel

theorem plaintext_roundtrip_blinker :
    deserializePlaintext (serializePlaintext #[(0, 0), (1, 0), (2, 0)] 0 2 0 0) =
    ⟨#[], #[(0, 0), (1, 0), (2, 0)]⟩ := by
  decide +kernel

theorem plaintext_roundtrip_glider :
    deserializePlaintext (serializePlaintext #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
    ⟨#[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ := by
  decide +kernel

theorem plaintext_roundtrip_toad :
    deserializePlaintext (serializePlaintext #[(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1)] 0 3 0 1) =
    ⟨#[], #[(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1)]⟩ := by
  decide +kernel

end Algorithm.Proofs
