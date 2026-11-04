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
import proofs.PlaintextProofs

namespace Algorithm

theorem deserializePlaintext_empty :
    deserializePlaintext #[] = ⟨#[], #[]⟩ :=
  Proofs.deserializePlaintext_empty

theorem deserializePlaintext_single_alive :
    deserializePlaintext #["O"] = ⟨#[], #[(0, 0)]⟩ :=
  Proofs.deserializePlaintext_single_alive

theorem deserializePlaintext_single_dead :
    deserializePlaintext #["."] = ⟨#[], #[]⟩ :=
  Proofs.deserializePlaintext_single_dead

theorem deserializePlaintext_comments_ignored :
    deserializePlaintext #["! comment", "O"] = ⟨#[], #[(0, 0)]⟩ :=
  Proofs.deserializePlaintext_comments_ignored

theorem serializePlaintext_empty :
    serializePlaintext #[] 0 0 0 0 = #["."] :=
  Proofs.serializePlaintext_empty

theorem serializePlaintext_single :
    serializePlaintext #[(0, 0)] 0 0 0 0 = #["O"] :=
  Proofs.serializePlaintext_single

theorem plaintext_roundtrip_single :
    deserializePlaintext (serializePlaintext #[(0, 0)] 0 0 0 0) = ⟨#[], #[(0, 0)]⟩ :=
  Proofs.plaintext_roundtrip_single

theorem plaintext_roundtrip_block :
    deserializePlaintext (serializePlaintext #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 1 0 1) =
    ⟨#[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ :=
  Proofs.plaintext_roundtrip_block

theorem plaintext_roundtrip_blinker :
    deserializePlaintext (serializePlaintext #[(0, 0), (1, 0), (2, 0)] 0 2 0 0) =
    ⟨#[], #[(0, 0), (1, 0), (2, 0)]⟩ :=
  Proofs.plaintext_roundtrip_blinker

theorem plaintext_roundtrip_glider :
    deserializePlaintext (serializePlaintext #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
    ⟨#[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ :=
  Proofs.plaintext_roundtrip_glider

theorem plaintext_roundtrip_toad :
    deserializePlaintext (serializePlaintext #[(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1)] 0 3 0 1) =
    ⟨#[], #[(1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1)]⟩ :=
  Proofs.plaintext_roundtrip_toad

end Algorithm
