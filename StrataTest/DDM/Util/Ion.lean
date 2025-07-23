/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DDM.Util.Ion
import Strata.DDM.Util.ByteArray

open Ion

def example2 : Ion String := .struct #[
  ("foo", .null .null),
  ("bar", .bool true),
  ("baz", .list #[.int 1, .int 2, .int 3])
]

def example2_enc := Ion.internAndSerialize [example2]

#guard example2_enc.asHex = "e00100eaee958183de9186710387bc83666f6f836261728362617adc8a0f8b118cb6210121022103"

def runRoundtrip (v : List (Ion SymbolId)) : Array (Ion SymbolId) :=
 match Ion.deserialize (Ion.serialize v.toArray) with
 | .error (off, msg) => panic! s!"Error at {off}: {msg}"
 | .ok r => r.flatten

def testRoundtrip (v : List (Ion SymbolId)) : Bool :=
 match Ion.deserialize (Ion.serialize v.toArray) with
 | .error _ => false
 | .ok r => r.flatten == v.toArray

#guard testRoundtrip [.bool false, .bool true]
#guard testRoundtrip [.int 0, .int 1, .int (-1), .int 256, .int (-256)]
#guard testRoundtrip [.float 1e-3, .float 3]
#guard testRoundtrip [.decimal ⟨0, 0 ⟩, .decimal ⟨1, 3 ⟩, .decimal ⟨0, 0 ⟩]
#guard testRoundtrip [.string "", .string "⟨"]
#guard testRoundtrip [.symbol (.mk 0), .symbol (.mk 1)]
#guard testRoundtrip [.list #[], .list #[.int 1]]
#guard testRoundtrip [.sexp #[], .sexp #[.int 1]]
#guard testRoundtrip [.struct #[], .struct #[(.mk 1, .int 1)]]
#guard testRoundtrip [.annotation #[.mk 1] (.int 1)]

#guard testRoundtrip <| intern [example2] |>.toList
