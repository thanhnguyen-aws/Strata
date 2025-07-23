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

import Lean.Data.Json.Basic

import Strata.DDM.Util.Array
import Strata.DDM.Util.Ion.AST


namespace Strata.Decimal

def ofJsonNumber (n : Lean.JsonNumber) : Decimal where
  mantissa := n.mantissa
  exponent := n.exponent

def toJsonNumber (d : Decimal) : Lean.JsonNumber :=
  let m := d.mantissa
  let e := d.exponent
  if e > 0 then
    { mantissa := m * (10 ^ e.natAbs), exponent := 0 }
  else
    { mantissa := m, exponent := e.natAbs }

end Strata.Decimal

namespace Ion

namespace Ion

/--
Convert Value into a corresponding JSON object.

Note.  This function may loses some information as JSON
has fewer native types than Ion and so some information.

Specific changes include:
 - Type information in nulls is dropped (e.g., `.null .struct` becomes
   just `.null`.
 - Floating point numbers are converted to strings.  N.B.
 - Decimal numbers lose distinction between positive and negative zero.
 - Symbols become strings
 - Structs become objects and lose represented subfields (last is preserved).
 - Sexpressions become lists.
 - Annotations are discarded.
-/
def toJson : Ion String → Lean.Json
| .null _ => .null
| .bool b => .bool b
| .int i => .num <| .fromInt i
| .float f => .str (toString f)
| .decimal d => .num d.toJsonNumber
| .string s => .str s
| .symbol s => .str s
| .struct a => .obj <| a.attach.foldl (init := {}) fun m ⟨(nm, v), _⟩ =>
  m.insert compare nm v.toJson
| .sexp l | .list l => .arr <| l.map (·.toJson)
| .annotation _ v => v.toJson
  termination_by t => t
  decreasing_by
    · rename_i p
      have q := Array.sizeOf_lt_of_mem p
      simp only [Prod.mk.sizeOf_spec] at q
      decreasing_tactic
    all_goals decreasing_tactic

/-- Constructs an ion value from a JSON object. -/
partial def ofJson : Lean.Json → Ion String
| .null => .null .null
| .bool b => .bool b
| .num n => .decimal <| .ofJsonNumber n
| .str s => .string s
| .obj m => .struct <| m.fold (init := #[]) fun a nm v => a.push (nm, .ofJson v)
| .arr a => .list <| a.map fun v => .ofJson v

end Ion
