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
import Lean.ToExpr
import Strata.DDM.Util.Lean

private def String.replicate (n : Nat) (c : Char) := n.repeat (a := "") (·.push c)

namespace Strata

structure Decimal where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Inhabited, Repr

namespace Decimal

def zero : Decimal := { mantissa := 0, exponent := 0 }

opaque maxPrettyExponent : Int := 5

opaque minPrettyExponent : Int := -5

def toString (d : Decimal) : String :=
  let m := d.mantissa
  let e := d.exponent
  if m = 0 then
    s!"0.0"
  else if e == 0 then
    s!"{m}.0"
  else if e > 0 ∧ e ≤ maxPrettyExponent then
    s!"{m}{String.replicate e.natAbs '0'}.0"
  else if e < 0 ∧ e ≥ minPrettyExponent then
    let ms := if m < 0 then "-" else ""
    let ma := m.natAbs
    let ne := 10^(-e).natAbs
    let md := ma % ne
    s!"{ms}{ma / ne}.{md}"
  else
    s!"{m}e{e}"

instance : ToString Decimal where
  toString := Decimal.toString

section

open _root_.Lean

instance : ToExpr Decimal where
  toTypeExpr := mkConst ``Decimal
  toExpr d :=
    mkApp2 (mkConst ``Decimal.mk) (toExpr d.mantissa) (toExpr d.exponent)

instance : Quote Decimal where
  quote d := Syntax.mkCApp ``Decimal.mk #[quote d.mantissa, quote d.exponent]

end

end Decimal

#guard s!"{Decimal.mk 0 0}" = "0.0"
#guard s!"{Decimal.mk 1 0}" = "1.0"
#guard s!"{Decimal.mk (-3) 0}" = "-3.0"
#guard s!"{Decimal.mk 4 2}" = "400.0"
#guard s!"{Decimal.mk (-4) 2}" = "-400.0"
#guard s!"{Decimal.mk (42) (-2)}" = "0.42"
#guard s!"{Decimal.mk (-42) (-2)}" = "-0.42"
#guard s!"{Decimal.mk (-134) (-2)}" = "-1.34"
#guard s!"{Decimal.mk (-142) 10}" = "-142e10"
#guard s!"{Decimal.mk (-142) 10}" = "-142e10"

end Strata
