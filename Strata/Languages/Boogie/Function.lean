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



import Strata.Languages.Boogie.Statement

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Lambda

/-! # Boogie Functions -/

abbrev Function := Lambda.LFunc BoogieIdent

open LTy.Syntax LExpr.Syntax in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (Identifier:=BoogieIdent)
                     ({ name := (.unres, "Foo"),
                        typeArgs := ["a", "b"],
                        inputs := [((.locl, "w"), mty[int]), ((.locl, "x"), mty[%a]), ((.locl, "y"), mty[%b]), ((.locl, "z"), mty[%a])],
                        output := mty[%a],
                        body := some (.fvar (.locl, "x") none) } : Function)
         return format type

---------------------------------------------------------------------

end Boogie
