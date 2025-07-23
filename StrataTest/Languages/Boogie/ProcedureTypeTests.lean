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

import Strata.Languages.Boogie.ProcedureType

namespace Boogie

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.Syntax Boogie.Syntax

/--
info: ok: ((procedure P :  ((x : int)) → ((y : int)))
 modifies: []
 preconditions: (0_lt_x, (((~Int.Lt : (arrow int (arrow int bool))) (#0 : int)) (x : int)))
 postconditions: (ret_y_lt_0, (((~Int.Lt : (arrow int (arrow int bool))) (y : int)) (#0 : int)))
 body: y := (((~Int.Sub : (arrow int (arrow int int))) (#0 : int)) (x : int))
 ,
 context:
 types:   ⏎
 aliases: []
 state:
 tyGen: 6
 tyPrefix: $__ty
 exprGen: 0
 exprPrefix: $__var
 subst: ($__ty5, int)
 ($__ty4, (arrow int int))
 ($__ty3, bool)
 ($__ty2, (arrow int bool))
 ($__ty1, bool)
 ($__ty0, (arrow int bool))
  known types: [∀[a, b]. (arrow a b), bool, int, string])
-/
#guard_msgs in
#eval do let ans ← typeCheck { TEnv.default with functions := Boogie.Factory }
                             Program.init
                             { header := {name := "P",
                                          typeArgs := [],
                                          inputs := [("x", mty[int])],
                                          outputs := [("y", mty[int])] },
                               spec := { modifies := [],
                                         preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default⟩)],
                                         postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default⟩)] },
                               body := [
                                 Statement.set "y" eb[((~Int.Sub #0) x)]
                               ]
                             }
         return format ans

/--
info: ok: (procedure P :  ((a : int)) → ())
modifies: [g]
preconditions: ⏎
postconditions: (P.g_eq_a, ((g : int) == (((~Int.Add : (arrow int (arrow int int))) ((~old : (arrow int int)) (g : int))) (a : int))))
body: g := (((~Int.Add : (arrow int (arrow int int))) (a : int)) (g : int))
-/
#guard_msgs in
#eval do let ans ←
              typeCheck { TEnv.default (Identifier:=BoogieIdent) with
                              functions := Boogie.Factory,
                              context := { types := [[("g", t[int])]] }}
                        Program.init
                        { header := { name := "P",
                                      typeArgs := [],
                                      inputs := [("a", mty[int])],
                                      outputs := [] },
                          spec := {
                          modifies := [("g")],
                          preconditions := [],
                          postconditions :=
                            [("P.g_eq_a", ⟨eb[g == ((~Int.Add (~old g)) a)], .Default⟩)] },
                          body :=
                            [Statement.set "g" eb[((~Int.Add a) g)]]
                        }
          return format ans.fst

/--
info: ok: (procedure P :  ((a : int)) → ())
modifies: [g]
preconditions: ⏎
postconditions: (P.g_eq_a, ((g : int) == (((~Int.Add : (arrow int (arrow int int))) ((~old : (arrow int int)) (a : int))) ((~old : (arrow int int)) (g : int)))))
body: g := (((~Int.Add : (arrow int (arrow int int))) (a : int)) (g : int))
-/
#guard_msgs in
#eval do let ans ←
              typeCheck { TEnv.default (Identifier:=BoogieIdent) with
                              functions := Boogie.Factory,
                              context := { types := [[("g", t[int])]] }}
                        Program.init
                        { header := { name := "P",
                                      typeArgs := [],
                                      inputs := [("a", mty[int])],
                                      outputs := [] },
                          spec := {
                          modifies := [("g")],
                          preconditions := [],
                          postconditions :=
                            [("P.g_eq_a", ⟨eb[g == (~old ((~Int.Add a) g))], .Default⟩)] },
                          body :=
                            [Statement.set "g" eb[((~Int.Add a) g)]]
                        }
          return format ans.fst


---------------------------------------------------------------------
end Tests
end Boogie
