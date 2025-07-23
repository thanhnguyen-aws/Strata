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

import Strata.Languages.Boogie.ProcedureEval

namespace Boogie

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.Syntax Boogie.Syntax

/--
info: ok: Error:
none
Subst Map:
(x, ($__x0 : int)) (y, ($__y1 : int))
Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 2
Factory Functions:
func Int.Add :  ((x : int) (y : int)) → int;
func Int.Sub :  ((x : int) (y : int)) → int;
func Int.Mul :  ((x : int) (y : int)) → int;
func Int.Div :  ((x : int) (y : int)) → int;
func Int.Mod :  ((x : int) (y : int)) → int;
func Int.Neg :  ((x : int)) → int;
func Int.Lt :  ((x : int) (y : int)) → bool;
func Int.Le :  ((x : int) (y : int)) → bool;
func Int.Gt :  ((x : int) (y : int)) → bool;
func Int.Ge :  ((x : int) (y : int)) → bool;
func Bool.And :  ((x : bool) (y : bool)) → bool;
func Bool.Or :  ((x : bool) (y : bool)) → bool;
func Bool.Implies :  ((x : bool) (y : bool)) → bool;
func Bool.Equiv :  ((x : bool) (y : bool)) → bool;
func Bool.Not :  ((x : bool)) → bool;
func Str.Length :  ((x : string)) → int;
func Str.Concat :  ((x : string) (y : string)) → string;
func old : ∀[a]. ((x : a)) → a;
func select : ∀[k, v]. ((m : (Map k v)) (i : k)) → v;
func update : ∀[k, v]. ((m : (Map k v)) (i : k) (x : v)) → (Map k v);


Path Conditions:


Deferred Proof Obligations:
Label: ret_y_lt_0
Assumptions:
(0_lt_x, ((~Int.Lt #0) $__x0))
Proof Obligation:
((~Int.Lt (~Int.Neg ($__x0 : int))) #0)
-/
#guard_msgs in
#eval do let E ← Env.init.addFactory Boogie.Factory
         let (_proc, E) := evalOne E
              { header := {name := "P",
                           typeArgs := [],
                           inputs := [("x", mty[int])],
                           outputs := [("y", mty[int])] },
                spec := {
                    modifies := [],
                    preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default⟩)],
                    postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default⟩)] },
                body := [
                  Statement.set "y" eb[(~Int.Neg x)]
                ]
              }
          return format E


end Tests
---------------------------------------------------------------------

end Boogie
