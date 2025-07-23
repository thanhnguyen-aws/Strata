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

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

#dialect
dialect C_Simp;

type int;
type bool;
type intArr;
type boolArr;

category TypeArgs;
op type_args (args : CommaSepBy Ident) : TypeArgs => "⟨" args "⟩";

category Bind;
@[declare(v, tp)]
op bind_mk (v : Ident, targs : Option TypeArgs, @[scope(targs)] tp : Type) : Bind =>
  v ":" targs tp;

category DeclList;
@[scope(b)]
op declAtom (b : Bind) : DeclList => b;
@[scope(b)]
op declPush (dl : DeclList, @[scope(dl)] b : Bind) : DeclList => dl "," b;

category MonoBind;
@[declare(v, tp)]
op mono_bind_mk (v : Ident, tp : Type) : MonoBind =>
  v ":" tp;

category MonoDeclList;
@[scope(b)]
op monoDeclAtom (b : MonoBind) : MonoDeclList => b;
@[scope(b)]
op monoDeclPush (dl : MonoDeclList, @[scope(dl)] b : MonoBind) : MonoDeclList =>
  dl "," b;


fn btrue : bool => "true";
fn bfalse : bool => "false";

fn eq (tp : Type, x : tp, y : tp) : bool => x "==" y;

fn lt (x : int, y : int) : bool => x "<" y;
fn le (x : int, y : int) : bool => x "<=" y;
fn gt (x : int, y : int) : bool => x ">" y;
fn ge (x : int, y : int) : bool => x ">=" y;

fn add (x : int, y : int) : int => x "+" y;
fn sub (x : int, y : int) : int => x "-" y;
fn mul (x : int, y : int) : int => x "*" y;
fn div (x : int, y : int) : int => x "/" y;
fn mod (x : int, y : int) : int => x "%" y;

fn not (x : bool) : bool => "!" x;
fn and (x : bool, y : bool) : bool => x "&&" y;
fn or  (x : bool, y : bool) : bool => x "||" y;


fn to_int (n : Num) : int => "#" n;

fn len (a : intArr) : int => "len(" a ")";
fn get (a : intArr, i: int) : int => "get(" a "," i ")";

category Statement;

category Block;
op block (stmts : Seq Statement) : Block => "{\n" stmts "}\n";

@[declare(v, tp)]
op init_decl (v : Ident, tp : Type) : Statement => "var" v ":" tp ";\n";

@[declare(v, tp)]
op init_def (v : Ident, tp : Type, val : tp) : Statement => "var" "(" v ":" tp ")" ":=" val ";\n";

op assert (lbl : Ident, c : bool) : Statement => "@assert" "[" lbl "]" c ";\n";

op assume (lbl : Ident, c : bool) : Statement => "@assume" "[" lbl "]" c ";\n";

category Else;
op if_command (c : bool, t : Block, f : Else) : Statement => "if" "(" c ")" "then" t f;
op else1 (f : Block) : Else => "else" f;
op else0 () : Else =>;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category MeasureCat;
op measure (e : int) : MeasureCat => "@decreases" e;

category InvariantCat;
op invariant (e : bool) : InvariantCat => "@invariant" e;

op while_command (g : bool,
                  measure: Option MeasureCat,
                  invariant: Option InvariantCat,
                  b : Block) : Statement => "while"  "(" g ")" measure invariant b;

op assign (tp : Type, v : Ident, val : tp) : Statement => v ":=" val ";\n";
op return (tp: Type, e : tp) : Statement => "return" e ";\n";

op procedure (retType: Type,
              typeArgs: Option TypeArgs,
              @[scope(typeArgs)] b : Bindings,
              name : Ident,
              @[scope(b)] pre: bool,
              @[scope(b)] post: bool,
              @[scope(b)] body : Block) : Command => "procedure" name typeArgs b "->" retType
                                                     "@pre" indent(2, pre)
                                                     "@post" indent(2, post)
                                                     indent(2, body);
#end
