/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
--import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier
import StrataTest.Transform.ProcedureInlining

namespace Strata
namespace Python

def PyThonLaurelprelude :=
#strata
program Core;

type DictStrAny;

// Any and ListAny types

forward type ListAny;
forward type Any;

mutual
datatype Any () {
  from_none (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_string (as_string : string),
  from_datetime (as_datetime : int),
  from_Dict (as_Dict: DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: DictStrAny)
};

datatype ListAny () {
  ListAny_nil (),
  ListAny_cons (h: Any, t: ListAny)
};

end;

// Accessible to users
inline function isBool (v: Any) : Any {
  from_bool (Any..isfrom_bool(v))
}

inline function isInt (v: Any) : Any {
  from_bool (Any..isfrom_int(v))
}

inline function isFloat (v: Any) : Any {
  from_bool (Any..isfrom_float(v))
}

inline function isString (v: Any) : Any {
  from_bool (Any..isfrom_string(v))
}

inline function isdatetime (v: Any) : Any {
  from_bool (Any..isfrom_datetime(v))
}

inline function isDict (v: Any) : Any {
  from_bool (Any..isfrom_Dict(v))
}

inline function isList (v: Any) : Any {
  from_bool (Any..isfrom_ListAny(v))
}

inline function isClassIntance (v: Any) : Any {
  from_bool (Any..isfrom_ClassInstance(v))
}

inline function is_instance_of_Class (v: Any, cn: string) : Any {
  from_bool (Any..isfrom_ClassInstance(v) && Any..classname(v) == cn)
}

inline function isInstance_of_Int (v: Any) : Any {
  from_bool (Any..isfrom_int(v) || Any..isfrom_bool(v))
}

inline function isInstance_of_Float (v: Any) : Any {
  from_bool (Any..isfrom_float(v) || Any..isfrom_int(v) || Any..isfrom_bool(v))
}

inline function Any_to_bool (v: Any) : bool {
  if (Any..isfrom_bool(v)) then Any..as_bool(v) else
  if (Any..isfrom_none(v)) then false else
  if (Any..isfrom_string(v)) then !(Any..as_string(v) == "") else
  if (Any..isfrom_int(v)) then !(Any..as_int(v) == 0) else
  false
  //TOBE MORE
}

function to_string(a: Any) : string;

function to_string_any(a: Any) : Any {
  from_string(to_string(a))
}

function to_int(a: Any) : int;

function to_int_any(a: Any) : Any {
  from_int(to_int(a))
}

function datetime_strptime(dtstring: Any, format: Any) : Any;

axiom [datetime_tostring_cancel]: forall dt: Any, format: Any ::{datetime_strptime(to_string_any(dt), format)}
  datetime_strptime(to_string_any(dt), format) == dt;

// ListAny functions
function List_contains (l : ListAny, x: Any) : bool;
function List_len (l : ListAny) : int;
function List_extend (l1 : ListAny, l2: ListAny) : ListAny;
function List_append (l: ListAny, x: Any) : ListAny;
function List_get_func (l : ListAny, i : int) : Any;
function List_set_func (l : ListAny, i : int, v: Any) : ListAny;
function List_reverse (l: ListAny) : ListAny;
function List_index! (l: ListAny, v: Any): int;
function List_index (l: ListAny, v: Any): int;
function List_repeat (l: ListAny, n: int): ListAny;
function List_insert (l: ListAny, i: int, v: Any): ListAny;
function List_remove (l: ListAny, v: Any): ListAny;
function List_pop (l: ListAny, i: int): ListAny;
function List_lt (l1: ListAny, L2: ListAny): bool;
function List_le (l1: ListAny, L2: ListAny): bool;
function List_gt (l1: ListAny, L2: ListAny): bool;
function List_ge (l1: ListAny, L2: ListAny): bool;


datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string)
};

// Accessible to users
inline function isTypeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
}

inline function isAttributeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
}

inline function isAssertionError (e: Error) : Any {
  from_bool (Error..isAssertionError(e))
}

inline function isUnimplementedError (e: Error) : Any {
  from_bool (Error..isUnimplementedError(e))
}

inline function isUndefinedError (e: Error) : Any {
  from_bool (Error..isUndefinedError(e))
}

inline function isError (e: Error) : Any {
  from_bool (! Error..isNoError(e))
}

function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;
// to be extended
inline function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
}


function TypeOf (v: Any) : string;
function DictStrAny_empty () : DictStrAny;
function DictStrAny_insert (d: DictStrAny, key: string, v: Any) : DictStrAny;


function int_to_real (i: int) : real;
inline function bool_to_int (bval: bool) : int {if bval then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

function string_repeat (s: string, i: int) : string;

// Unary operations
procedure PNeg (v: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v))
  {
    ret:= from_int(- bool_to_int(Any..as_bool(v)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v))
  {
    ret:= from_int(- Any..as_int(v));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v))
  {
    ret:= from_float(- Any..as_float(v));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}
};

procedure PNot (v: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v))
  {
    ret:= from_bool(!(Any..as_bool(v)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v))
  {
    ret:= from_bool(!(Any..as_int(v) == 0));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v))
  {
    ret:= from_bool(!(Any..as_float(v) == 0.0));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v))
  {
    ret:= from_bool(!(Any..as_string(v) == ""));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v))
  {
    ret:= from_bool(!(List_len(Any..as_ListAny(v)) == 0));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}
};


//Binary operations
function string_lt (s1: string, s2: string) : bool;
function string_le (s1: string, s2: string) : bool;
function string_gt (s1: string, s2: string) : bool;
function string_ge (s1: string, s2: string) : bool;

procedure PAdd (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) + bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) + bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) + bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) + int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v1))
  {
    ret:= from_string(str.concat(Any..as_string(v1),Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_int(v2))
  {
    ret:= from_datetime((Any..as_datetime(v1) + Any..as_int(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}
};

procedure PSub (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) - bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) - Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) - bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) - Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) - bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) - Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) - Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) - int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) - Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_int(v2))
  {
    ret:= from_datetime(Any..as_datetime(v1) - Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2))
  {
    ret:= from_int(Any..as_datetime(v1) - Any..as_datetime(v2));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}
};

procedure PMul (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) * bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(bool_to_int(Any..as_bool(v1)) * Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_int(Any..as_int(v1) * bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(bool_to_real(Any..as_bool(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_float(Any..as_float(v1) * bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_string(v2))
  {
    ret:= if Any..as_bool(v1) then v2 else from_string("");
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_bool(v2))
  {
    ret:= if Any..as_bool(v2) then v1 else from_string("");
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_int(Any..as_int(v1) + Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(int_to_real(Any..as_int(v1)) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_float(Any..as_float(v1) + int_to_real(Any..as_int(v2)) );
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_string(v2))
  {
    ret:= from_string(string_repeat(Any..as_string(v2), Any..as_int(v1)));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_int(v2))
  {
    ret:= from_string(string_repeat(Any..as_string(v1), Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_repeat(Any..as_ListAny(v2), Any..as_int(v1)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_int(v2))
  {
    ret:= from_ListAny(List_repeat(Any..as_ListAny(v1), Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_float(Any..as_float(v1) + Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_string(str.concat(Any..as_string(v1),Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}}}}}}
};

procedure PLt (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) < bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) < Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_int(v1) < bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(bool_to_real(Any..as_bool(v1)) < Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_float(v1) < bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_int(v1) < Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(int_to_real(Any..as_int(v1)) < Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_float(v1) < int_to_real(Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(Any..as_float(v1) < Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_bool(string_lt(Any..as_string(v1), Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_bool(List_lt(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2))
  {
    ret:= from_bool(Any..as_datetime(v1) <Any..as_datetime(v2));
    error := NoError ();
  }
  else
  {
    ret := from_bool(false);
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}
};

procedure PLe (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) <= bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) <= Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_int(v1) <= bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(bool_to_real(Any..as_bool(v1)) <= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_float(v1) <= bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_int(v1) <= Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(int_to_real(Any..as_int(v1)) <= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_float(v1) <= int_to_real(Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(Any..as_float(v1) <= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_bool(string_le(Any..as_string(v1), Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_bool(List_le(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2))
  {
    ret:= from_bool(Any..as_datetime(v1) <= Any..as_datetime(v2));
    error := NoError ();
  }
  else
  {
    ret := from_bool(false);
    error := UndefinedError("Operand Type is not defined");
  }
  }}}}}}}}}}}
};


procedure PGt (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) > bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) > Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_int(v1) > bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(bool_to_real(Any..as_bool(v1)) > Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_float(v1) > bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_int(v1) > Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(int_to_real(Any..as_int(v1)) > Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_float(v1) > int_to_real(Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(Any..as_float(v1) > Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_bool(string_gt(Any..as_string(v1), Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_bool(List_gt(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2))
  {
    ret:= from_bool(Any..as_datetime(v1) > Any..as_datetime(v2));
    error := NoError ();
  }
  else
  {
    ret := from_bool(false);
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}
};

procedure PGe (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_bool(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) >= bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(bool_to_int(Any..as_bool(v1)) >= Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_int(v1) >= bool_to_int(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_bool(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(bool_to_real(Any..as_bool(v1)) >= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_bool(v2))
  {
    ret:= from_bool(Any..as_float(v1) >= bool_to_real(Any..as_bool(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_int(v1) >= Any..as_int(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_int(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(int_to_real(Any..as_int(v1)) >= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_int(v2))
  {
    ret:= from_bool(Any..as_float(v1) >= int_to_real(Any..as_int(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_float(v1) && Any..isfrom_float(v2))
  {
    ret:= from_bool(Any..as_float(v1) >= Any..as_float(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_string(v1) && Any..isfrom_string(v2))
  {
    ret:= from_bool(string_ge(Any..as_string(v1), Any..as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_bool(List_ge(Any..as_ListAny(v1),Any..as_ListAny(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_datetime(v1) && Any..isfrom_datetime(v2))
  {
    ret:= from_bool(Any..as_datetime(v1) >= Any..as_datetime(v2));
    error := NoError ();
  }
  else
  {
    ret := from_bool(false);
    error := UndefinedError ("Operand Type is not defined");
  }
  }}}}}}}}}}}
};


inline function PAnd (v1: Any, v2: Any) : Any
{
  from_bool(Any_to_bool (v1) && Any_to_bool (v2))
}

inline function POr (v1: Any, v2: Any) : Any
{
  from_bool(Any_to_bool (v1) || Any_to_bool (v2))
}

inline function PEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) == normalize_any (v'))
}

inline function PNEq (v: Any, v': Any) : Any {
  from_bool(normalize_any(v) != normalize_any (v'))
}

inline function PPow (v1: Any, v2: Any) : Any
{
  from_none()
}

inline function PDiv (v1: Any, v2: Any) : Any
{
  from_none()
}

inline function PMod (v1: Any, v2: Any) : Any
{
  from_none()
}


// Python proc

procedure datetime_date(d: Any) returns (ret: Any, error: Error)
{
  var timedt: int;
  if (Any..isfrom_datetime(d)) {
    havoc timedt;
    assume [timedt_le]: timedt <= Any..as_datetime(d);
    ret := from_datetime(timedt);
    error := NoError();
  }
  else {
    ret := from_none();
    error := TypeError("Input must be datetime");
  }
};


//Test

procedure datetime_now() returns (ret: Any)
{
  var d: int;
  havoc d;
  ret := from_datetime(d);
};

procedure timedelta(days: Any, hours: Any) returns (delta : Any, maybe_except: Error)
spec{
}
{
  var days_i : int := 0;
  if (Any..isfrom_int(days)) {
        days_i := Any..as_int(days);
  }
  var hours_i : int := 0;
  if (Any..isfrom_int(hours)) {
        hours_i := Any..as_int(hours);
  }
  delta := from_int ((((days_i * 24) + hours_i) * 3600) * 1000000);
};

procedure test_helper_procedure(req_name : Any, opt_name : Any) returns (ret : Any, maybe_except: Error)
spec {
  requires [req_name_is_foo]: req_name == from_string("foo");
  requires [req_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar")) ;
  ensures [ensures_maybe_except_none]: (Error..isNoError(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == from_string("foo");
  assert [assert_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar"));
  assume [assume_maybe_except_none]: (Error..isNoError(maybe_except));
};


#end

def Core.PythonLaurelPrelude : Core.Program :=
   Core.getProgram PyThonLaurelprelude |>.fst

def getFunctions (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.func => decl.name.name::getFunctions t
        | _ => getFunctions t

def getDatatypeFunctions (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match h: decl.kind with
        |.type =>
          let typedec := decl.getTypeDecl (by simp_all)
          match typedec with
          | .data dtypes =>
            let constructors := dtypes.flatMap (λ t => t.constrs.map (λ c => c.name.name))
            let destructors := dtypes.flatMap (λ t => (t.constrs.flatMap (λ c => c.args.map (fun (n,y) => t.name ++ ".." ++ n.name))))
            let testers := dtypes.flatMap (λ t => t.constrs.map (λ c => c.testerName))
            constructors ++ destructors ++ testers ++ getDatatypeFunctions t
          | _ => getDatatypeFunctions t
        | _ => getDatatypeFunctions t


def get_preludeFunctions (prelude: Core.Program) : List String := (getFunctions prelude.decls) ++ (getDatatypeFunctions prelude.decls)

def CorePrelude_functions := get_preludeFunctions Core.PythonLaurelPrelude


end Python
end Strata
