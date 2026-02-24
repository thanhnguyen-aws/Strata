/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

def coreLaurelPrelude :=
#strata
program Core;

datatype PNone () {
  None_none()
};

datatype Option (a: Type) {Some (unwrap: a), None ()};

type Object;
function Object_len(x : Object) : int;
axiom [Object_len_ge_zero]: (forall x : Object :: Object_len(x) >= 0);

function inheritsFrom(child : string, parent : string) : (bool);
axiom [inheritsFrom_refl]: (forall s: string :: {inheritsFrom(s, s)} inheritsFrom(s, s));

// /////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.


datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string),
  RePatternError(RePatternError_msg: string)
};

// /////////////////////////////////////////////////////////////////////////////////////
// /////////////////////////////////////////////////////////////////////////////////////
// Regular Expressions

datatype Except (err : Type, ok : Type) {
  Except_mkOK(Except_getOK: ok),
  Except_mkErr(Except_getErr: err)
};

type ExceptErrorRegex := Except Error regex;

// NOTE: `re.match` returns a `Re.Match` object, but for now, we are interested
// only in match/nomatch, which is why we return `bool` here.
function PyReMatchRegex(pattern : regex, str : string, flags : int) : bool;
// We only support Re.Match when flags == 0.
axiom [PyReMatchRegex_def_noFlg]:
  (forall pattern : regex, str : string :: {PyReMatchRegex(pattern, str, 0)}
    PyReMatchRegex(pattern, str, 0) == str.in.re(str, pattern));

// Unsupported/uninterpreted: eventually, this would first call PyReCompile and if there's
// no exception, call PyReMatchRegex.
function PyReMatchStr(pattern : string, str : string, flags : int) : Except Error bool;

// /////////////////////////////////////////////////////////////////////////////////////

// List of strings
datatype ListStr () {
  ListStr_nil(),
  ListStr_cons(head: string, tail: ListStr)
};

// /////////////////////////////////////////////////////////////////////////////////////

// Temporary Types

type StrOrNone := Option (string);
type IntOrNone := Option (int);

function strOrNone_toObject(v : StrOrNone) : Object;
// Injectivity axiom: different StrOrNone map to different objects.
axiom (forall s1:StrOrNone, s2: StrOrNone :: {strOrNone_toObject(s1), strOrNone_toObject(s2)}
        s1 != s2 ==>
        strOrNone_toObject(s1) != strOrNone_toObject(s2));

//https://github.com/strata-org/Strata/issues/460
//axiom (forall s : StrOrNone :: {Some (s)}
//        Option..isSome (s) ==>
//        Object_len(strOrNone_toObject(s)) == str.len(Option..unwrap(s)));

datatype BoolOrStrOrNone () {
  BoolOrStrOrNone_mk_bool(bool_val: bool),
  BoolOrStrOrNone_mk_str(str_val: string),
  BoolOrStrOrNone_mk_none(none_val: PNone)
};

datatype DictStrStrOrNone () {
  DictStrStrOrNone_mk_str(str_val: string),
  DictStrStrOrNone_mk_none(none_val: PNone)
};

datatype BytesOrStrOrNone () {
  BytesOrStrOrNone_mk_none(none_val: PNone),
  BytesOrStrOrNone_mk_str(str_val: string)
};

type DictStrAny;
function DictStrAny_mk(s : string) : (DictStrAny);

type ListDictStrAny;
function ListDictStrAny_nil() : (ListDictStrAny);

datatype Client () {
  Client_S3(),
  Client_CW()
};

// /////////////////////////////////////////////////////////////////////////////////////
// Datetime

////// 1. Timedelta.

// According to http://docs.python.org/3/library/datetime.html,
// ""
//  Only days, seconds and microseconds are stored internally. Arguments are
//  converted to those units:
//  - A millisecond is converted to 1000 microseconds.
//  - A minute is converted to 60 seconds.
//  - An hour is converted to 3600 seconds.
//  - A week is converted to 7 days.
//  and days, seconds and microseconds are then normalized so that the
//  representation is unique, with
//  - 0 <= microseconds < 1000000
//  - 0 <= seconds < 3600*24 (the number of seconds in one day)
//  - -999999999 <= days <= 999999999
// ""

// In the Strata Core representation, an int type that corresponds to the full
// milliseconds is simply used. See Timedelta_mk.



function Timedelta_mk(days : int, seconds : int, microseconds : int): int {
  ((days * 3600 * 24) + seconds) * 1000000 + microseconds
}

function Timedelta_get_days(timedelta : int) : int;
function Timedelta_get_seconds(timedelta : int) : int;
function Timedelta_get_microseconds(timedelta : int) : int;

axiom [Timedelta_deconstructors]:
    (forall days0 : int, seconds0 : int, msecs0 : int,
            days : int, seconds : int, msecs : int
            :: {(Timedelta_mk(days0, seconds0, msecs0))}
      Timedelta_mk(days0, seconds0, msecs0) ==
          Timedelta_mk(days, seconds, msecs) &&
      0 <= msecs && msecs < 1000000 &&
      0 <= seconds && seconds < 3600 * 24 &&
      -999999999 <= days && days <= 999999999
      ==> Timedelta_get_days(Timedelta_mk(days0, seconds0, msecs0)) == days &&
          Timedelta_get_seconds(Timedelta_mk(days0, seconds0, msecs0)) == seconds &&
          Timedelta_get_microseconds(Timedelta_mk(days0, seconds0, msecs0)) == msecs);


////// Datetime.
// Datetime is abstractly defined as a pair of (base time, relative timedelta).
// datetime.now() returns (<the curent datetime>, 0).
// Adding or subtracting datetime.timedelta updates
type Datetime;
type Datetime_base;

function Datetime_get_base(d : Datetime) : Datetime_base;
function Datetime_get_timedelta(d : Datetime) : int;

// now() returns an abstract, fresh current datetime.
// This abstract now() does not guarantee monotonic increase of time, and this
// means subtracting an 'old' timestamp from a 'new' timestamp may return
// a negative difference.




// Comparison of Datetimes is abstractly defined so that the result is
// meaningful only if the two datetimes have same base.
function Datetime_lt(d1:Datetime, d2:Datetime):bool;

axiom [Datetime_lt_ax]:
    (forall d1:Datetime, d2:Datetime :: {}
        Datetime_get_base(d1) == Datetime_get_base(d2)
        ==> Datetime_lt(d1, d2) ==
            (Datetime_get_timedelta(d1) < Datetime_get_timedelta(d2)));


type Date;


/////////////////////////////////////////////////////////////////////////////////////


// /////////////////////////////////////////////////////////////////////////////////////

// Uninterpreted procedures
procedure importFrom(module : string, names : ListStr, level : int) returns ();
procedure import(names : ListStr) returns ();
procedure print(msg : string, opt : StrOrNone) returns ();

procedure json_dumps(msg : DictStrAny, opt_indent : IntOrNone) returns (s: string, maybe_except: Error)
spec{};

procedure json_loads(msg : string) returns (d: DictStrAny, maybe_except: Error)
spec{};

procedure input(msg : string) returns (result: string, maybe_except: Error)
spec{};

procedure random_choice(l : ListStr) returns (result: string, maybe_except: Error)
spec{};

function str_in_list_str(s : string, l: ListStr) : bool;

function str_in_dict_str_any(s : string, l: DictStrAny) : bool;

function list_str_get(l : ListStr, i: int) : string;

function str_len(s : string) : int;

function dict_str_any_get(d : DictStrAny, k: string) : DictStrAny;

function dict_str_any_get_list_str(d : DictStrAny, k: string) : ListStr;

function dict_str_any_get_str(d : DictStrAny, k: string) : string;

function dict_str_any_length(d : DictStrAny) : int;

procedure str_to_float(s : string) returns (result: string, maybe_except: Error)
;

function Float_gt(lhs : string, rhs: string) : bool;

// /////////////////////////////////////////////////////////////////////////////////////


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

function TypeOf (v: Any) : string;
function DictStrAny_empty () : DictStrAny;
function DictStrAny_insert (d: DictStrAny, key: string, v: Any) : DictStrAny;

inline function Any_to_bool (v: Any) : bool {
  if (Any..isfrom_bool(v)) then Any..as_bool(v) else
  if (Any..isfrom_none(v)) then false else
  if (Any..isfrom_string(v)) then !(Any..as_string(v) == "") else
  if (Any..isfrom_int(v)) then !(Any..as_int(v) == 0) else
  false
  //TOBE MORE
}

function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;
// to be extended
function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if Any..isfrom_float(v) && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
}



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

function Any_in_Dict (a: Any, d: Any) : Any;

procedure PIn (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_Dict(v2))
  {
    ret:= Any_in_Dict(v1, v2);
    error := NoError ();
  }
  else { if (Any..isfrom_ListAny(v2))
  {
    ret := from_bool(List_contains(Any..as_ListAny(v2), v1));
    error := NoError ();
  }
  else {
    ret := from_bool(false);
    error := UndefinedError ("Operand type not supported");
  }
  }
};

procedure PNotIn (v1: Any, v2: Any) returns (ret: Any, error: Error)
spec {
  free requires [dummy]: true;
  free ensures [dummy]: true;
}
{
  if (Any..isfrom_Dict(v2))
  {
    ret:= from_bool(!Any..as_bool(Any_in_Dict(v1, v2)));
    error := NoError ();
  }
  else { if (Any..isfrom_ListAny(v2))
  {
    ret := from_bool(!List_contains(Any..as_ListAny(v2), v1));
    error := NoError ();
  }
  else {
    ret := from_bool(true);
    error := UndefinedError ("Operand type not supported");
  }
  }
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

// Class functions

function Attributes_set (c: Any, attrs: ListStr, val: Any) : Any;
function Attribute_set (c: Any, attr: string, val: Any) : Any;
function Attributes_get (c: Any, attrs: ListStr) : Any;
function Attribute_get (c: Any, attr: string) : Any;

//Python functions

procedure datetime_now() returns (ret: Any)
{
  var d: int;
  havoc d;
  ret := from_datetime(d);
};

procedure datetime_utcnow() returns (d:Datetime, maybe_except: Error)
spec {
  ensures (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
}
{
  assume [assume_datetime_now]: (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
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
  assume [assume_timedelta_sign_matches]: (Any..as_int(delta) == (((days_i * 24) + hours_i) * 3600) * 1000000);
};

procedure datetime_date(dt: Any) returns (d : Any, maybe_except: Error)
spec{};

function datetime_to_str(dt : Datetime) : string;

function datetime_to_int() : int;

function to_string(a: Any) : string;

function to_string_any(a: Any) : Any {
  from_string(to_string(a))
}

function to_int(a: Any) : int;

function to_int_any(a: Any) : Any {
  from_int(to_int(a))
}


procedure datetime_strptime(time: Any, format: Any) returns (ret : Any, maybe_except: Error)
spec{
  requires [req_format_str]: (format == from_string("%Y-%m-%d"));
  ensures [ensures_str_strp_reverse]: (forall dt : Any :: {ret == dt} ((time == to_string_any(dt)) <==> (ret == dt)));
}
{
  assume [assume_str_strp_reverse]: (forall dt : Any :: {ret == dt} ((time == to_string_any(dt)) <==> (ret == dt)));
};




procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: Error)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [req_opt_name_none_or_bar]: (Option..isNone(opt_name)) || (Option..unwrap(opt_name) == "bar") ;
  ensures [ensures_maybe_except_none]: (Error..isNoError(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == "foo";
  assert [assert_opt_name_none_or_bar]: (Option..isNone(opt_name)) || (Option..unwrap(opt_name) == "bar");
  assume [assume_maybe_except_none]: (Error..isNoError(maybe_except));
};


#end

def Core.PythonLaurelrelude : Core.Program :=
   Core.getProgram coreLaurelPrelude |>.fst

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

--#eval (getDatatypeFunctions Core.prelude.decls).filter (fun x => x.startsWith "None")

def get_preludeFunctions (prelude: Core.Program) : List String := (getFunctions prelude.decls) ++ (getDatatypeFunctions prelude.decls)

def CorePrelude_functions := get_preludeFunctions Core.PythonLaurelrelude


end Python
end Strata
