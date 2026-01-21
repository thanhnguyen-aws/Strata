/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata

def CoreTypePrelude :=
#strata
program Core;

datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  Unimplemented (Unimplement_msg : string),
  Undefined (Undefined_msg : string)
};

inline function isError (e: Error) : bool {
  ! Error..isNoError(e)
}



type Datetime;

// Class type
type ClassInstance;
type InstanceAttributes;
type Dict;


// Any and ListAny types
type ListAny;

datatype Any () {
  from_none (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_string (as_string : string),
  from_datetime (as_datetime : Datetime),
  from_Dict (as_Dict: Dict),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: InstanceAttributes)
};


// Types of Any
type ListPType;

datatype PyType () {
  NONE(),
  BOOL (),
  INT (),
  FLOAT (),
  STRING (),
  DATETIME(),
  DICT(),
  LIST (listtype: ListPType),
  CLASS (typeclassname: string)
};

function TypesOf (l: ListAny) : ListPType;

function TypeOf (v : Any) : PyType {
  if Any..isfrom_none (v) then
    NONE ()
  else if Any..isfrom_bool (v) then
    BOOL ()
  else if Any..isfrom_int (v) then
    INT ()
  else if Any..isfrom_float (v) then
    FLOAT ()
  else if Any..isfrom_string (v) then
    STRING ()
  else if Any..isfrom_datetime (v) then
    DATETIME ()
  else if Any..isfrom_Dict (v) then
    DICT ()
  else if Any..isfrom_ListAny (v) then
    LIST (TypesOf (as_ListAny(v)))
  else CLASS(classname(v))
}

inline function isAssertionError (e: Error) : Any {
  from_bool (Error..isAssertionError(e))
}

inline function isTypeError (e: Error) : Any {
  from_bool (Error..isTypeError(e))
}



//Dup type for ListAny, to be remove when mutual recursive datatype is supported
datatype ListAnyDup () {
  nil (),
  cons (head: Any, tail: ListAnyDup)
};
function ListAny_from_ListAnyDup(l: ListAnyDup): ListAny;
function ListAny_to_ListAnyDup(l: ListAny): ListAnyDup;
axiom [List_constr_destr_cancel]: forall l: ListAnyDup :: {ListAny_to_ListAnyDup(ListAny_from_ListAnyDup(l))}
  ListAny_to_ListAnyDup(ListAny_from_ListAnyDup(l)) == l;
axiom [List_destr_constr_cancel]: forall l: ListAny :: {ListAny_from_ListAnyDup(ListAny_to_ListAnyDup(l))}
  ListAny_from_ListAnyDup(ListAny_to_ListAnyDup(l)) == l;
// End of ListAnyDup

//Dup type for ListPType, to be remove when mutual recursive datatype is supported
datatype ListPTypeDup () {
  tnil (),
  tcons (thead: Any, ttail: ListPTypeDup)
};
function ListPType_from_ListPTypeDup(l: ListPTypeDup): ListPType;
function ListPType_to_ListPTypeDup(l: ListPType): ListPTypeDup;
axiom [ListPType_constr_destr_cancel]: forall l: ListPTypeDup :: {ListPType_to_ListPTypeDup(ListPType_from_ListPTypeDup(l))}
  ListPType_to_ListPTypeDup(ListPType_from_ListPTypeDup(l)) == l;
axiom [ListPType_destr_constr_cancel]: forall l: ListPType :: {ListPType_from_ListPTypeDup(ListPType_to_ListPTypeDup(l))}
  ListPType_from_ListPTypeDup(ListPType_to_ListPTypeDup(l)) == l;
// End of ListPTypeDup


// Class types
//Dup type for InstanceAttributes,
type InstanceAttributesDup := Map string Any;
function InstanceAttributes_from_Dup(ia: InstanceAttributesDup): InstanceAttributes;
function InstanceAttributes_to_Dup(ia: InstanceAttributes): InstanceAttributesDup;
axiom [IA_constr_destr_cancel]: forall ia: InstanceAttributesDup :: {InstanceAttributes_to_Dup(InstanceAttributes_from_Dup(ia))}
  InstanceAttributes_to_Dup(InstanceAttributes_from_Dup(ia)) == ia;
axiom [IA_destr_constr_cancel]: forall ia: InstanceAttributes :: {InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(ia))}
  InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(ia)) == ia;


function InstanceAttributes_empty() : InstanceAttributes;
axiom [AttributeAnys_empty_def]: forall a: string :: {InstanceAttributes_to_Dup(InstanceAttributes_empty())[a]}
  InstanceAttributes_to_Dup(InstanceAttributes_empty())[a] == from_none();

function ClassInstance_empty (c: string) : Any {
  from_ClassInstance(c,InstanceAttributes_empty())
}


procedure ClassInstance_init_InstanceAttribute(ci: Any, attribute: string, v: Any) returns (ret: Any, error: Error)
{
  if (Any..isfrom_ClassInstance(ci)) {
    ret := from_ClassInstance(classname(ci), InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(instance_attributes(ci))[attribute := v]));
    error := NoError ();
  }
  else {
    error := TypeError ("Not a Class");
  }
};

procedure ClassInstance_get_InstanceAttribute(ci: Any, attribute: string) returns (ret: Any, error: Error) {
  if (Any..isfrom_ClassInstance(ci))
  {
    ret := InstanceAttributes_to_Dup(instance_attributes(ci))[attribute];
    if (Any..isfrom_none(ret)) {
      error := AttributeError("Attribute not in ClassInstance Attributes");
    } else {
      error := NoError ();
    }
  } else {
    ret := from_none();
    error := TypeError ("Not a Class");
  }
};

procedure ClassInstance_set_InstanceAttribute(ci: Any, attribute: string, v: Any) returns (ret: Any, error: Error)
{
  var attval : Any;
  if (Any..isfrom_ClassInstance(ci))
  {
    attval := InstanceAttributes_to_Dup(instance_attributes(ci))[attribute];
    if (Any..isfrom_none(attval)) {
      error := AttributeError("Attribute not in ClassInstance Attributes");
    } else {
      ret := from_ClassInstance(classname(ci), InstanceAttributes_from_Dup(InstanceAttributes_to_Dup(instance_attributes(ci))[attribute := v]));
      error := NoError ();
    }
  } else {
    ret := ci;
    error := TypeError ("Not a Class");
  }
};

function hasAttribute(ci: Any, attribute: string): bool {
  if (Any..isfrom_ClassInstance(ci)) then
    !(InstanceAttributes_to_Dup(instance_attributes(ci))[attribute] == from_none())
  else false
}

// isSubType functions
// mutual
function isSubTypes (t1: ListPType, t2: ListPType) : bool;
function isSubType (t1: PyType, t2: PyType) : bool {
  if t1 == t2 then true
  else if PyType..isFLOAT(t2) && (PyType..isBOOL(t1) || PyType..isBOOL(t1)) then true
  else if PyType..isLIST(t1) && PyType..isLIST(t2) && isSubTypes(listtype(t1), listtype(t2)) then true
  else false
}
// end mutal

// isInstance function:
function isInstance (v: Any, vt: PyType) : bool {
  isSubType(TypeOf(v), vt)
}

function is_IntReal (v: Any) : bool;
function Any_real_to_int (v: Any) : int;
// to be extended
function normalize_any (v : Any) : Any {
  if v == from_bool(true) then from_int(1)
  else (if v == from_bool(false) then from_int(0) else
        if TypeOf(v) == FLOAT && is_IntReal(v) then from_int(Any_real_to_int(v)) else
        v)
}

// Dict type
type DictDup := Map Any Any;
function Dict_from_DictDup(d: DictDup): Dict;
function Dict_to_DictDup(d: Dict): DictDup;
axiom [Dict_constr_destr_cancel]: forall d: DictDup :: {Dict_to_DictDup(Dict_from_DictDup(d))}
  Dict_to_DictDup(Dict_from_DictDup(d)) == d;
axiom [Dict_destr_constr_cancel]: forall d: Dict :: {Dict_from_DictDup(Dict_to_DictDup(d))}
  Dict_from_DictDup(Dict_to_DictDup(d)) == d;


function Dict_insert (d: Dict, k: Any, v: Any) : Dict {
  Dict_from_DictDup(Dict_to_DictDup(d)[normalize_any(k):= v])
}

function Dict_get (d: Dict, k: Any) : Any {
  Dict_to_DictDup(d)[normalize_any(k)]
}

function Dict_remove (d: Dict, k: Any) : Dict {
  Dict_from_DictDup(Dict_to_DictDup(d)[normalize_any(k):= from_none()])
}

inline function Dict_contains (d: Dict, k: Any) : bool {
  Dict_get (d,k) != from_none()
}

function Any_to_DictDup (d: Any): DictDup {
  Dict_to_DictDup(as_Dict(d))
}

inline function Any_in_Dict (a: Any, d: Any) : Any {
  from_bool(Any_to_DictDup(d)[a]!= from_none())
}


type kwargs := Map string Any;
//Dictionary functions
function kwargs_empty() : kwargs;
axiom [kwargs_empty_def]: forall k: string :: {kwargs_empty() [k]} kwargs_empty()[k] == from_none();
function kwargs_set (kwa: kwargs, k: string, v: Any) : kwargs {
  kwa[k:= v]
}
function kwargs_get (kwa: kwargs, k: string) : Any {
  kwa[k]
}
function kwargs_contains (d: kwargs, k: string) : bool {
  kwargs_get (d,k) != from_none()
}

// ListAny functions
function List_contains (l : ListAny, x: Any) : bool;
function List_len (l : ListAny) : int;
function List_extend (l1 : ListAny, l2: ListAny) : ListAny;
function List_append (l: ListAny, x: Any) : ListAny;
function List_get (l : ListAny, i : int) : Any;
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


function int_to_real (i: int) : real;
inline function bool_to_int (b: bool) : int {if b then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

function string_repeat (s: string, i: int) : string;



//Binary operations
function string_lt (s1: string, s2: string) : bool;
function string_le (s1: string, s2: string) : bool;
function string_gt (s1: string, s2: string) : bool;
function string_ge (s1: string, s2: string) : bool;

procedure PAdd (v1: Any, v2: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) + bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) + as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(as_int(v1) + bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(bool_to_real(as_bool(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= from_float(as_float(v1) + bool_to_real(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= from_int(as_int(v1) + as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(int_to_real(as_int(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= from_float(as_float(v1) + int_to_real(as_int(v2)) );
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(as_float(v1) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= from_string(str.concat(as_string(v1),as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(as_ListAny(v1),as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};


procedure PIn (v1: Any, v2: Any) returns (ret: Any, error: Error) {
  if (Any..isfrom_Dict(v2))
  {
    ret:= Any_in_Dict(v1, v2);
    error := NoError ();
  }
  else { if (Any..isfrom_ListAny(v2))
  {
    ret := from_bool(List_contains(as_ListAny(v2), v1));
    error := NoError ();
  }
  else {
    ret := from_bool(false);
    error := Undefined ("Operand type not supported");
  }
  }
};

function PEq (v: Any, v': Any) : bool {
  normalize_any(v) == normalize_any (v')
}




#end

--#eval verify "cvc5" CoreTypePrelude
--#eval boogieTypePrelude.format

def Core.Typeprelude : Core.Program :=
   Core.getProgram Strata.CoreTypePrelude |>.fst

end Strata

/-

function int_to_real (i: int) : real;
inline function bool_to_int (b: bool) : int {if b then 1 else 0}
inline function bool_to_real (b: bool) : real {if b then 1.0 else 0.0}

function string_repeat (s: string, i: int) : string;

// Unary operations
procedure PNeg (v: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v) == BOOL())
  {
    ret:= from_int(- bool_to_int(as_bool(v)));
    error := NoError ();
  }
  else {if (TypeOf(v) == INT())
  {
    ret:= from_int(- as_int(v));
    error := NoError ();
  }
  else {if (TypeOf(v) == FLOAT())
  {
    ret:= from_float(- as_float(v));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}
};

procedure PNot (v: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v) == BOOL())
  {
    ret:= from_bool(!(as_bool(v)));
    error := NoError ();
  }
  else {if (TypeOf(v) == INT())
  {
    ret:= from_bool(!(as_int(v) == 0));
    error := NoError ();
  }
  else {if (TypeOf(v) == FLOAT())
  {
    ret:= from_bool(!(as_float(v) == 0.0));
    error := NoError ();
  }
  else {if (TypeOf(v) == STRING())
  {
    ret:= from_bool(!(as_string(v) == ""));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v))
  {
    ret:= from_bool(!(List_len(as_ListAny(v)) == 0));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}}}
};


//Binary operations
function string_lt (s1: string, s2: string) : bool;
function string_le (s1: string, s2: string) : bool;
function string_gt (s1: string, s2: string) : bool;
function string_ge (s1: string, s2: string) : bool;

procedure PAdd (v1: Any, v2: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) + bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) + as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(as_int(v1) + bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(bool_to_real(as_bool(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= from_float(as_float(v1) + bool_to_real(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= from_int(as_int(v1) + as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(int_to_real(as_int(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= from_float(as_float(v1) + int_to_real(as_int(v2)) );
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(as_float(v1) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= from_string(str.concat(as_string(v1),as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(as_ListAny(v1),as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};


procedure PSub (v1: Any, v2: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) - bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) - as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(as_int(v1) - bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(bool_to_real(as_bool(v1)) - as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= from_float(as_float(v1) - bool_to_real(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= from_int(as_int(v1) - as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(int_to_real(as_int(v1)) - as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= from_float(as_float(v1) - int_to_real(as_int(v2)) );
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(as_float(v1) - as_float(v2));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}
};


function PEq (v: Any, v': Any) : bool {
  normalize_any(v) == normalize_any (v')
}

procedure PMul (v1: Any, v2: Any) returns (ret: Any, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) * bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= from_int(bool_to_int(as_bool(v1)) * as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= from_int(as_int(v1) * bool_to_int(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(bool_to_real(as_bool(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= from_float(as_float(v1) * bool_to_real(as_bool(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == STRING())
  {
    ret:= if as_bool(v1) then v2 else from_string("");
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == BOOL())
  {
    ret:= if as_bool(v2) then v1 else from_string("");
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= from_int(as_int(v1) + as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(int_to_real(as_int(v1)) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= from_float(as_float(v1) + int_to_real(as_int(v2)) );
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == STRING())
  {
    ret:= from_string(string_repeat(as_string(v2), as_int(v1)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == INT())
  {
    ret:= from_string(string_repeat(as_string(v1), as_int(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_repeat(as_ListAny(v2), as_int(v1)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && TypeOf(v2) == INT())
  {
    ret:= from_ListAny(List_repeat(as_ListAny(v1), as_int(v2)));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= from_float(as_float(v1) + as_float(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= from_string(str.concat(as_string(v1),as_string(v2)));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= from_ListAny(List_extend(as_ListAny(v1),as_ListAny(v2)));
    error := NoError ();
  }
  else
  {
    ret := from_none();
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}}}}}}}
};

procedure PLt (v1: Any, v2: Any) returns (ret: bool, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= bool_to_int(as_bool(v1)) < bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= bool_to_int(as_bool(v1)) < as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= as_int(v1) < bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= bool_to_real(as_bool(v1)) < as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= as_float(v1) < bool_to_real(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= as_int(v1) < as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= int_to_real(as_int(v1)) < as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= as_float(v1) < int_to_real(as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= as_float(v1) < as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= string_lt(as_string(v1), as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_lt(as_ListAny(v1),as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};

procedure PLe (v1: Any, v2: Any) returns (ret: bool, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= bool_to_int(as_bool(v1)) <= bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= bool_to_int(as_bool(v1)) <= as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= as_int(v1) <= bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= bool_to_real(as_bool(v1)) <= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= as_float(v1) <= bool_to_real(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= as_int(v1) <= as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= int_to_real(as_int(v1)) <= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= as_float(v1) <= int_to_real(as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= as_float(v1) <= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= string_le(as_string(v1), as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_le(as_ListAny(v1),as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};


procedure PGt (v1: Any, v2: Any) returns (ret: bool, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= bool_to_int(as_bool(v1)) > bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= bool_to_int(as_bool(v1)) > as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= as_int(v1) > bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= bool_to_real(as_bool(v1)) > as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= as_float(v1) > bool_to_real(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= as_int(v1) > as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= int_to_real(as_int(v1)) > as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= as_float(v1) > int_to_real(as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= as_float(v1) > as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= string_gt(as_string(v1), as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_gt(as_ListAny(v1),as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};

procedure PGe (v1: Any, v2: Any) returns (ret: bool, error: Error) {
  if (TypeOf(v1) == BOOL() && TypeOf(v2) == BOOL())
  {
    ret:= bool_to_int(as_bool(v1)) >= bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == INT())
  {
    ret:= bool_to_int(as_bool(v1)) >= as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == BOOL())
  {
    ret:= as_int(v1) >= bool_to_int(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == BOOL() && TypeOf(v2) == FLOAT())
  {
    ret:= bool_to_real(as_bool(v1)) >= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == BOOL())
  {
    ret:= as_float(v1) >= bool_to_real(as_bool(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == INT())
  {
    ret:= as_int(v1) >= as_int(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == INT() && TypeOf(v2) == FLOAT())
  {
    ret:= int_to_real(as_int(v1)) >= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == INT())
  {
    ret:= as_float(v1) >= int_to_real(as_int(v2));
    error := NoError ();
  }
  else {if (TypeOf(v1) == FLOAT() && TypeOf(v2) == FLOAT())
  {
    ret:= as_float(v1) >= as_float(v2);
    error := NoError ();
  }
  else {if (TypeOf(v1) == STRING() && TypeOf(v2) == STRING())
  {
    ret:= string_ge(as_string(v1), as_string(v2));
    error := NoError ();
  }
  else {if (Any..isfrom_ListAny(v1) && Any..isfrom_ListAny(v2))
  {
    ret:= List_ge(as_ListAny(v1),as_ListAny(v2));
    error := NoError ();
  }
  else
  {
    ret := false;
    error := Undefined ("Operand Type is not defined");
  }
  }}}}}}}}}}
};
-/
