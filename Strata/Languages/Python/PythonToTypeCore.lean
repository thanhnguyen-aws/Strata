/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse

import Strata.Languages.Core.Core
import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.FunctionSignatures
import Strata.Languages.Python.Regex.ReToCore
import Strata.Languages.Python.PyFactory
import Strata.Languages.Python.FunctionSignatures
import Strata.Languages.Python.CoreTypePrelude
import StrataTest.Transform.ProcedureInlining
import StrataTest.Internal.InternalCorePrelude
import StrataTest.Internal.InternalFunctionSignatures
import Strata.Languages.Core.Verifier
import Strata.DDM.Ion
import Strata.Util.IO

namespace Strata
open Lambda.LTy.Syntax
open Rat
-- Some hard-coded things we'll need to fix later:


def datetimeType : Core.Expression.Ty := .forAll [] (.tcons "Datetime" [])
def dummyDatetime : Core.Expression.Expr := .fvar () "DUMMY_DATETIME" none


def timedeltaType : Core.Expression.Ty := .forAll [] (.tcons "int" [])
def dummyTimedelta : Core.Expression.Expr := .fvar () "DUMMY_Timedelta" none


def AnyTy : Core.Expression.Ty := .forAll [] (.tcons "Any" [])
def ErrorTy : Core.Expression.Ty := .forAll [] (.tcons "Error" [])
def ClassInstanceTy : Core.Expression.Ty := .forAll [] (.tcons "ClassInstance" [])

def DictTy : Core.Expression.Ty := .forAll [] (.tcons "Dict" [])
def exceptvar : Core.Expression.Expr := .fvar () "exceptvar" none


-------------------------------------------------------------------------------

-- Translating a Python expression can require Core statements, e.g., a function call
-- We translate these by first defining temporary variables to store the results of the stmts
-- and then using those variables in the expression.
structure PyExprTranslated where
  stmts : List Core.Statement
  args : List Core.Expression.Expr := []
  expr: Core.Expression.Expr
  post_stmts : List Core.Statement := []
deriving Inhabited

structure PythonFunctionDecl where
  name : String
  args : List (String × String) -- Elements are (arg_name, arg_ty) where `arg_ty` is the string representation of the type in Python
  ret : String
deriving Repr, BEq, Inhabited

structure PythonClassDecl where
  name : String
  --ClassAttributes: List String
  --InstanceAttribute: List String
deriving Repr, BEq, Inhabited

structure TryBlockInfo where
  ErrorTypes: List String
  TryBlockIndex: String
deriving Inhabited

structure TranslationContext where
  signatures : Python.Signatures
  expectedType : Option (Lambda.LMonoTy) := none
  variableTypes : List (String × Lambda.LMonoTy) := []
  currentTryBlock: Option TryBlockInfo
  func_infos : List PythonFunctionDecl := []
  class_infos : List PythonClassDecl := []
deriving Inhabited

def isVar_inContext (trans_ctx: TranslationContext) (varname: String) : Bool :=
  varname ∈ trans_ctx.variableTypes.unzip.fst

-------------------------------------------------------------------------------
def getFunctions (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.func => decl.name.name::getFunctions t
        | _ => getFunctions t

def PreludeFunctions : List String := getFunctions Core.Typeprelude.decls

def getProcedures (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.proc => decl.name.name::getProcedures t
        | _ => getProcedures t

def getExceptProcedures (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match h: decl.kind with
      |.proc =>
          let p := decl.getProc h
          if p.header.outputs.length > 0 then
            let lastret := p.header.outputs.getLast!.fst.name
            if (lastret == "exception") || (lastret == "error") then
              p.header.name.name :: (getExceptProcedures t)
            else getExceptProcedures t
          else getExceptProcedures t
      | _ => getExceptProcedures t


def PreludeProcedures : List String := getProcedures Core.Typeprelude.decls

def PreludeExceptProcedures : List String := getExceptProcedures Core.Typeprelude.decls

def IgnoredProcedures : List String := ["print", "import", "importFrom"]

--#eval PreludeExceptProcedures

def create_function_app_acc (args: List Core.Expression.Expr) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match args with
  | [] => acc
  | arg :: t => create_function_app_acc t (.app () acc arg)

def create_function_app (fn: String) (args: List Core.Expression.Expr): Core.Expression.Expr :=
  create_function_app_acc args (.op () fn none)

def toPyCommands (a : Array Operation) : Array (Python.Command SourceRange) :=
  a.map (λ op => match Python.Command.ofAst op with
    | .error e => panic! s!"Failed to translate to Python.Command: {e}"
    | .ok cmd => cmd)

def unwrapModule (c : Python.Command SourceRange) : Array (Python.stmt SourceRange) :=
  match c with
  | Python.Command.Module _ body _ => body.val
  | _ => panic! "Expected module"

def strToCoreExpr (s: String) : Core.Expression.Expr :=
  .strConst () s

def intToCoreExpr (i: Int) : Core.Expression.Expr :=
  .intConst () i

def PyIntToInt (i : Python.int SourceRange) : Int :=
  match i with
  | .IntPos _ n => n.val
  | .IntNeg _ n => -n.val

def PyConstToCore (c: Python.constant SourceRange) : Core.Expression.Expr :=
  match c with
  | .ConString _ s => .strConst () s.val
  | .ConPos _ i => .intConst () i.val
  | .ConNeg _ i => .intConst () (-i.val)
  | .ConBytes _ _b => .const () (.strConst "") -- TODO: fix
  | .ConFloat _ f => .strConst () (f.val)
  | .ConTrue _ => .boolConst () true
  | .ConFalse _ => .boolConst () false
  | _ => panic! s!"Unhandled Constant: {repr c}"

def PyAliasToCoreExpr (a : Python.alias SourceRange) : Core.Expression.Expr :=
  match a with
  | .mk_alias _ n as_n =>
  assert! as_n.val.isNone
  .strConst () n.val

-------------------------------------------------------------------------------

def strToAny (s: String) : Core.Expression.Expr :=
  .app () (.op () "from_string" none) (.strConst () s)

def intToAny (i: Int) : Core.Expression.Expr :=
  .app () (.op () "from_int" none) (.intConst () i)

def boolToAny (b: Bool) : Core.Expression.Expr :=
  .app () (.op () "from_bool" none) (.boolConst () b)

def Any_asBool (b: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.op () "as_bool" none) b

def strVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_string" none) (.fvar () varname none)

def intVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_int" none) (.fvar () varname none)

def boolVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_bool" none) (.fvar () varname none)

def DictVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_Dict" none) (.fvar () varname none)

def AnyNoneExpr : Core.Expression.Expr :=
  .op () "from_none" none

def classVarToAny (varname: String) : Core.Expression.Expr :=
  .app () (.op () "from_Class" none) (.fvar () varname none)

def emptyClassInstance (classname: String) : Core.Expression.Expr :=
  .app () (.op () "ClassInstance_empty" none) (.strConst () classname)

def stringToRat (s : String) : Rat :=
  match s.toInt? with
  | some n => n
  | none =>
    let parts := s.splitOn "."
    if parts.length == 2 then
      match parts[0]!.toInt?, parts[1]!.toNat? with
      | some whole, some frac =>
        (mkRat whole frac)
      | _, _ => panic! s!"Cannot convert: {s} to Rat"
    else panic! s!"Cannot convert: {s} to Rat"

def PyConstToAny (c: Python.constant SourceRange) : Core.Expression.Expr :=
  match c with
  | .ConString _ s => strToAny s.val
  | .ConPos _ i => intToAny i.val
  | .ConNeg _ i => intToAny (-i.val)
  | .ConBytes _ _b => .const () (.strConst "") -- TODO: fix
  | .ConFloat _ f => .app () (.op () "from_Float" none) (.realConst () (stringToRat f.val))
  | .ConTrue _ => boolToAny true
  | .ConFalse _ => boolToAny false
  | .ConNone _ => (.op () "from_none" none)
  | _ => panic! s!"Unhandled Constant: {repr c}"


-------------------------------------------------------------------------------

def handleFloorDiv (_translation_ctx: TranslationContext) (lhs rhs: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs) rhs

def handleDictIn (lhs rhs: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (.op () "Any_in_Dict" none) lhs) rhs

def handleAttribute (var: Core.Expression.Expr) (attr: String) : Core.Expression.Expr :=
  .app () (.op () "AnyExcept_unwrap" none) (.app () (.app () (.op () "get_InstanceAttribute" none) var) (strToCoreExpr attr))


-------------------------------------------------------------------------------

structure SubstitutionRecord where
  pyExpr : Python.expr SourceRange
  boogieExpr : Core.Expression.Expr

instance : Repr (List SubstitutionRecord) where
  reprPrec xs _ :=
    let py_exprs := xs.map (λ r => r.pyExpr)
    s!"{repr py_exprs}"

def PyExprIdent (e1 e2: Python.expr SourceRange) : Bool :=
  match e1, e2 with
  | .Call sr1 _ _ _, .Call sr2 _ _ _ => sr1 == sr2
  | _ , _ => false

-- TODO: handle rest of names
def PyListStrToCore (names : Array (Python.alias SourceRange)) : Core.Expression.Expr :=
  .app () (.app () (.op () "ListStr_cons" mty[string → (ListStr → ListStr)]) (PyAliasToCoreExpr names[0]!))
       (.op () "ListStr_nil" mty[ListStr])


def PyOptExprToString (e : Python.opt_expr SourceRange) : String :=
  match e with
  | .some_expr _ (.Constant _ (.ConString _ s) _) => s.val
  | _ => panic! "Expected some constant string: {e}"

partial def PyExprToString (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Attribute _ v attr _ => s!"{PyExprToString v}_{attr.val}"
  | .Subscript _ v slice _ =>
    let v_name := PyExprToString v
    match v_name with
    | "Dict" =>
      match slice with
      | .Tuple _ elts _ =>
        assert! elts.val.size == 2
        s!"Dict[{PyExprToString elts.val[0]!} {PyExprToString elts.val[1]!}]"
      | _ => panic! s!"Unsupported slice: {repr slice}"
    | "List" =>
      match slice with
      | .Name _ id _ => s!"List[{id.val}]"
      | _ => panic! s!"Unsupported slice: {repr slice}"
    | _ => panic! s!"Unsupported subscript to string: {repr e}"
  | _ => panic! s!"Unhandled Expr: {repr e}"

partial def PyExprGetRoot (e : Python.expr SourceRange) : String :=
  match e with
  | .Name _ n _ => n.val
  | .Attribute _ v _ _ => PyExprGetRoot v
  | .Subscript _ v _ _ => PyExprGetRoot v
  | _ => panic! s!"Unhandled Expr: {repr e}"

def PyExprToMonoTy (e : Python.expr SourceRange) : Lambda.LMonoTy :=
  match e with
  | .Name _ n _ =>
    match n.val with
    | "bool" => .tcons "bool" []
    | "int" => .tcons "int" []
    | "str" => .tcons "string" []
    | "float" => .tcons "string" []
    | "Dict[str Any]" => .tcons "DictStrAny" []
    | "List[str]" => .tcons "ListStr" []
    | "datetime" => .tcons "Datetime" []
    | "date" => .tcons "Date" []
    | "timedelta" => .tcons "Timedelta" []
    | "Client" => .tcons "Client" []
    | "LatencyAnalyzer" => .tcons "LatencyAnalyzer" []
    | _ => panic! s!"Unhandled name: {repr e}"
  | .Subscript _ val _slice _ =>
    match val with
    | .Name _ n _ =>
      match n.val with
      | "Dict" => .tcons "DictStrAny" []
      | "List" => .tcons "ListStr" []
      | _ => panic! s!"Unsupported name: {repr n}"
    | _ => panic! s!"Expected name: {repr e}"
  | .Attribute _ _ _ _ => .tcons "Any" []
  | _ => panic! s!"Unhandled Expr: {repr e}"

def AnyTy_var (var: String) := (var, Lambda.LMonoTy.tcons "Any" [])

def isFunctionWithException (funname: String) : Bool :=
  (funname ∈ PreludeExceptProcedures) || (¬ funname ∈ PreludeProcedures)

def deduplicateTypeAnnotations (l : List (String × Option String)) : List (String × String) := Id.run do
  let mut m : Map String String := []
  for p in l do
    let name := p.fst
    let oty := p.snd
    match oty with
    | .some ty =>
      match m.find? name with
      | .some other_ty =>
        if ty != other_ty then
          panic! s!"Type annotation mismatch: {other_ty} vs {ty}"
      | .none => m := (name, ty) :: m
    | .none => ()
  let names := l.map (λ p => p.fst)
  let unique_names := names.dedup
  unique_names.map (λ n =>
    match m.find? n with
    | .some ty => (n, ty)
    | .none => panic s!"Missing type annotations for {n}")

partial def collectVarDecls (stmts: Array (Python.stmt SourceRange)) : List Core.Statement :=
  let rec go (s : Python.stmt SourceRange) : List (String × Option String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := lhs.val.toList.map PyExprToString
      names.map (λ n => (n, "Any"))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body _ => body.val.toList.flatMap go
    | .For _ _ _ body _ _ => body.val.toList.flatMap go
    | .Try _ body handlers _orelse finalbody =>
        let handlers_bodies := handlers.val.toList.map (λ h => match h with
          | .ExceptHandler _ _ _ body => body.val.toList)
        (body.val.toList.flatMap go) ++ (handlers_bodies.flatten.flatMap go) ++ (finalbody.val.toList.flatMap go)
    | _ => []
  let dup := stmts.toList.flatMap go
  let dedup := deduplicateTypeAnnotations dup
  let toCore (p: String × String) : List Core.Statement :=
    let name := p.fst
    let corename := name ++ "_coreval"
    let ty_name := p.snd
    match ty_name with
    | "bool" => [(.init corename t[bool] (.boolConst () false)), (.havoc corename), (.init name AnyTy (boolVarToAny corename))]
    | "str" => [(.init corename t[string] (.strConst () "")), (.havoc corename), (.init name AnyTy (strVarToAny corename))]
    | "int" => [(.init corename t[int] (.intConst () 0)), (.havoc corename), (.init name AnyTy (intVarToAny corename))]
    | "float" => [(.init name t[string] (.strConst () "0.0")), (.havoc name)] -- Floats as strs for now
    | "bytes" => [(.init name t[string] (.strConst () "")), (.havoc name)]
    | "Dict[str Any]" => [(.init corename DictTy (.op () "Dict_empty" none)), (.havoc corename), (.init name AnyTy (DictVarToAny corename))]
    | "List[str]" => [(.init name AnyTy AnyNoneExpr), (.havoc name)]
    | "datetime" => [(.init name datetimeType dummyDatetime), (.havoc name)]
    | "timedelta" => [(.init name timedeltaType dummyTimedelta), (.havoc name)]
    | "Any" => [(.init name AnyTy AnyNoneExpr), (.havoc name)]
    | _ => [(.init corename ClassInstanceTy (emptyClassInstance ty_name) ), (.havoc corename), (.init name AnyTy (classVarToAny corename))]
  let foo := dedup.map toCore
  foo.flatten

def isCall (e: Python.expr SourceRange) : Bool :=
  match e with
  | .Call _ _ _ _ => true
  | _ => false

def remapFname (translation_ctx: TranslationContext) (fname: String) : String :=
  match translation_ctx.class_infos.find? (λ i => i.name == fname) with
  | .some i =>
    i.name ++ "___init__"
  | _ =>
    match fname with
    | "float" => "str_to_float"
    | _ => fname

structure TryCatchContext where
  Err_Label : List (String × String)
deriving Inhabited

def ErrTyToGuard (err_expr: Core.Expression.Expr) (errty: String) : Core.Expression.Expr := match errty with
  | "TypeError" => .app () (.op () "Error..isTypeError" none) err_expr
  | "ZeroDivisionError" => .app () (.op () "Error..isUndefinedError" none) err_expr
  | "AssertionError" => .app () (.op () "Error..isAssertionError" none) err_expr
  | "Exception" => .app () (.op () "Bool.Not" none) (.app () (.op () "Error..isNoError" none) err_expr)
  | _ => panic! ("Unsupport Error Type: " ++ errty)

def create_ErrorHandle_stmt (err_expr: Core.Expression.Expr) (tryblockindex : String) (errtys : List String) : Core.Statement :=
  match errtys with
  | [] => panic! "Cannot be null"
  | errty::[] =>
        let label := errty ++ tryblockindex
        let guard := ErrTyToGuard err_expr errty
        .ite guard [.goto label] []
  | errty::t =>
        let label := errty ++ tryblockindex
        let guard := ErrTyToGuard err_expr errty
        .ite guard [.goto label] [create_ErrorHandle_stmt err_expr tryblockindex t]

def MaybeErrorStmts_to_Stmts (maybe_err_stmts: List (Core.Statement ×  Option Core.Expression.Expr))
                              (errtys : List String)
                              (tryblockindex : String): List Core.Statement :=
  let create_errhandlestmts := maybe_err_stmts.map (λ (stmt, err) =>
      match err with
      | none => [stmt]
      | some err =>  [stmt, create_ErrorHandle_stmt err tryblockindex errtys])
  create_errhandlestmts.flatten

def addExceptionHandle (translation_ctx : TranslationContext) (callstmt: Core.Statement) (sr: SourceRange): List Core.Statement :=
  match callstmt with
  | .call lhs fnname args =>
      if isFunctionWithException fnname then
        let exceptionhandling_stmt := match translation_ctx.currentTryBlock with
        | some tryblockinfo => create_ErrorHandle_stmt exceptvar tryblockinfo.TryBlockIndex tryblockinfo.ErrorTypes
        | _ =>
              let nonerrassert : Core.Expression.Expr := .app () (.op () "Error..isNoError" none) exceptvar
              (.assert s!"safety_assert_{sr.start}_{sr.stop}" nonerrassert)
        [.call (lhs ++ [⟨ "exceptvar", default⟩ ]) fnname args, exceptionhandling_stmt]
      else [callstmt]
  | _ => panic s!"Not a call statement "

mutual

partial def PyExprToCoreWithSubst (translation_ctx : TranslationContext)  (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : PyExprTranslated :=
  PyExprToCore translation_ctx e substitution_records

partial def PyKWordsToCore (kw : Python.keyword SourceRange) : (String × PyExprTranslated) :=
  match kw with
  | .mk_keyword _ name expr =>
    match name.val with
    | some n => (n.val, PyExprToCore default expr)
    | none => panic! "Keyword arg should have a name"

partial def kwargs_mk
    (kv: List (String × PyExprTranslated)) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := .strConst () k
      let val := v.expr
      let dict_insert := .app () (.app () (.app () (.op () "kwargs_set" none) acc) key) val
      kwargs_mk t dict_insert

partial def KwargsToCore  (kwords : Array (Python.keyword SourceRange)): PyExprTranslated :=
  let kws_and_exprs := kwords.toList.map (PyKWordsToCore)
  let ret := kwargs_mk  kws_and_exprs (.op () "kwargs_empty" none)
  let stmts_all := (kws_and_exprs.map (λ (_, pe) => pe.stmts)).flatten
  {stmts := stmts_all , expr := ret, args := []}


partial def Dict_mk (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (kv: List ((Python.opt_expr SourceRange) × (Python.expr SourceRange))) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := strToAny (PyOptExprToString k)
      let val := (PyExprToCore translation_ctx v substitution_records).expr
      let dict_insert := .app () (.app () (.app () (.op () "Dict_insert" none) acc) key) val
      Dict_mk translation_ctx substitution_records t dict_insert

partial def handleDict (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (keys: Array (Python.opt_expr SourceRange)) (values: Array (Python.expr SourceRange)) : PyExprTranslated :=
  assert! keys.size == values.size
  let kv := keys.toList.zip values.toList
  let dict :=  Dict_mk translation_ctx substitution_records kv (.op () "Dict_empty" none)
  let valueDict := .app () (.op () "from_Dict" none) dict
  {stmts := [] , expr := valueDict, post_stmts := []}

partial def List_mk (es: List Core.Expression.Expr) : Core.Expression.Expr := match es with
  | [] => .op () "ListAny_nil" none
  | e::t => .app () (.app () (.op () "ListAny_cons" none) e) (List_mk t)

partial def handleList (elmts: Array (Python.expr SourceRange)) (translation_ctx : TranslationContext): PyExprTranslated :=
  let trans_elmts := elmts.toList.map (PyExprToCore translation_ctx)
  let stmts := (trans_elmts.map (λ x => x.stmts)).flatten
  let expr := List_mk (trans_elmts.map (λ x => x.expr))
  {stmts, expr}

partial def PyCallToCore  (translation_ctx : TranslationContext)
                            (func: Python.expr SourceRange) (sr: SourceRange)
                            (args: Ann (Array (Python.expr SourceRange)) SourceRange)
                            (kwords : Ann (Array (Python.keyword SourceRange)) SourceRange): PyExprTranslated:=
  let (fname, args) := match func with
    | .Name _ n _ => (n.val, args.val.toList)
    | .Attribute _ v attr _ =>
        if (PyExprGetRoot v) ∈ translation_ctx.variableTypes.unzip.1 then
          (attr.val, [v] ++ args.val.toList)
        else (s!"{PyExprToString v}_{attr.val}", args.val.toList)
    | _ => panic! s!"{repr func} is not a function"
  let fname := remapFname translation_ctx fname
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let trans_kwords := KwargsToCore kwords.val
  let trans_kwords_exprs := if kwords.val.size == 0 then [] else [trans_kwords.expr]
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs ++ trans_kwords_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs ++ trans_kwords_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ trans_kwords.stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs ++ trans_kwords_exprs)}
  res

partial def PyBinOpToCore (translation_ctx : TranslationContext)
                        (fname: String)
                        (sr: SourceRange)
                        (lhs: Python.expr SourceRange)
                        (rhs: Python.expr SourceRange): PyExprTranslated:=
  let args:= [lhs, rhs]
  let fname := remapFname translation_ctx fname
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs)}
  res

partial def PyUnOpToCore (translation_ctx : TranslationContext)
                        (fname: String)
                        (sr: SourceRange)
                        (arg: Python.expr SourceRange): PyExprTranslated:=
  let args:= [arg]
  let fname := remapFname translation_ctx fname
  let trans_arg_exprs := (args.map (λ a => (PyExprToCore translation_ctx a none).expr))
  let trans_arg_stmts := (args.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs)) sr)
  let res := {stmts:= trans_arg_stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs)}
  res

partial def PyExprToCore (translation_ctx : TranslationContext) (e : Python.expr SourceRange)
    (substitution_records : Option (List SubstitutionRecord) := none) : PyExprTranslated :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    {stmts := [], expr := record.boogieExpr}
  else
    match e with
    | .Call sr f args kwords => PyCallToCore translation_ctx f sr args kwords
    | .Constant _ c _ => {stmts := [], expr :=  PyConstToAny c}
    | .Name _ n _ =>
      match n.val with
      | "AssertionError" | "Exception" => {stmts := [], expr := .strConst () n.val}
      | s =>
        match translation_ctx.variableTypes.find? (λ p => p.fst == s) with
        | .some p =>
          if translation_ctx.expectedType == some (.tcons "bool" []) && p.snd == (.tcons "DictStrAny" []) then
            let a := .fvar () n.val none
            let e := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) a) (.intConst () 0))
            {stmts := [], expr := e}
          else
            {stmts := [], expr := .fvar () n.val none}
        | .none => {stmts := [], expr := .fvar () n.val none}
    | .JoinedStr _ ss => PyExprToCore translation_ctx ss.val[0]! -- TODO: need to actually join strings
    | .BinOp sr lhs op rhs =>
      match op with
      | .Add _ => PyBinOpToCore translation_ctx "PAdd" sr lhs rhs
      | .Sub _ => PyBinOpToCore translation_ctx "PSub" sr lhs rhs
      | .Mult _ => PyBinOpToCore translation_ctx "PMul" sr lhs rhs
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare sr lhs op rhs =>
      assert! rhs.val.size == 1
      let rhs := rhs.val[0]!
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ => PyBinOpToCore translation_ctx "PEq" sr lhs rhs
        | Strata.Python.cmpop.In _ => PyBinOpToCore translation_ctx "PIn" sr lhs rhs
        | Strata.Python.cmpop.Lt _ => PyBinOpToCore translation_ctx "PLt" sr lhs rhs
        | Strata.Python.cmpop.LtE _ => PyBinOpToCore translation_ctx "PLe" sr lhs rhs
        | Strata.Python.cmpop.Gt _ => PyBinOpToCore translation_ctx "PGt" sr lhs rhs
        | Strata.Python.cmpop.GtE _ => PyBinOpToCore translation_ctx "PGt" sr lhs rhs
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values =>
      let res := handleDict translation_ctx substitution_records keys.val values.val
      res
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp sr op arg => match op with
      | .Not _ => PyUnOpToCore translation_ctx "PNot" sr arg
      | _ => panic! "Unsupported UnaryOp: {repr e}"
    | .Subscript _ v slice _ =>
      let l := PyExprToCore translation_ctx v
      let k := PyExprToCore translation_ctx slice
      -- TODO: we need to plumb the type of `v` here
      match s!"{repr l.expr}" with
      | "LExpr.fvar () { name := \"keys\", metadata := Core.Visibility.unres } none" =>
          -- let access_check : Core.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts, expr := .app () (.app () (.op () "list_str_get" none) l.expr) k.expr}
      | "LExpr.fvar () { name := \"blended_cost\", metadata := Core.Visibility.unres } none" =>
          -- let access_check : Core.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts, expr := .app () (.app () (.op () "dict_str_any_get_str" none) l.expr) k.expr}
      | _ =>
        match translation_ctx.expectedType with
        | .some (.tcons "ListStr" []) =>
          let access_check : Core.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts ++ [access_check], expr := .app () (.app () (.op () "dict_str_any_get_list_str" none) l.expr) k.expr}
        | _ =>
          let access_check : Core.Statement := .assert "subscript_bounds_check" (.app () (.app () (.op () "str_in_dict_str_any" none) k.expr) l.expr)
          {stmts := l.stmts ++ k.stmts ++ [access_check], expr := .app () (.app () (.op () "dict_str_any_get" none) l.expr) k.expr}
    | .List _ elmts _ => handleList elmts.val translation_ctx
    | .Attribute _ v attr _ =>
        let vCore := (PyExprToCore translation_ctx v).expr
        {stmts:= [], expr:= handleAttribute vCore attr.val}
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def initTmpParam (p: Python.expr SourceRange × String) : List Core.Statement :=
  match p.fst with
  | .Call _ f args _ =>
    match f with
    | .Name _ n _ =>
      match n.val with
      | "json_dumps" => [(.init p.snd t[string] (.strConst () "")),
                          .call [p.snd, "maybe_except"] "json_dumps" [(.app () (.op () "DictStrAny_mk" none) (.strConst () "DefaultDict")),
                          (Strata.Python.TypeStrToCoreExpr "IntOrNone")]]
      | "str" =>
        assert! args.val.size == 1
        [(.init p.snd t[string] (.strConst () "")), .set p.snd (.app () (.op () "datetime_to_str" none) ((PyExprToCore default args.val[0]!).expr))]
      | "int" => [(.init p.snd t[int] (.intConst () 0)), .set p.snd (.op () "datetime_to_int" none)]
      | _ => panic! s!"Unsupported name {n.val}"
    | _ => panic! s!"Unsupported tmp param init call: {repr f}"
  | _ => panic! "Expected Call"

partial def exceptHandlersToCoreBlock
        (translation_ctx: TranslationContext)
        (tryblockindex: String)
        (h : Python.excepthandler SourceRange) : Core.Statement :=
  match h with
  | .ExceptHandler _ ex_ty _ body =>
    let finalblocklabel := "finalblock" ++ tryblockindex
    let handler_body := body.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst) ++ [.goto finalblocklabel]
    let blockname := match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty ++ tryblockindex
      | .none => "exception" ++ tryblockindex
    (.block blockname handler_body)

partial def getErrorTypes_fromexceptHandlers (hs : List (Python.excepthandler SourceRange)) : List String :=
  hs.map (λ h =>
  match h with
  | .ExceptHandler _ ex_ty _ _ => match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty
      | .none => "exception")



partial def handleComprehension (lhs: Python.expr SourceRange) (gen: Array (Python.comprehension SourceRange)) : List Core.Statement :=
  assert! gen.size == 1
  match gen[0]! with
  | .mk_comprehension _ _ itr _ _ =>
    let res := PyExprToCore default itr
    let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) res.expr) (.intConst () 0))
    let then_ss: List Core.Statement := [.havoc (PyExprToString lhs)]
    let else_ss: List Core.Statement := [.set (PyExprToString lhs) (.op () "ListStr_nil" none)]
    res.stmts ++ [.ite guard then_ss else_ss]



partial def handleFunctionCall
        (translation_ctx : TranslationContext)
        (lhs:  List String)
        (call_expr: Python.expr SourceRange): List Core.Statement :=
  let call_trans := PyExprToCore translation_ctx call_expr
  let lhs : List Core.Expression.Ident := if lhs.length == 0 then [] else [lhs[0]!]
  match call_expr with
  | (.Call sr _ _ _) =>
      match call_trans.stmts.getLast! with
      | .call _ fn args =>
          let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
          call_trans.stmts.dropLast  ++ newcall
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call _ fn args =>
              let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
              call_trans.stmts.dropLast.dropLast ++  newcall
          | _ => panic! s!"Expect a Call expr"
      | .init _ _ expr => call_trans.stmts.dropLast  ++  [.set lhs[0]! expr]
      | _ => panic! "expect a Call"
  | _ => panic! s!"Expect a Call expr, get {repr call_expr}"

partial def PyStmtToCore (translation_ctx : TranslationContext) (s : Python.stmt SourceRange)
        : List Core.Statement × TranslationContext :=
  --dbg_trace s!"Handling: {repr s}"
  let trans_stmts: List Core.Statement × Option (String × Lambda.LMonoTy) := match s with
    | .Import _ names =>
      ([.call [] "import" [PyListStrToCore names.val]], none)
    | .ImportFrom _ s names i =>
      let n := match s.val with
      | some s => [strToCoreExpr s.val]
      | none => []
      let i := match i.val with
      | some i => [intToCoreExpr (PyIntToInt i)]
      | none => []
      ([.call [] "importFrom" (n ++ [PyListStrToCore names.val] ++ i)], none)
    | .Expr _ (.Call sr func args kwords) =>
      if (PyExprToString func) ∈ IgnoredProcedures then ([], none)
      else
        (handleFunctionCall translation_ctx [] (.Call sr func args kwords), none)
    | .Expr _ (.Constant _ (.ConString _ _) _) =>
      -- TODO: Check that it's a doc string
      ([], none) -- Doc string
    | .Expr _ _ =>
      panic! s!"Can't handle Expr statements that aren't calls: {repr s}"
    | .Assign _ lhs (.Call sr func args kwords) _ =>
      assert! lhs.val.size == 1
      let lhs := PyExprToString lhs.val[0]!
      let call_stmts := handleFunctionCall translation_ctx [lhs] (.Call sr func args kwords)
      if isVar_inContext translation_ctx lhs then
        (call_stmts, some (AnyTy_var lhs))
      else
        ([.init lhs AnyTy AnyNoneExpr] ++ call_stmts, some (AnyTy_var lhs))
    | .Assign _ lhs rhs _ =>
      assert! lhs.val.size == 1
      let lhs := PyExprToString lhs.val[0]!
      let res := PyExprToCore translation_ctx rhs
      if isVar_inContext translation_ctx lhs then
        (res.stmts ++ [(.set lhs res.expr)], some (AnyTy_var lhs))
      else
      (res.stmts ++ [(.init lhs AnyTy res.expr)], some (AnyTy_var lhs))
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.Call sr func args kwords))} _ =>
      let lhs := PyExprToString lhs
      let call_stmts := handleFunctionCall translation_ctx [lhs] (.Call sr func args kwords)
      if isVar_inContext translation_ctx lhs then
        (call_stmts, some (lhs, PyExprToMonoTy ty))
      else
        ([.init lhs AnyTy AnyNoneExpr] ++ call_stmts, some (lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty { ann := _ , val := (.some (.ListComp _ _ gen))} _ => ([], none)
    --  (handleComprehension lhs gen.val, some (PyExprToString lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty {ann := _, val := (.some e)} _ =>
      let lhs := PyExprToString lhs
      let res := (PyExprToCore {translation_ctx with expectedType := PyExprToMonoTy ty} e)
      if isVar_inContext translation_ctx lhs then
        (res.stmts ++ [(.set lhs res.expr)], some (lhs, PyExprToMonoTy ty))
      else
        (res.stmts ++ [(.init lhs AnyTy res.expr)], some (lhs, PyExprToMonoTy ty))
    | .Try sr body handlers _orelse finalbody =>
        let tryblockindex := s!"_{sr.start}_{sr.stop}"
        let tryblockname := "tryblock" ++ tryblockindex
        let finalblockname := "finalblock" ++ tryblockindex
        let ErrorTypes := getErrorTypes_fromexceptHandlers handlers.val.toList
        let curTryblock : TryBlockInfo := {ErrorTypes, TryBlockIndex:= tryblockindex}
        let except_handlers_blocks := handlers.val.toList.map (exceptHandlersToCoreBlock translation_ctx tryblockindex)
        let finalblockbody := finalbody.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst)
        let finalblock :=.block finalblockname finalblockbody
        let translation_ctx := {translation_ctx with currentTryBlock:= some curTryblock}
        --let var_decls := collectVarDecls translation_ctx body.val
        let tryblockbody := body.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst) ++ [.goto finalblockname]
        let tryblock := .block tryblockname tryblockbody
        let stmts : List Core.Statement := [tryblock] ++ except_handlers_blocks ++ [finalblock]
        (stmts ,none)
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Core statement"
    | .If _ test then_b else_b =>
      let guard_ctx := {translation_ctx with expectedType := some (.tcons "bool" [])}
      ([.ite (Any_asBool (PyExprToCore guard_ctx test).expr) (ArrPyStmtToCore translation_ctx then_b.val).fst (ArrPyStmtToCore translation_ctx else_b.val).fst], none)
    | .Return _ v =>
      match v.val with
      | .some v => ([(.set "ret" (PyExprToCore translation_ctx v).expr), (.goto "end")], none) -- TODO: need to thread return value name here. For now, assume "ret"
      | .none => ([(.goto "end")], none)
    | .For _ tgt itr body _ _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToCore default itr).expr) (.intConst () 0))
      match tgt with
      | .Name _ n _ =>
        let assign_tgt := [(.init n.val AnyTy AnyNoneExpr)]
        ([(.ite guard (assign_tgt ++ (ArrPyStmtToCore translation_ctx body.val).fst) [])], none)
      | _ => panic! s!"tgt must be single name: {repr tgt}"
      -- TODO: missing havoc
    | .While _ test body _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToCore default test).expr) (.intConst () 0))
      ([(.ite guard (ArrPyStmtToCore translation_ctx body.val).fst [])], none)
      -- TODO: missing havoc
    | .Assert pos a _ =>
      let res := PyExprToCore translation_ctx a
      let assertname := s!"py_assertion_line_{pos.start}_col_{pos.stop}"
      let assert_expr := Any_asBool res.expr
      (res.stmts ++ [(.assert assertname assert_expr)], none)
    | .AugAssign _ lhs op rhs =>
      match op with
      | .Add _ =>
        match lhs with
        | .Name _ n _ =>
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := (.strConst () "DUMMY_FLOAT")
          (rhs.stmts ++ [(.set n.val new_lhs)], none)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | .FloorDiv _ =>
        match lhs with
        | .Name _ n _ =>
          let lhs := PyExprToCore translation_ctx lhs
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs.expr) rhs.expr
          (rhs.stmts ++ [(.set n.val new_lhs)], none)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | _ => panic! s!"Unsupported AugAssign op: {repr op}"
    | .Pass _ => ([], none)
    | _ => panic! s!"Unsupported {repr s}"
  let new_translation_ctx := match trans_stmts.snd with
  | .some s => {translation_ctx with variableTypes := s :: translation_ctx.variableTypes}
  | .none => translation_ctx
  (trans_stmts.fst, new_translation_ctx)

partial def ArrPyStmtToCore (translation_ctx: TranslationContext) (a : Array (Python.stmt SourceRange)) : (List Core.Statement × TranslationContext) :=
  a.foldl (fun (stmts, ctx) stmt =>
    let (newStmts, newCtx) := PyStmtToCore ctx stmt
    (stmts ++ newStmts, newCtx)
  ) ([], translation_ctx)

end --mutual


def translateFunctions (a : Array (Python.stmt SourceRange)) (translation_ctx: TranslationContext) : List Core.Decl :=
  a.toList.filterMap (λ s => match s with
    | .FunctionDef _ name _args body _ _ret _ _ =>

      let varDecls : List Core.Statement := []
      let proc : Core.Procedure := {
        header := {
               name := name.val,
               typeArgs := [],
               inputs := [],
               outputs := [("exceptvar", (.tcons "Error" []))]},
        spec := default,
        body := varDecls ++ (ArrPyStmtToCore translation_ctx body.val).fst ++ [.block "end" []]
      }
      some (.proc proc)
    | _ => none)

def isSubstring (needle : String) (haystack : String) : Bool :=
  let needleLen := needle.length
  let haystackLen := haystack.length
  if needleLen > haystackLen then false
  else
    (List.range (haystackLen - needleLen + 1)).any fun i =>
      String.Pos.Raw.extract haystack ⟨i⟩  ⟨i + needleLen⟩ == needle

def IsOrType (ty_str: String) : Bool := isSubstring "Or" ty_str

def pyTyStrToLMonoTy (ty_str: String) : Lambda.LMonoTy :=
  match ty_str with
  | "str" => mty[string]
  | "int" => mty[int]
  | "bool" => mty[bool]
  | "datetime" => (.tcons "Datetime" [])
  | _ =>
    if IsOrType ty_str then (.tcons "Any" []) else
      panic! s!"Unsupported type: {ty_str}"

def arg_typecheck_assertion (var: String) (ty_str: String) : Core.Expression.Expr :=
  match ty_str.toLower with
  | "str" => .app () (.op () "isStr" none) (.fvar () var none)
  | "int" => .app () (.op () "isInt" none) (.fvar () var none)
  | "bool" => .app () (.op () "isBool" none) (.fvar () var none)
  | "datetime" => .app () (.op () "isDatetime" none) (.fvar () var none)
  | "none" => .app () (.op () "isNone" none) (.fvar () var none)
  | _ => panic! s!"Unsupported type: {ty_str}"

def arg_typecheck_or_expr (var: String) (ty_strs: List String) : Core.Expression.Expr :=
  match ty_strs with
  | [] => panic! "ty_strs cannot be empty"
  | [ty] => arg_typecheck_assertion var ty
  | ty::tys => .app () (.app () (.op () "Bool.Or" none) (arg_typecheck_assertion var ty)) (arg_typecheck_or_expr var tys)

def getArg_typecheck_assertions (var: String) (ty: String) : Core.Statement :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    .assert assertionname (arg_typecheck_or_expr var typelist)
  else .assert assertionname (arg_typecheck_assertion var ty)

def getArgs_typecheck_assertions (args: List (String × String)) : List Core.Statement :=
  match args with
  | [] => []
  | (var, typ)::t => (getArg_typecheck_assertions var typ) :: (getArgs_typecheck_assertions t)

def getArg_typecheck_precond (var: String) (ty: String) : (Core.CoreLabel × Core.Procedure.Check) :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    (assertionname, {expr:=arg_typecheck_or_expr var typelist})
  else (assertionname, {expr:=arg_typecheck_assertion var ty})

def getArgs_typecheck_preconds (args: List (String × String)) : ListMap Core.CoreLabel Core.Procedure.Check :=
  match args with
  | [] => []
  | (var, typ)::t => if typ == "Any" then (getArgs_typecheck_preconds t) else
            (getArg_typecheck_precond var typ) :: (getArgs_typecheck_preconds t)

def pythonFuncToCore (name : String) (args: List (String × String)) (body: Array (Python.stmt SourceRange))
      (ret : Option (Python.expr SourceRange)) (spec : Core.Procedure.Spec) (translation_ctx : TranslationContext) : Core.Procedure :=
  let inputs : List (Lambda.Identifier Core.Visibility × Lambda.LMonoTy) := args.map (λ p => (p.fst, (.tcons "Any" [])))
  --let varDecls := collectVarDecls translation_ctx body
  --++ [(.init "exception_ty_matches" t[bool] (.boolConst () false)), (.havoc "exception_ty_matches")]
  let arg_typecheck := getArgs_typecheck_preconds args
  let newspec := {spec with preconditions:= arg_typecheck ++ spec.preconditions}
  let stmts := (ArrPyStmtToCore translation_ctx body).fst
  --let body := varDecls ++ stmts ++ [.block "end" []]
  let body := stmts ++ [.block "end" []]
  let constructor := name.endsWith "___init__"
  let outputs : Lambda.LMonoTySignature := if not constructor then
    [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]
  else
    let class_ty_name := name.dropRight ("___init__".length)
    [("ret", (.tcons s!"{class_ty_name}" [])), ("exceptvar", (.tcons "Error" []))]
  {
    header := {name,
               typeArgs := [],
               inputs,
               outputs},
    spec:=newspec,
    body
  }

def unpackPyArguments (args: Python.arguments SourceRange) : List (String × String) :=
-- Python AST:
-- arguments = (arg* posonlyargs, arg* args, arg? vararg, arg* kwonlyargs,
--                  expr* kw_defaults, arg? kwarg, expr* defaults)
  match args with -- TODO: Error if any other types of args
  | .mk_arguments _ _ args _ _ _ _ _ =>
    let combined := args.val
    combined.toList.filterMap (λ a =>
    match a with
    | .mk_arg _ name oty _ =>
      if name.val == "self" then
        none
      else
        match oty.val with
        | .some ty => some (name.val, PyExprToString ty)
        | _ => some (name.val, "Any"))

def PyFuncDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × PythonFunctionDecl :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ =>
    let args := unpackPyArguments args
    ([.proc (pythonFuncToCore name.val args body.val ret.val default translation_ctx)], {name := name.val, args, ret := s!"{repr ret}"})
  | _ => panic! s!"Expected function def: {repr s}"

def PyClassDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × PythonClassDecl :=
  match s with
  | .ClassDef _ c_name _ _ body _ _ =>
    let member_fn_defs := body.val.toList.filterMap (λ s => match s with
      | .FunctionDef _ name args body _ ret _ _ => some (name, args, body, ret)
      | _ => none)
    (member_fn_defs.map (λ f =>
      let name := f.fst.val
      let args := unpackPyArguments f.snd.fst
      let body := f.snd.snd.fst.val
      let ret := f.snd.snd.snd.val
      .proc (pythonFuncToCore (c_name.val++"_"++name) args body ret default translation_ctx)), {name := c_name.val})
  | _ => panic! s!"Expected function def: {repr s}"

def pythonToCore (pgm: Strata.Program): Core.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | _ => false)

  let class_defs := insideMod.filter (λ s => match s with
  | .ClassDef _ _ _ _ _ _ _ => true
  | _ => false)

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | .ClassDef _ _ _ _ _ _ _ => false
  | _ => true)

  let globals := [(.var "__name__" (.forAll [] mty[string]) (.strConst () "__main__"))]

  let rec helper {α : Type} (f : Python.stmt SourceRange → TranslationContext → List Core.Decl × α)
               (update : TranslationContext → α → TranslationContext)
               (acc : TranslationContext) :
               List (Python.stmt SourceRange) → List Core.Decl × TranslationContext
  | [] => ([], acc)
  | x :: xs =>
    let (y, info) := f x acc
    let new_acc := update acc info
    let (ys, acc'') := helper f update new_acc xs
    (y ++ ys, acc'')

  let func_defs_and_infos := helper PyFuncDefToCore (fun acc info => {acc with func_infos := info :: acc.func_infos}) default func_defs.toList
  let func_defs := func_defs_and_infos.fst
  let func_infos := func_defs_and_infos.snd

  let class_defs_and_infos := helper PyClassDefToCore (fun acc info => {acc with class_infos := info :: acc.class_infos}) func_infos class_defs.toList
  let class_defs := class_defs_and_infos.fst
  let class_infos := class_defs_and_infos.snd
  let class_ty_decls := [(.type (.con {name := "LatencyAnalyzer", numargs := 0})) ]

  {decls := globals ++ class_ty_decls ++ func_defs ++ class_defs ++ [.proc (pythonFuncToCore "__main__" [] non_func_blocks none default class_infos)]}


def exitFailure {α} (message : String) : IO α := do
  IO.eprintln (message  ++ "\n\nRun strata --help for additional help.")
  IO.Process.exit 1

def readPythonStrata (path : String) : IO Strata.Program := do
  let bytes ← Strata.Util.readBinInputSource path
  if ! Ion.isIonFile bytes then
    exitFailure s!"pyAnalyze expected Ion file"
  match Strata.Program.fileFromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok p => pure p
  | .error msg => exitFailure msg


def getCoreProgram (path : String) : IO Core.Program := do
  let pgm ← readPythonStrata path
  let bpgm := Strata.pythonToCore pgm
  return bpgm


def verifyCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  IO.print newPgm
  let verboseMode := VerboseMode.ofBool false
  let vcResults ← IO.FS.withTempDir (fun tempDir =>
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify "cvc5" newPgm tempDir
              { Options.default with stopOnFirstError := false, verbose := verboseMode, removeIrrelevantAxioms := true }
                                      (moreFns := Strata.Python.ReFactory)))
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  IO.println s

def verifyInliningCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  let newPgm :=  runInlineCall newPgm
  let filterdecls := newPgm.decls.filter (λ d => ! d.name.name ∈ Strata.PyOps)
  let newPgm: Core.Program := { decls := filterdecls}
  IO.print newPgm
  let verboseMode := VerboseMode.ofBool false
  let vcResults ← IO.FS.withTempDir (fun tempDir =>
          EIO.toIO
            (fun f => IO.Error.userError (toString f))
            (Core.verify "cvc5" newPgm tempDir
              { Options.default with stopOnFirstError := false, verbose := verboseMode, removeIrrelevantAxioms := true }
                                      (moreFns := Strata.Python.ReFactory)))
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  IO.println s

def partialEvalCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  let options := { Options.default with stopOnFirstError := false, verbose:= VerboseMode.ofBool true, removeIrrelevantAxioms := false}
  let peval := Core.typeCheckAndPartialEval options newPgm
  match peval with
  | .ok pval => IO.println s!"{pval[1]!.fst}"
  | _ => IO.println s!"partial evaluation failed"

def partialEvalInliningCoreProgram (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Core.Typeprelude
  let bpgm := Strata.pythonToCore pgm
  let newPgm : Core.Program := { decls := preludePgm.decls ++ bpgm.decls }
  let newPgm :=  runInlineCall newPgm
  let options := { Options.default with stopOnFirstError := false, verbose:= VerboseMode.ofBool false, removeIrrelevantAxioms := false}
  let peval := Core.typeCheckAndPartialEval options newPgm
  match peval with
  | .ok pval =>
      for p in pval do
        IO.println s!"Branch"
        IO.println s!"{p.fst}"
  | _ => IO.println s!"partial evaluation failed"

end Strata
