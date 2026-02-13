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
import Strata.Languages.Core.Verifier
import Strata.Languages.Python.PyEval
import Strata.DDM.Ion
import Strata.Util.IO

namespace Strata
open Lambda.LTy.Syntax
open Rat


-------------------------------------------------------------------------------

--CoreTypePrelude types
def AnyTy : Core.Expression.Ty := .forAll [] (.tcons "Any" [])
def KwargsTy : Core.Expression.Ty := .forAll [] (.tcons "kwargs" [])
def ErrorTy : Core.Expression.Ty := .forAll [] (.tcons "Error" [])
def DictTy : Core.Expression.Ty := .forAll [] (.tcons "Dict" [])
def ClassInstanceTy : Core.Expression.Ty := .forAll [] (.tcons "ClassInstance" [])

--CoreTypePrelude functions

def getFunctions (decls: List Core.Decl) : List String :=
  match decls with
  | [] => []
  | decl::t => match decl.kind with
        |.func => decl.name.name::getFunctions t
        | _ => getFunctions t

def Any_testers := ["Any..isfrom_none", "Any..isfrom_bool", "Any..isfrom_int", "Any..isfrom_float",
       "Any..isfrom_string", "Any..isfrom_datetime", "Any..isfrom_ListAny", "Any..isfrom_Dict",
       "Any..isfrom_ClassInstance"]

def Any_constructors := ["from_none", "from_bool", "from_int", "from_float",
       "from_string", "from_datetime", "from_ListAny", "from_Dict", "from_ClassInstance"]

def Any_destructors := ["Any..as_none", "Any..as_bool", "Any..as_int", "Any..as_float",
       "Any..as_string", "Any..as_datetime", "Any..as_ListAny", "Any..as_Dict",
       "Any..classname", "Any..instance_attributes"]


def PreludeFunctions : List String := (getFunctions Core.Typeprelude.decls) ++ Any_testers
                    ++ Any_constructors ++ Any_destructors

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

-------------------------------------------------------------------------------

--Core.Expression.Expr constructing
def FVar(name: String) : Core.Expression.Expr := .fvar () name none
def exceptvar : Core.Expression.Expr := .fvar () "exceptvar" none
def UndefinedError : Core.Expression.Expr := .app () (.op () "UndefinedError" none) (.strConst () "")

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

def Any_toBool (b: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.op () "Any_to_bool" none) b

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
  .app () (.op () "from_ClassInstance" none) (.fvar () varname none)

def emptyClassInstance (classname: String) : Core.Expression.Expr :=
  .app () (.op () "ClassInstance_empty" none) (.strConst () classname)

def KwargsEmpty: Core.Expression.Expr :=
  .op () "kwargs_empty" none

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
  | .ConFloat _ f => .app () (.op () "from_float" none) (.realConst () (stringToRat f.val))
  | .ConTrue _ => boolToAny true
  | .ConFalse _ => boolToAny false
  | .ConNone _ => (.op () "from_none" none)
  | _ => panic! s!"Unhandled Constant: {repr c}"

def TypeOfPyConst (c: Python.constant SourceRange) : String :=
  match c with
  | .ConString _ _ => "string"
  | .ConPos _ _ => "int"
  | .ConNeg _ _ => "int"
  | .ConBytes _ _ => "string"
  | .ConFloat _ _ => "float"
  | .ConTrue _ => "bool"
  | .ConFalse _ => "bool"
  | .ConNone _ => "none"
  | _ => panic! s!"Unhandled Constant: {repr c}"

-------------------------------------------------------------------------------

def handleFloorDiv (_translation_ctx: TranslationContext) (lhs rhs: Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs) rhs

-------------------------------------------------------------------------------

-- Translating a Python expression can require Core statements, e.g., a function call
-- We translate these by first defining temporary variables to store the results of the stmts
-- and then using those variables in the expression.

structure PyExprTranslated where
  stmts : List Core.Statement
  args : List Core.Expression.Expr := []
  expr: Core.Expression.Expr
  post_stmts : List Core.Statement := []
  type : String := "Any"
deriving Inhabited

structure PythonFunctionDecl where
  name : String
  args : List (String × String × Option (Python.expr SourceRange)) -- Elements are (arg_name, arg_ty) where `arg_ty` is the string representation of the type in Python
  ret : String
deriving Repr, Inhabited

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
  variableTypes : Std.HashMap String String:= {}
  currentTryBlock: Option TryBlockInfo
  func_infos : List PythonFunctionDecl := []
  class_infos : List PythonClassDecl := []
  currentclassname : String := ""
  currentfunctionname : String := ""
  classinstance_attributetype: Std.HashMap (String × String) String := {}
deriving Inhabited

def Type_of_var (trans_ctx: TranslationContext) (varname: String) : String :=
  match trans_ctx.variableTypes.get? varname with
  | some "Any" => "UnknownType"
  | some ty => ty
  | _ => "UnknownType"

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
      | _ => "List[Any]"
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
    | "float" => .tcons "real" []
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

partial def collectVars (stmts: Array (Python.stmt SourceRange)) : List (String × String) :=
  let rec go (s : Python.stmt SourceRange) : List (String × String) :=
    match s with
    | .Assign _ lhs _ _ =>
      let names := (lhs.val.toList.filter (λ e => match e with |.Name _ _ _ => true | _=> false)).map PyExprToString
      names.map (λ n => (n, "Any"))
    | .AnnAssign _ lhs ty _ _ =>
      [(PyExprToString lhs, PyExprToString ty)]
    | .If _ _ body elsebody => body.val.toList.flatMap go ++ elsebody.val.toList.flatMap go
    | .For _ _ _ body _ _ => body.val.toList.flatMap go
    | .Try _ body handlers _orelse finalbody =>
        let handlers_bodies := handlers.val.toList.map (λ h => match h with
          | .ExceptHandler _ _ _ body => body.val.toList)
        let error_var := (handlers.val.toList.filterMap (λ h => match h with
          | .ExceptHandler _ _ errname _ => errname.val)).map (λ h => (h.val, "Any"))
        error_var ++ (body.val.toList.flatMap go) ++ (handlers_bodies.flatten.flatMap go) ++ (finalbody.val.toList.flatMap go)
    | _ => []
  let dup := stmts.toList.flatMap go
  dup

partial def vardecls (stmts: Array (Python.stmt SourceRange)) : List Core.Statement :=
  let vars := (collectVars stmts).unzip.fst.dedup
  let vardecs: List (List Core.Statement):= vars.map (λ v: String => [.init v AnyTy AnyNoneExpr, .havoc v])
  vardecs.flatten

def isCall (e: Python.expr SourceRange) : Bool :=
  match e with
  | .Call _ _ _ _ => true
  | _ => false

def ErrTyToGuard (err_expr: Core.Expression.Expr) (err_ty: String) : Core.Expression.Expr := match err_ty with
  | "TypeError" => .app () (.op () "Error..isTypeError" none) err_expr
  | "ZeroDivisionError" => .app () (.op () "Error..isUndefinedError" none) err_expr
  | "AssertionError" => .app () (.op () "Error..isAssertionError" none) err_expr
  | "Exception" => .app () (.op () "Bool.Not" none) (.app () (.op () "Error..isNoError" none) err_expr)
  | _ => .app () (.op () "Bool.Not" none) (.app () (.op () "Error..isNoError" none) err_expr)

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

def addExceptionHandle (translation_ctx : TranslationContext) (callstmt: Core.Statement) (sr: SourceRange) (count : Nat := 0): List Core.Statement :=
  match callstmt with
  | .call lhs fnname args =>
      if isFunctionWithException fnname then
        let exceptionhandling_stmt := match translation_ctx.currentTryBlock with
          | some tryblockinfo => create_ErrorHandle_stmt exceptvar tryblockinfo.TryBlockIndex tryblockinfo.ErrorTypes
          | _ =>
              let nonerrassert : Core.Expression.Expr := .app () (.op () "Error..isNoError" none) exceptvar
              let assertlabel := if count == 0 then s!"safety_assert_{sr.start}_{sr.stop}"
                                else s!"safety_assert_{sr.start}_{sr.stop}_{count}"
              (.assert assertlabel nonerrassert)
        let exceptvarident : Core.Expression.Ident := "exceptvar"
        [.call (lhs ++ [exceptvarident]) fnname args, exceptionhandling_stmt]
      else [callstmt]
  | _ => panic s!"Not a call statement "

mutual

partial def PyExprToCoreWithSubst (translation_ctx : TranslationContext)  (substitution_records : Option (List SubstitutionRecord)) (e : Python.expr SourceRange) : PyExprTranslated :=
  PyExprToCore translation_ctx e substitution_records

partial def PyKWordsToCore (kw : Python.keyword SourceRange) : (String × PyExprTranslated) :=
  match kw with
  | .mk_keyword sr name expr =>
    match name.val with
    | some n => (n.val, PyExprToCore default expr)
    | none => panic! s!"Keyword arg should have a name {sr.start} {sr.stop}"

partial def PyKWordsToHashMap (kwords : List (Python.keyword SourceRange)) : Std.HashMap String (Python.expr SourceRange) :=
  kwords.foldl (λ hashmap kw =>
    match kw with
      | .mk_keyword _ name expr =>
        match name.val with
        | some n => hashmap.insert n.val expr
        | none => hashmap)
    {}

partial def kwargs_mk
    (kv: List (String × PyExprTranslated)) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := .strConst () k
      let val := v.expr
      let dict_insert := .app () (.app () (.app () (.op () "kwargs_set" none) acc) key) val
      kwargs_mk t dict_insert

partial def isDictKwargs (kwords : List (Python.keyword SourceRange)) : Bool :=
  if kwords.length == 0 then false else
  match kwords[0]! with
  | .mk_keyword _ name _ =>
    match name.val with
    | some _ => false
    | none => true

partial def DictKwargsToCore (kwords : List (Python.keyword SourceRange)) : PyExprTranslated :=
  match kwords[0]! with
  | .mk_keyword _ name expr =>
    match name.val with
    | some _ => panic! s!"Keyword arg should be a Dict"
    | none =>
        let dict:= PyExprToCore default expr
        {dict with expr:= .app () (.op () "Any_to_kwargs" none) dict.expr}

partial def KwargsToCore  (kwords : List (Python.keyword SourceRange)): PyExprTranslated :=
  if isDictKwargs kwords then DictKwargsToCore kwords else
    let kws_and_exprs := kwords.map (PyKWordsToCore)
    let ret := kwargs_mk  kws_and_exprs (.op () "kwargs_empty" none)
    let stmts_all := (kws_and_exprs.map (λ (_, pe) => pe.stmts)).flatten
    {stmts := stmts_all , expr := ret, args := []}

partial def KwargsFilter (kwords : List (Python.keyword SourceRange)) (funcdecl: PythonFunctionDecl) : List (Python.keyword SourceRange) :=
  kwords.filter (λ kw => match kw with
    | .mk_keyword _ name _ =>
      match name.val with
        | some n => n.val ∉ funcdecl.args.unzip.fst
        | none => True)

partial def CombinePositionalAndKeywordArgs
    (posargs: List (Python.expr SourceRange))
    (kwords : List (Python.keyword SourceRange))
    (funcdecl: PythonFunctionDecl) : (List (Python.expr SourceRange)) × (List (Python.keyword SourceRange) × Bool):=
  let kwordargs := KwargsFilter kwords funcdecl
  let kwords := PyKWordsToHashMap kwords
  let posargs := funcdecl.args.unzip.fst.zip posargs
  let funcdeclsargs:= funcdecl.args
  let funcdecl_has_kwargs := if funcdeclsargs.isEmpty then false else funcdeclsargs.getLast!.fst == "kw"
  let funcdeclsargs := if funcdecl_has_kwargs then funcdeclsargs.dropLast else funcdeclsargs
  let funcdeclsargs := funcdeclsargs.drop posargs.length
  let args := funcdeclsargs.map (λ (name, _, default) =>
    match kwords.get? name with
    | some expr => (name, expr)
    | none => match default with | .some default => (name, default) | _ => panic! "Must have a default")
  let posargs := posargs.unzip.snd ++ args.unzip.snd
  (posargs, kwordargs, funcdecl_has_kwargs)

partial def Dict_mk (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (kv: List ((Python.opt_expr SourceRange) × (Python.expr SourceRange))) (acc: Core.Expression.Expr): Core.Expression.Expr :=
  match kv with
  | [] => acc
  | (k,v)::t =>
      let key := strToAny (PyOptExprToString k)
      let val := (PyExprToCore translation_ctx v substitution_records).expr
      let dict_insert := .app () (.app () (.app () (.op () "Dict_set_func" none) acc) key) val
      Dict_mk translation_ctx substitution_records t dict_insert

partial def DictToCore (translation_ctx : TranslationContext) (substitution_records : Option (List SubstitutionRecord) := none)
    (keys: Array (Python.opt_expr SourceRange)) (values: Array (Python.expr SourceRange)) : PyExprTranslated :=
  assert! keys.size == values.size
  let kv := keys.toList.zip values.toList
  let val_stmts := (kv.unzip.snd.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let dict :=  Dict_mk translation_ctx substitution_records kv (.op () "Dict_empty" none)
  let valueDict := .app () (.op () "from_Dict" none) dict
  {stmts := val_stmts , expr := valueDict, post_stmts := []}

partial def List_mk (es: List Core.Expression.Expr) : Core.Expression.Expr := match es with
  | [] => .op () "ListAny_nil" none
  | e::t => .app () (.app () (.op () "ListAny_cons" none) e) (List_mk t)

partial def ListToCore (elmts: Array (Python.expr SourceRange)) (translation_ctx : TranslationContext): PyExprTranslated :=
  let trans_elmts := elmts.toList.map (PyExprToCore translation_ctx)
  let stmts := (trans_elmts.map (λ x => x.stmts)).flatten
  let expr := .app () (.op () "from_ListAny" none) (List_mk (trans_elmts.map (λ x => x.expr)))
  {stmts, expr}

partial def breakdown_Attribute (expr: Python.expr SourceRange): (Python.expr SourceRange) × List String :=
  match expr with
  | .Attribute _ v attr _ =>
      let ret := (breakdown_Attribute v)
      (ret.fst , ret.snd ++ [attr.val])
  | _ => (expr, [])

partial def breakdown_Attribute_with_SourceRange (expr: Python.expr SourceRange)
  : (Python.expr SourceRange) × List (String × SourceRange) :=
  match expr with
  | .Attribute _ v attr _ =>
      let ret := (breakdown_Attribute_with_SourceRange v)
      (ret.fst , ret.snd ++ [(attr.val, attr.ann)])
  | _ => (expr, [])
--------------------------------------------------------------------
-- Function Call handling

partial def remapFname (translation_ctx: TranslationContext) (fname: String) : String :=
  match translation_ctx.class_infos.find? (λ i => i.name == fname) with
  | .some i =>
    i.name ++ "___init__"
  | _ =>
    match fname with
    | "str" => "to_string_any"
    | "len" => "Any_len_to_Any"
    | _ => fname

partial def get_attributes_type (translation_ctx : TranslationContext) (headtype: String) (attributes: List String) : String :=
  if headtype ∈  ["package", "Any"] then headtype else
  match attributes with
  | [] => headtype
  | attr::attrs =>
      match translation_ctx.classinstance_attributetype.get? (headtype, attr) with
      | some ty => get_attributes_type translation_ctx ty attrs
      | _ => "Any"

partial def get_Attribute_root_type (translation_ctx : TranslationContext) (expr: Python.expr SourceRange): String :=
  let (head, attrs) := breakdown_Attribute expr
  match head with
  | .Name _ n _ =>
      if n.val == "self" then get_attributes_type translation_ctx translation_ctx.currentclassname attrs else
      match translation_ctx.variableTypes.get? n.val with
                | none => "package"
                | some "Any" => "UnknownType"
                | some headty => get_attributes_type translation_ctx headty attrs
  | _ => "UnknownType"


/-
Python function call can be a.function_name(arg1, arg2, ...)
If a is a variable, this should be translated to type_of_a_function_name (a, arg1, arg2)
If a is a package, this should be translated to a_function_name (arg1, arg2)
If the function_name is a class, add __init__ into it
The following function return a tuple (translated function name, first argument)
-/

partial def refineFunctionCallExpr (translation_ctx : TranslationContext) (func: Python.expr SourceRange) :
        (String × Option (Python.expr SourceRange)) :=
  match func with
    | .Name _ n _ => (remapFname translation_ctx n.val, none)
    | .Attribute _ v attr _ =>
        let some_firstarg := some v
        let callerty := get_Attribute_root_type translation_ctx v
        let callname := attr.val
        if callerty == "package" then (PyExprToString func, none) else
          (callerty ++ "_" ++ callname, some_firstarg)
    | _ => panic! s!"{repr func} is not a function"

partial def getFunctionReturnType (translation_ctx : TranslationContext) (fname: String) : String :=
  match translation_ctx.func_infos.find? (λ f => f.name == fname) with
  | some funcinfo => funcinfo.ret
  | _ => "UnknownType"

partial def CallExprToCore  (translation_ctx : TranslationContext)
                            (func: Python.expr SourceRange) (sr: SourceRange)
                            (args: List (Python.expr SourceRange))
                            (kwords : List (Python.keyword SourceRange)): PyExprTranslated:=
  let (fname, opt_firstarg) := refineFunctionCallExpr translation_ctx func
  let args := match opt_firstarg with | some firstarg => firstarg::args | _ => args
  let (args, kwords, funcdecl_has_kwargs) := match translation_ctx.func_infos.find? (λ x => x.name == fname) with
    | .some funcdecl => CombinePositionalAndKeywordArgs args kwords funcdecl
    | _ => (args, kwords, false)
  let trans_args := (args.map (λ a => PyExprToCore translation_ctx a none))
  let trans_arg_exprs := (trans_args.map (λ a => a.expr))
  let trans_arg_stmts := (trans_args.map (λ a => a.stmts)).flatten
  let trans_kwords := KwargsToCore kwords
  let trans_kwords_exprs :=
    if kwords.length == 0 then
      if funcdecl_has_kwargs then [KwargsEmpty] else []
    else [trans_kwords.expr]
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs ++ trans_kwords_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs ++ trans_kwords_exprs)) sr)
  let retty := getFunctionReturnType translation_ctx fname
  {stmts:= trans_arg_stmts ++ trans_kwords.stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs ++ trans_kwords_exprs), type := retty}


partial def PyOpToCore (translation_ctx : TranslationContext)
                        (fname: String)
                        (sr: SourceRange)
                        (args: List (Python.expr SourceRange))
                      : PyExprTranslated:=
  let fname := remapFname translation_ctx fname
  let trans_args := (args.map (λ a => PyExprToCore translation_ctx a none))
  let trans_arg_exprs := (trans_args.map (λ a => a.expr))
  let trans_arg_stmts := (trans_args.map (λ a => a.stmts)).flatten
  let tempvarname := s!"tmpvar_{sr.start}_{sr.stop}"
  let fvar_expr : Core.Expression.Expr := .fvar () tempvarname none
  let inittemp  :=
    if fname ∈ PreludeFunctions then
      let expr:=create_function_app fname (trans_arg_exprs)
      [.init tempvarname AnyTy expr]
    else (.init tempvarname AnyTy AnyNoneExpr)::
      (addExceptionHandle translation_ctx (.call [tempvarname] fname (trans_arg_exprs)) sr)
  {stmts:= trans_arg_stmts ++ inittemp, expr:= fvar_expr, args:= (trans_arg_exprs), type := getFunctionReturnType translation_ctx fname}

partial def SubscriptExprToCore (translation_ctx : TranslationContext) (expr : Python.expr SourceRange) : PyExprTranslated :=
  let (start, slices) := match breakdown_Subscript expr with
    | first :: slices => (first, slices)
    | _ =>  panic! "Invalid Subscript Expr"
  let start := PyExprToCore translation_ctx start none
  match slices with
  | [] => panic! "expect subscript"
  | [_] =>
    match expr with
    | .Subscript _ v slice _ =>
        let sr := slice.toAst.ann
        PyOpToCore translation_ctx "Any_get" sr [v, slice]
    | _ => panic! "expect subscript"
  | _ =>
  let slice_exprs := slices.map (λ a => ((PyExprToCore translation_ctx a none).expr))
  let slices_stmts := (slices.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let list_slice_exprs := LEToListAny slice_exprs
  let set_expr := .app () (.app () (.op () "Any_gets_func" none) start.expr) list_slice_exprs
  {expr:= set_expr, stmts:= start.stmts ++ slices_stmts}

partial def AttributeExprToCore_forClass (translation_ctx : TranslationContext) (ss: SourceRange) (start: String)
    (keys: List (String × SourceRange)):
    PyExprTranslated :=
  match keys with
  | [] => {stmts:= [], expr:= FVar start}
  | (slice, sr)::slices =>
    let tempvarget := s!"temp_{ss.start}_{ss.stop}_{slices.length}_get"
    let getstmt := Core.Statement.call [tempvarget] "get_InstanceAttribute" [FVar start, .strConst () slice]
    let getstmts := [.init tempvarget AnyTy AnyNoneExpr] ++ addExceptionHandle translation_ctx getstmt sr
    let tail_trans:= AttributeExprToCore_forClass translation_ctx ss tempvarget slices
    {stmts:= getstmts ++ tail_trans.stmts, expr:= tail_trans.expr}


partial def AttributeExprToCore (translation_ctx : TranslationContext) (expr : Python.expr SourceRange): PyExprTranslated :=
  let roottype := get_Attribute_root_type translation_ctx expr
  match roottype with
  | "package" =>
    let varname := PyExprToString expr
    {stmts:= [.init varname AnyTy AnyNoneExpr], expr:= FVar varname}
  | _ =>
  let (start, slices) := match breakdown_Attribute_with_SourceRange expr with
    | (.Name _ n _, slices)  => (n.val, slices)
    | _ => panic! "Invalid Subscript Expr"
  AttributeExprToCore_forClass translation_ctx (expr.toAst.ann) start slices


partial def PyExprToCore (translation_ctx : TranslationContext) (e : Python.expr SourceRange)
    (substitution_records : Option (List SubstitutionRecord) := none) : PyExprTranslated :=
  if h : substitution_records.isSome && (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).isSome then
    have hr : (List.find? (fun r => PyExprIdent r.pyExpr e) substitution_records.get!).isSome = true := by rw [Bool.and_eq_true] at h; exact h.2
    let record := (substitution_records.get!.find? (λ r => PyExprIdent r.pyExpr e)).get hr
    {stmts := [], expr := record.boogieExpr}
  else
    match e with
    | .Call sr f args kwords => CallExprToCore translation_ctx f sr args.val.toList kwords.val.toList
    | .Constant _ c _ => {stmts := [], expr :=  PyConstToAny c, type := TypeOfPyConst c}
    | .Name _ n _ => {stmts := [], expr := .fvar () n.val none, type:= Type_of_var translation_ctx n.val}
    | .JoinedStr _ ss => PyExprToCore translation_ctx ss.val[0]! -- TODO: need to actually join strings
    | .BoolOp _ op values =>
      match op with
      | .And _ =>
          let lhs:= values.val[0]!
          let rhs:= values.val[1]!
          let sr := {rhs.toAst.ann with stop:=⟨rhs.toAst.ann.stop.byteIdx -1⟩}
          PyOpToCore translation_ctx "PAnd" sr [lhs,rhs]
      | .Or _ =>
          let lhs:= values.val[0]!
          let rhs:= values.val[1]!
          let sr := {rhs.toAst.ann with stop:=⟨rhs.toAst.ann.stop.byteIdx -1⟩}
          PyOpToCore translation_ctx "POr" sr [lhs,rhs]
    | .BinOp _ lhs op rhs =>
      let sr := {rhs.toAst.ann with stop:=⟨rhs.toAst.ann.stop.byteIdx -1⟩}
      match op with
      | .Add _ => PyOpToCore translation_ctx "PAdd" sr [lhs,rhs]
      | .Sub _ => PyOpToCore translation_ctx "PSub" sr [lhs,rhs]
      | .Mult _ => PyOpToCore translation_ctx "PMul" sr [lhs,rhs]
      | .Div _ => PyOpToCore translation_ctx "PDiv" sr [lhs,rhs]
      | .Pow _ => PyOpToCore translation_ctx "PPow" sr [lhs,rhs]
      | _ => panic! s!"Unhandled BinOp: {repr e}"
    | .Compare _ lhs op rhs =>
      assert! rhs.val.size == 1
      let rhs := rhs.val[0]!
      let sr := {rhs.toAst.ann with stop:=⟨rhs.toAst.ann.stop.byteIdx -1⟩}
      match op.val with
      | #[v] => match v with
        | Strata.Python.cmpop.Eq _ => PyOpToCore translation_ctx "PEq" sr [lhs,rhs]
        | Strata.Python.cmpop.NotEq _ => PyOpToCore translation_ctx "PNEq" sr [lhs,rhs]
        | Strata.Python.cmpop.In _ => PyOpToCore translation_ctx "PIn" sr [lhs,rhs]
        | Strata.Python.cmpop.Lt _ => PyOpToCore translation_ctx "PLt" sr [lhs,rhs]
        | Strata.Python.cmpop.LtE _ => PyOpToCore translation_ctx "PLe" sr [lhs,rhs]
        | Strata.Python.cmpop.Gt _ => PyOpToCore translation_ctx "PGt" sr [lhs,rhs]
        | Strata.Python.cmpop.GtE _ => PyOpToCore translation_ctx "PGe" sr [lhs,rhs]
        | _ => panic! s!"Unhandled comparison op: {repr op.val}"
      | _ => panic! s!"Unhandled comparison op: {repr op.val}"
    | .Dict _ keys values => DictToCore translation_ctx substitution_records keys.val values.val
    | .ListComp _ keys values => panic! "ListComp must be handled at stmt level"
    | .UnaryOp sr op arg => match op with
      | .Not _ => PyOpToCore translation_ctx "PNot" sr [arg]
      | .USub _ => PyOpToCore translation_ctx "PNeg" sr [arg]
      | _ => panic! s!"Unsupported UnaryOp: {repr e}"
    | .Subscript _ v slice ctx =>
        SubscriptExprToCore translation_ctx e
    | .List _ elmts _ => ListToCore elmts.val translation_ctx
    | .Attribute sr v attr _ => AttributeExprToCore translation_ctx e
    | .Tuple _ tup _ => ListToCore tup.val translation_ctx
    | .GeneratorExp _ a b => {stmts:= [], expr:= AnyNoneExpr}
    | _ => panic! s!"Unhandled Expr: {repr e}"

partial def exceptHandlersToCoreBlock
        (translation_ctx: TranslationContext)
        (tryblockindex: String)
        (h : Python.excepthandler SourceRange) : Core.Statement :=
  match h with
  | .ExceptHandler _ ex_ty _ body =>
    let error_ty:= match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty
      | .none => "exception"
    let finalblocklabel := "finalblock" ++ tryblockindex
    let handler_body := body.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst) ++ [.goto finalblocklabel]
    let blockname := error_ty ++ tryblockindex
    (.block blockname handler_body)

partial def getErrorTypes_fromexceptHandlers (hs : List (Python.excepthandler SourceRange)) : List String :=
  hs.map (λ h =>
  match h with
  | .ExceptHandler _ ex_ty _ _ => match ex_ty.val with
      | .some ex_ty => PyExprToString ex_ty
      | .none => "exception")

partial def get_tempvarname_of_call_trans (call_trans: PyExprTranslated) : String :=
  match call_trans.stmts.getLast! with
      | .call tempvarname _ _ => tempvarname[0]!.name
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call tempvarname _ _ =>tempvarname[0]!.name
          | _ => panic! s!"Expect a Call expr"
      | .init tempvarname _ _ => tempvarname.name
      | _ => panic! "expect a Call"

partial def breakdown_Subscript (expr:  Python.expr SourceRange) : List ( Python.expr SourceRange) :=
  match expr with
  | .Subscript _ val slice _ => (breakdown_Subscript val) ++ [slice]
  | _ => [expr]

partial def SubscriptGetStmts (translation_ctx : TranslationContext) (ss: SourceRange) (start: String)
    (keys: List (Core.Expression.Expr × SourceRange)):
    List (Core.Statement) :=
  match keys with
  | [] => []
  | [_] => []
  | (slice, sr)::slices =>
    let tempvarget := s!"temp_{ss.start}_{ss.stop}_{slices.length}_get"
    let getstmt := Core.Statement.call [tempvarget] "Any_get" [FVar start, slice]
    let getstmts := [.init tempvarget AnyTy AnyNoneExpr] ++ addExceptionHandle translation_ctx getstmt sr
    getstmts ++ SubscriptGetStmts translation_ctx ss tempvarget slices

partial def SubscriptSetStmts (translation_ctx : TranslationContext) (ss: SourceRange) (start: String)
      (keys: List (Core.Expression.Expr × SourceRange))
      (val: Core.Expression.Expr) (count: Nat):
    List (Core.Statement) :=
  match keys with
  | [] => []
  | [(slice, sr)] =>
    let setstmt := Core.Statement.call [start] "Any_set" [FVar start, slice, val]
    addExceptionHandle translation_ctx setstmt sr
  | (slice, sr)::slices =>
    let tempvarset := s!"temp_{ss.start}_{ss.stop}_{count}_set"
    let tempvarget := s!"temp_{ss.start}_{ss.stop}_{count + 1}_get"
    let setstmt := Core.Statement.call [tempvarset] "Any_set" [FVar tempvarget, slice, val]
    let setstmts := [.init tempvarset AnyTy AnyNoneExpr] ++ addExceptionHandle translation_ctx setstmt sr 1
    setstmts ++ SubscriptSetStmts translation_ctx ss start slices (FVar tempvarset) (count + 1)

partial def SubscriptAssignToCore (translation_ctx : TranslationContext) (ss: SourceRange)
    (expr:  Python.expr SourceRange) (rhs: Core.Expression.Expr)
    : List (Core.Statement) :=
  let (start, slices) := match breakdown_Subscript expr with
    | (.Name _ n _) :: slices => (n.val, slices)
    | _ => panic! "Invalid Subscript Expr"
  let slice_exprs := slices.map (λ a => ((PyExprToCore translation_ctx a none).expr, a.toAst.ann))
  let slices_stmts := (slices.map (λ a => (PyExprToCore translation_ctx a none).stmts)).flatten
  let getstmts := SubscriptGetStmts translation_ctx ss start slice_exprs
  let setstmts := SubscriptSetStmts translation_ctx ss start slice_exprs.reverse rhs 0
  slices_stmts ++ getstmts ++ setstmts

partial def AttributeGetStmts (translation_ctx : TranslationContext) (ss: SourceRange) (start: String)
    (keys: List (String × SourceRange)):
    List (Core.Statement) :=
  match keys with
  | [] => []
  | [_] => []
  | (slice, sr)::slices =>
    let tempvarget := s!"temp_{ss.start}_{ss.stop}_{slices.length}_get"
    let getstmt := Core.Statement.call [tempvarget] "get_InstanceAttribute" [FVar start, .strConst () slice]
    let getstmts := [.init tempvarget AnyTy AnyNoneExpr] ++ addExceptionHandle translation_ctx getstmt sr
    getstmts ++ AttributeGetStmts translation_ctx ss tempvarget slices

partial def AttributeSetStmts (translation_ctx : TranslationContext) (ss: SourceRange) (start: String)
      (keys: List (String × SourceRange))
      (val: Core.Expression.Expr) (count: Nat):
    List (Core.Statement) :=
  let init_or_set_func := if translation_ctx.currentfunctionname.endsWith "init__" then
                                "init_InstanceAttribute"
                          else "set_InstanceAttribute"
  match keys with
  | [] => []
  | [(slice, sr)] =>
    let setstmt := Core.Statement.call [start] init_or_set_func [FVar start, .strConst () slice, val]
    addExceptionHandle translation_ctx setstmt sr
  | (slice, sr)::slices =>
    let tempvarset := s!"temp_{ss.start}_{ss.stop}_{count}_set"
    let tempvarget := s!"temp_{ss.start}_{ss.stop}_{count + 1}_get"
    let setstmt := Core.Statement.call [tempvarset] init_or_set_func [FVar tempvarget, .strConst () slice, val]
    let setstmts := [.init tempvarset AnyTy AnyNoneExpr] ++ addExceptionHandle translation_ctx setstmt sr 1
    setstmts ++ AttributeSetStmts translation_ctx ss start slices (FVar tempvarset) (count + 1)

partial def AttributeAssignToCore (translation_ctx : TranslationContext) (ss: SourceRange)
    (expr:  Python.expr SourceRange) (rhs: Core.Expression.Expr)
    : List (Core.Statement) :=
  let (start, slices) := match breakdown_Attribute_with_SourceRange expr with
    | (.Name _ n _, slices)  => (n.val, slices)
    | _ => panic! "Invalid Subscript Expr"
  let getstmts := AttributeGetStmts translation_ctx ss start slices
  let setstmts := AttributeSetStmts translation_ctx ss start slices.reverse rhs 0
  getstmts ++ setstmts


partial def handleAssignFunctionCall
        (translation_ctx : TranslationContext)
        (lhs:  Python.expr SourceRange)
        (call_expr: Python.expr SourceRange): List Core.Statement :=
  let call_trans := PyExprToCore translation_ctx call_expr
  match call_expr with
  | (.Call sr _ _ _) =>
    match lhs with
    | .Name _ n _ =>
      let lhs : List Core.Expression.Ident := [n.val]
      replaceCallTmpwithLHS translation_ctx sr lhs call_trans
    | .Subscript _ _ _ _ =>
      call_trans.stmts ++ (SubscriptAssignToCore translation_ctx (lhs.toAst.ann) lhs call_trans.expr)
    | .Attribute _ _ _ _ =>
      call_trans.stmts ++ AttributeAssignToCore translation_ctx (lhs.toAst.ann) lhs call_trans.expr
    | _ => panic! s!"Unexpected LHS"
  | _ => panic! s!"Expect a Call expr, get {repr call_expr}"


partial def replaceCallTmpwithLHS
        (translation_ctx : TranslationContext)
        (sr : SourceRange)
        (lhs:  List (Core.Expression.Ident))
        (call_trans: PyExprTranslated): List Core.Statement :=
    match call_trans.stmts.getLast! with
      | .call _ fn args =>
          let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
          (call_trans.stmts.dropLast.dropLast)  ++ newcall
      | .ite _ _ _
      | .assert _ _ _
        => match call_trans.stmts.dropLast.getLast! with
          | .call _ fn args =>
              let newcall := addExceptionHandle translation_ctx (.call lhs fn args) sr
              (call_trans.stmts.dropLast.dropLast.dropLast) ++  newcall
          | _ => panic! s!"Expect a Call expr"
      | .init _ _ expr => call_trans.stmts.dropLast  ++  [.set lhs[0]! expr]
      | _ => panic! "expect a Call"

partial def AssignToCore  (translation_ctx : TranslationContext)
                          (lhs: Python.expr SourceRange) (rhs: Python.expr SourceRange)
                    :List Core.Statement × TranslationContext :=
  let (rhs, iscall) := (PyExprToCore translation_ctx rhs, isCall rhs)
  let sr := lhs.toAst.ann
  match lhs with
    | .Name _ val _ =>
          let lhs := val.val
          let stmts:= if iscall then replaceCallTmpwithLHS translation_ctx sr [val.val] rhs
                else rhs.stmts ++ [(.set lhs rhs.expr)]
          (stmts,
              {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs rhs.type})
    | .Subscript _ _ _ _ =>
          (rhs.stmts ++ SubscriptAssignToCore translation_ctx (lhs.toAst.ann) lhs rhs.expr, translation_ctx)
    | .Attribute _ _ att _ =>
          (rhs.stmts ++ AttributeAssignToCore translation_ctx (lhs.toAst.ann) lhs rhs.expr,
          if (breakdown_Attribute lhs).snd.length == 1 then
          {translation_ctx with classinstance_attributetype :=
            translation_ctx.classinstance_attributetype.insert (translation_ctx.currentclassname, att.val) rhs.type}
          else translation_ctx
          )
    | _ => panic! s!"Invalid LHS"

partial def IfStmtToCore (translation_ctx : TranslationContext)
    (cond: Python.expr SourceRange)
    (thenblock: Array (Python.stmt SourceRange))
    (elseblock: Array (Python.stmt SourceRange))
        : List Core.Statement × TranslationContext :=
  let cond := PyExprToCore translation_ctx cond
  let thenblock := ArrPyStmtToCore translation_ctx thenblock
  let elseblock := ArrPyStmtToCore translation_ctx elseblock
  let newvarTypes:= Std.HashMap.union thenblock.snd.variableTypes elseblock.snd.variableTypes
  (cond.stmts ++ [.ite (Any_toBool cond.expr) thenblock.fst elseblock.fst],
    {translation_ctx with variableTypes := newvarTypes})

partial def StrataHavocToCore (varname: String) (vartype: String) : List Core.Statement :=
  let initstmt := match vartype with
  | "string" => .init varname (.forAll [] (.tcons "string" [])) (.strConst () "")
  | "int" => .init varname (.forAll [] (.tcons "int" [])) (.intConst () 1)
  | _ => panic! "jk"
  [initstmt, .havoc varname]


partial def PyStmtToCore (translation_ctx : TranslationContext) (s : Python.stmt SourceRange)
        : List Core.Statement × TranslationContext :=
  --dbg_trace s!"Handling: {repr s}"
  match s with
    | .Import _ _ => ([], translation_ctx)
    | .ImportFrom _ _ _ _ => ([], translation_ctx)
    | .Expr _ (.Call sr func args kwords) =>
      if (PyExprGetRoot func) == "StrataHavoc" then
        let varname := PyExprGetRoot args.val[0]!
        let varty := match (args.val[1]!) with
          |.Constant _ (.ConString _ a ) _ => a.val
          | _ => panic! "unsupport"
        (StrataHavocToCore varname varty, translation_ctx)
      else
      let fname := (refineFunctionCallExpr translation_ctx func).fst
      if fname ∈ IgnoredProcedures then ([], translation_ctx)
      else
        let call := PyExprToCore translation_ctx (.Call sr func args kwords)
        (call.stmts, translation_ctx)
        --(replaceCallTmpwithLHS translation_ctx sr [] call, translation_ctx)
    | .Expr _ (.Constant _ (.ConString _ _) _) =>
      -- TODO: Check that it's a doc string
      ([], translation_ctx) -- Doc string
    | .Expr _ _ =>
      panic! s!"Can't handle Expr statements that aren't calls: {repr s}"
    | .Assign _ lhs rhs _ =>
      assert! lhs.val.size == 1
      let lhs := lhs.val[0]!
      AssignToCore translation_ctx lhs rhs
    | .AnnAssign _ lhs _ { ann := _ , val := (.some (.Call sr func args kwords))} _ =>
      let call_stmts := handleAssignFunctionCall translation_ctx lhs (.Call sr func args kwords)
      match lhs with
      | .Name _ val _ =>
          let lhs := val.val
          (call_stmts,
            {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs "Any"})
      | .Subscript _ _ _ _ => (call_stmts, translation_ctx)
      | _ => panic! s!"Invalid LHS"
    | .AnnAssign _ _ _ { ann := _ , val := (.some (.ListComp _ _ _))} _ =>
        panic! "List Comp is not yet supported"
    --  (handleComprehension lhs gen.val, some (PyExprToString lhs, PyExprToMonoTy ty))
    | .AnnAssign _ lhs ty {ann := _, val := (.some e)} _ =>
      let lhs := PyExprToString lhs
      let res := (PyExprToCore {translation_ctx with expectedType := PyExprToMonoTy ty} e)
      (res.stmts ++ [(.set lhs res.expr)],
        {translation_ctx with variableTypes := translation_ctx.variableTypes.insert lhs (PyExprToString ty)})
    | .Try sr body handlers _orelse finalbody =>
        let tryblockindex := s!"_{sr.start}_{sr.stop}"
        let tryblockname := "tryblock" ++ tryblockindex
        let finalblockname := "finalblock" ++ tryblockindex
        let ErrorTypes := getErrorTypes_fromexceptHandlers handlers.val.toList
        let curTryblock : TryBlockInfo := {ErrorTypes, TryBlockIndex:= tryblockindex}
        let except_handlers_blocks := handlers.val.toList.map (exceptHandlersToCoreBlock translation_ctx tryblockindex)
        let finalblockbody := finalbody.val.toList.flatMap (λ s => (PyStmtToCore translation_ctx s).fst)
        let finalblock :=.block finalblockname finalblockbody
        let new_translation_ctx := {translation_ctx with currentTryBlock:= some curTryblock}
        let tryblockbody := ArrPyStmtToCore new_translation_ctx body.val
        let tryblock := .block tryblockname tryblockbody.fst
        let stmts : List Core.Statement := [tryblock] ++ except_handlers_blocks ++ [finalblock]
        (stmts,
        {translation_ctx with variableTypes := tryblockbody.snd.variableTypes})
    | .FunctionDef _ _ _ _ _ _ _ _ => panic! "Can't translate FunctionDef to Core statement"
    | .If _ cond then_b else_b =>
        IfStmtToCore translation_ctx cond then_b.val else_b.val
    | .Return _ v =>
      match v.val with
      | .some v =>
          let ret := (PyExprToCore translation_ctx v)
          (ret.stmts ++ [(.set "ret" ret.expr), (.goto "end")], translation_ctx) -- TODO: need to thread return value name here. For now, assume "ret"
      | .none => ([(.goto "end")], translation_ctx)
    | .For _ tgt itr body _ _ =>
      -- Do one unrolling:
      let itr_trans := PyExprToCore translation_ctx itr
      let guard := .app () (.op () "Bool.Not" none)
            (.eq () (.app () (.op () "List_len" none) (.app () (.op () "Any..as_ListAny" none) itr_trans.expr))
            (.intConst () 0))
      match tgt with
      | .Name _ n _ =>
        let assume_contain:= .assume "" (.app () (.app () (.op () "List_contains" none) (.app () (.op () "Any..as_ListAny" none) (PyExprToCore default itr).expr))
                        (FVar n.val))
        let assign_tgt := [(.init n.val AnyTy AnyNoneExpr), .havoc n.val,  assume_contain]
        (itr_trans.stmts ++ [(.ite guard (assign_tgt ++ (ArrPyStmtToCore translation_ctx body.val).fst) [])], translation_ctx)
      | _ => panic! s!"tgt must be single name: {repr tgt}"
      -- TODO: missing havoc
    | .While _ test body _ =>
      -- Do one unrolling:
      let guard := .app () (.op () "Bool.Not" none) (.eq () (.app () (.op () "dict_str_any_length" none) (PyExprToCore default test).expr) (.intConst () 0))
      ([(.ite guard (ArrPyStmtToCore translation_ctx body.val).fst [])], translation_ctx)
      -- TODO: missing havoc
    | .Assert pos a _ =>
      let res := PyExprToCore translation_ctx a
      let assertname := s!"py_assertion_line_{pos.start}_col_{pos.stop}"
      let assert_expr := Any_toBool res.expr
      (res.stmts ++ [(.assert assertname assert_expr)], translation_ctx)
    | .AugAssign _ lhs op rhs =>
      match op with
      | .Add _ =>
        match lhs with
        | .Name _ n _ =>
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := (.strConst () "DUMMY_FLOAT")
          (rhs.stmts ++ [(.set n.val new_lhs)], translation_ctx)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | .FloorDiv _ =>
        match lhs with
        | .Name _ n _ =>
          let lhs := PyExprToCore translation_ctx lhs
          let rhs := PyExprToCore translation_ctx rhs
          let new_lhs := .app () (.app () (.op () "Int.Div" mty[int → (int → int)]) lhs.expr) rhs.expr
          (rhs.stmts ++ [(.set n.val new_lhs)], translation_ctx)
        | _ => panic! s!"Expected lhs to be name: {repr lhs}"
      | _ => panic! s!"Unsupported AugAssign op: {repr op}"
    | .Pass _ => ([], translation_ctx)
    | .Raise _ _ _ => ([.set "exceptvar" UndefinedError], translation_ctx)
    | _ => panic! s!"Unsupported {repr s}"


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

def arg_typecheck_assertion (var: String) (ty_str: String) (default: Option (Python.expr SourceRange)): Core.Expression.Expr :=
  let constraint := match ty_str.toLower with
  | "str" => .app () (.op () "Any..isfrom_string" none) (.fvar () var none)
  | "int" => .app () (.op () "Any..isfrom_int" none) (.fvar () var none)
  | "bool" => .app () (.op () "Any..isfrom_bool" none) (.fvar () var none)
  | "datetime" => .app () (.op () "Any..isfrom_datetime" none) (.fvar () var none)
  | "none" => .app () (.op () "Any..isfrom_none" none) (.fvar () var none)
  | _ => if ty_str.startsWith "Dict" then .app () (.op () "Any..isfrom_Dict" none) (.fvar () var none)
      else if ty_str.startsWith "List" then .app () (.op () "Any..isfrom_ListAny" none) (.fvar () var none)
      else .eq () (.app () (.op () "Any..classname" none) (.fvar () var none)) (.strConst () ty_str)
  match default with
    |.some (.Constant _ (.ConNone _) _ ) =>
      .app () (.app () (.op () "Bool.Or" none) constraint) (.app () (.op () "Any..isfrom_none" none) (.fvar () var none))
    | _ => constraint

def arg_typecheck_or_expr (var: String) (ty_strs: List String) : Core.Expression.Expr :=
  match ty_strs with
  | [] => panic! "ty_strs cannot be empty"
  | [ty] => arg_typecheck_assertion var ty none
  | ty::tys => .app () (.app () (.op () "Bool.Or" none) (arg_typecheck_assertion var ty none)) (arg_typecheck_or_expr var tys)

def getArg_typecheck_assertions (var: String) (ty: String) (default: Option (Python.expr SourceRange)): Core.Statement :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    .assert assertionname (arg_typecheck_or_expr var typelist)
  else .assert assertionname (arg_typecheck_assertion var ty default)

def defautmd: Imperative.MetaData Core.Expression := default

def getArg_typecheck_precond (var: String) (ty: String) (default: Option (Python.expr SourceRange)): (Core.CoreLabel × Core.Procedure.Check) :=
  let typelist := ty.splitOn "Or"
  let assertionname := var ++ "_typeconstraint"
  if IsOrType ty then
    (assertionname, {expr:=arg_typecheck_or_expr var typelist, md:= defautmd })
  else (assertionname, {expr:=arg_typecheck_assertion var ty default, md:= defautmd})

def getArgs_typecheck_preconds (args: List (String × String × Option (Python.expr SourceRange))) : ListMap Core.CoreLabel Core.Procedure.Check :=
  match args with
  | [] => []
  | (var, typ, default)::t => if (typ == "Any"  || typ == "kwargs") then (getArgs_typecheck_preconds t) else
            (getArg_typecheck_precond var typ default) :: (getArgs_typecheck_preconds t)

def getArgs_typecheck_assertions (args: List (String × String × Option (Python.expr SourceRange))) : List Core.Statement :=
  let preconds := getArgs_typecheck_preconds args
  preconds.map (λ (name, check) => .assert name check.expr)

def pythonFuncToCore (name : String) (args: List (String × String × Option (Python.expr SourceRange))) (body: Array (Python.stmt SourceRange))
      (ret : Option (Python.expr SourceRange)) (spec : Core.Procedure.Spec) (translation_ctx : TranslationContext) : Core.Procedure × TranslationContext:=
  let inputtypes := Std.HashMap.ofList (args.map (fun (name,type,_) => (name, type)))
  let translation_ctx := {translation_ctx with currentfunctionname := name, variableTypes:= inputtypes}
  let constructor := name.endsWith "___init__"
  let args := if constructor then args.tail else args
  let inputs : List (Lambda.Identifier Core.Visibility × Lambda.LMonoTy) :=
      args.map (λ p => if p.snd.fst == "kwargs" then (p.fst, (.tcons "kwargs" [])) else (p.fst, (.tcons "Any" [])))
  let arg_typecheck := getArgs_typecheck_preconds args
  let arg_typecheck_assertions_stmts := getArgs_typecheck_assertions args
  let vardec_stmts := vardecls body
  let stmts := (ArrPyStmtToCore translation_ctx body).fst
  let newctx := (ArrPyStmtToCore translation_ctx body).snd
  let body := arg_typecheck_assertions_stmts ++ [.set "exceptvar" (.op () "NoError" none)] ++ vardec_stmts ++ stmts
  let body := if constructor then
      [.init "self" AnyTy (emptyClassInstance translation_ctx.currentclassname)] ++ body ++ [.set "ret" (FVar "self")]
    else body
  let body := body ++ [.block "end" []]
  let ret_typecheck : ListMap Core.CoreLabel Core.Procedure.Check :=
    if constructor then
      let class_ty_name := (name.dropEnd ("___init__".length)).toString
      [("ret_typeconstraint",
        {expr:= .eq () (.app () (.op () "Any..classname" none) (FVar "ret")) (strToCoreExpr class_ty_name), md:= default} )]
    else
      match ret with
      | some ret =>
       [("ret_typeconstraint",
        {expr:= arg_typecheck_assertion "ret" (PyExprToString ret) none, md:= default})]
      | _ => []
  let newspec := {spec with preconditions:= arg_typecheck ++ spec.preconditions
                            postconditions:= ret_typecheck ++ spec.postconditions}
  let outputs : Lambda.LMonoTySignature := match ret with
      | some _ => [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]
      | _ => if constructor then [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]
              else --[("exceptvar", (.tcons "Error" []))]
              [("ret", (.tcons "Any" [])), ("exceptvar", (.tcons "Error" []))]

  let outproc := {
    header := {name,
               typeArgs := [],
               inputs,
               outputs},
    spec:=newspec,
    body
  }
  let newctx:= {translation_ctx with classinstance_attributetype:= newctx.classinstance_attributetype, currentfunctionname := ""}
  (outproc, newctx)

def ArgumentTypeToString (arg: Python.expr SourceRange) : String :=
  match arg with
  | .Name _ n _ => n.val
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
      | _ => "List[Any]"
    | "Optional" => "NoneOr" ++ ArgumentTypeToString slice
    | _ => panic! s!"Unsupported subscript to string: {repr arg}"
  | _ => panic! s!"Unhandled Expr: {repr arg}"

def unpackPyArguments (args: Python.arguments SourceRange) : List (String × String × Option (Python.expr SourceRange)) :=
  match args with
    | .mk_arguments _ _ args _ _ _ kwargs defaults =>
      let argscount := args.val.size
      let defaultscount := defaults.val.size;
      let listdefaults := (List.range (argscount - defaultscount)).map (λ _ => none)
                        ++ defaults.val.toList.map (λ x => some x)
      let argsinfo := args.val.toList.zip listdefaults
      let argtypes :=
        argsinfo.map (λ a: Python.arg SourceRange × Option (Python.expr SourceRange) =>
        match a.fst with
          | .mk_arg _ name oty _ =>
            match oty.val with
              | .some ty => (name.val, ArgumentTypeToString ty, a.snd)
              | _ => (name.val, "Any", a.snd))
      match kwargs.val with
      | .none => argtypes
      | _ => argtypes ++ [("kw", "kwargs", none)]


def PyFuncDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × TranslationContext :=
  match s with
  | .FunctionDef _ name args body _ ret _ _ =>
    let args := unpackPyArguments args
    let retty := match ret.val with
    | none => "UnknownType"
    | some ty => PyExprToString ty
    let funcdecl := {name := name.val, args, ret := retty}
    let transproc := pythonFuncToCore name.val args body.val ret.val default translation_ctx
    ([.proc transproc.fst],
      {translation_ctx with func_infos:= translation_ctx.func_infos ++ [funcdecl]})
  | _ => panic! s!"Expected function def: {repr s}"

def PyClassDefToCore (s: Python.stmt SourceRange) (translation_ctx: TranslationContext) : List Core.Decl × TranslationContext :=
  match s with
  | .ClassDef _ c_name _ _ body _ _ =>
    let member_fn_defs := body.val.toList.filterMap (λ s => match s with
      | .FunctionDef _ name args body _ ret _ _ => some (name, args, body, ret)
      | _ => none)
    let funcinfos : List PythonFunctionDecl := member_fn_defs.map (λ f =>
      let name := c_name.val++"_" ++ f.fst.val
      let args := unpackPyArguments f.snd.fst
      let args := if name.endsWith "___init__" then args.drop 1 else args
      let ret := f.snd.snd.snd.val
      let ret := match ret with
        | none => "UnknownType"
        | some ty => PyExprToString ty
      let ret := if name.endsWith "___init__" then c_name.val else ret
      {name := name, args, ret := ret})
    let translation_ctx := {translation_ctx with func_infos:= translation_ctx.func_infos ++ funcinfos,
                                                  currentclassname := c_name.val}
    let getattributetype := match member_fn_defs.find? (λ f => f.fst.val.endsWith "init__") with
      | some f =>
          let name := c_name.val++"_" ++ f.fst.val
          let args := unpackPyArguments f.snd.fst
          let body := f.snd.snd.fst.val
          let ret := f.snd.snd.snd.val
          (pythonFuncToCore name args body ret default translation_ctx).snd
      | none => panic! s!"require a constructor {c_name.val}"
    let translation_ctx := {translation_ctx with classinstance_attributetype:= getattributetype.classinstance_attributetype}
    let funcdecls : List Core.Decl := member_fn_defs.map (λ f =>
      let name := c_name.val++"_" ++ f.fst.val
      let args := unpackPyArguments f.snd.fst
      let body := f.snd.snd.fst.val
      let ret := f.snd.snd.snd.val
      .proc (pythonFuncToCore name args body ret default translation_ctx).fst)
    let classdecl:=  {name := c_name.val}
    (funcdecls,
      {translation_ctx with class_infos := translation_ctx.class_infos ++ [classdecl], currentclassname:= ""})
  | _ => panic! s!"Expected function def: {repr s}"

mutual
partial def PythonDefToCore (pydef: Python.stmt SourceRange) (translation_ctx: TranslationContext): List Core.Decl × TranslationContext :=
  match pydef with
  | .FunctionDef _ _ _ _ _ _ _ _ => PyFuncDefToCore pydef translation_ctx
  | .ClassDef _ _ _ _ _ _ _ => PyClassDefToCore pydef translation_ctx
  | _ => ([], translation_ctx)

partial def PythonDefsToCore (a : Array (Python.stmt SourceRange)) (translation_ctx: TranslationContext)  : (List Core.Decl × TranslationContext) :=
  a.foldl (fun (decls, ctx) pydef =>
    let (newdecls, newCtx) := PythonDefToCore pydef ctx
    (decls ++ newdecls, newCtx))
  ([], translation_ctx)

end

def pythonToCoreBind (pgm: Strata.Program) (translation_ctx: TranslationContext:= default): Core.Program × TranslationContext:=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_and_class_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | .ClassDef _ _ _ _ _ _ _ => true
  | _ => false)
  let (decls, translation_ctx) := PythonDefsToCore func_and_class_defs translation_ctx

  --let globals := [(.var "__name__" AnyTy (strToAny "__main__"))]
  --let mainfunction := Core.Decl.proc (pythonFuncToCore "__main__" [] non_func_blocks none default translation_ctx).fst
  ({decls := decls }, translation_ctx)

def pythonToCore (pgm: Strata.Program) (translation_ctx: TranslationContext:= default): Core.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  let insideMod := unwrapModule pyCmds[0]!
  let func_and_class_defs := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => true
  | .ClassDef _ _ _ _ _ _ _ => true
  | _ => false)
  let (decls, translation_ctx) := PythonDefsToCore func_and_class_defs translation_ctx

  let non_func_blocks := insideMod.filter (λ s => match s with
  | .FunctionDef _ _ _ _ _ _ _ _ => false
  | .ClassDef _ _ _ _ _ _ _ => false
  | _ => true)

  --let globals := [(.var "__name__" AnyTy (strToAny "__main__"))]
  let mainfunction := Core.Decl.proc (pythonFuncToCore "__main__" [] non_func_blocks none default translation_ctx).fst
  {decls := decls ++  [mainfunction]}

--------------------
--Testing
--------------------



end Strata
