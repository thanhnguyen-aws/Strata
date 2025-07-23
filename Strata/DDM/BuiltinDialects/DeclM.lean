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

import Strata.DDM.Parser
import Strata.DDM.Util.Lean

open Lean (Syntax Message)

open Strata.Parser (DeclParser InputContext Parser ParsingContext ParserState)

namespace Strata

namespace Elab

/--
Describes an elaboration relationship between a argument in the bindings and
the syntax node.
-/
structure ArgElaborator where
  -- Index of this argument to elaborator in syntax tree.
  syntaxLevel : Nat
  -- Level of argument in bindings.
  argLevel : Nat
  -- Index of argument to use for typing context (if specified, must be less than argIndex)
  contextLevel : Option (Fin argLevel) := .none
deriving Inhabited, Repr

def mkArgElab (bindings : DeclBindings) (syntaxLevel : Nat) (argLevel : Fin bindings.size) : ArgElaborator :=
  let contextLevel : Option (Fin argLevel) := bindings.argScopeLevel argLevel
  { argLevel := argLevel.val, syntaxLevel, contextLevel }

def addElaborators (bindings : DeclBindings) (p : Nat × Array ArgElaborator) (a : SyntaxDefAtom) : Nat × Array ArgElaborator :=
  match a with
  | .ident level _prec =>
    let (si, es) := p
    if h : level < bindings.size then
      let argElab := mkArgElab bindings si ⟨level, h⟩
      (si + 1, es.push argElab)
    else
      panic! "Invalid index"
  | .str _ =>
    let (si, es) := p
    (si + 1, es)
  | .indent _ as =>
    as.attach.foldl (init := p) (fun p ⟨a, _⟩ => addElaborators bindings p a)

/-- Information needed to elaborator operations or functions. -/
structure SyntaxElaborator where
  argElaborators : Array ArgElaborator
  resultScope : Option Nat
deriving Inhabited, Repr

def mkElaborators (bindings : DeclBindings) (as : Array SyntaxDefAtom) : Array ArgElaborator :=
  let init : Array ArgElaborator := Array.mkEmpty bindings.size
  let (_, es) := as.foldl (init := (0, init)) (addElaborators bindings)
  es.qsort (fun x y => x.argLevel < y.argLevel)

def mkSyntaxElab (bindings : DeclBindings) (stx : SyntaxDef) (opMd : Metadata) : SyntaxElaborator := {
    argElaborators := mkElaborators bindings stx.atoms,
    resultScope := opMd.resultLevel bindings.size,
  }

def opDeclElaborator (decl : OpDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

def fnDeclElaborator (decl : FunctionDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

abbrev SyntaxElabMap := Std.HashMap QualifiedIdent SyntaxElaborator

def addSyntaxElab (m : SyntaxElabMap) (dialect : String) (name : String) (se : SyntaxElaborator) : SyntaxElabMap :=
  m.insert { dialect, name := name } se

def addDeclSyntaxElabs (dialect : String) (m : SyntaxElabMap) (d : Decl) : SyntaxElabMap :=
  match d with
  | .op d => addSyntaxElab m dialect d.name (opDeclElaborator d)
  | .function d => addSyntaxElab m dialect d.name (fnDeclElaborator d)
  | _ => m

def addDialectSyntaxElabs (m : SyntaxElabMap) (d : Dialect) : SyntaxElabMap :=
  d.declarations.foldl (addDeclSyntaxElabs d.name) m

-- Metadata syntax

syntax "md{" withoutPosition(sepBy(term, ", ")) "}" : term

macro_rules
  | `(md{ $elems,* }) => `(Metadata.ofArray (List.toArray [ $elems,* ]))

-- ElabClass

class ElabClass (m : Type → Type) extends Monad m where
  getInputContext : m InputContext
  getEnv : m Environment
  getParserState : m ParserState
  getErrorCount : m Nat
  logErrorMessage : Syntax → Message → m Unit

export ElabClass (getInputContext getEnv getParserState getErrorCount logErrorMessage)

/-
Runs action and returns result along with Bool that is true if
action ran without producing errors.
-/
def runChecked [ElabClass m] (action : m α) : m (α × Bool) := do
  let errorCount ← getErrorCount
  let r ← action
  return (r, errorCount = (← getErrorCount))

def logError [ElabClass m] (stx : Syntax) (msg : String) : m Unit := do
  let pos := stx.getHeadInfo.getPos?.getD 0
  let inputCtx ← getInputContext
  logErrorMessage stx <| Lean.mkStringMessage inputCtx pos msg

def logErrorMF [ElabClass m] (stx : Syntax) (msg : StrataFormat) : m Unit := do
  let env ← Elab.getEnv
  let c := env.formatContext {}
  let s := env.formatState
  logError stx (msg c s |>.format |>.pretty)

-- DeclM

structure DeclContext where
  inputContext : InputContext
  stopPos : String.Pos

def DeclContext.empty : DeclContext where
  inputContext := default
  stopPos := 0

structure DeclState where
  env : Environment
  -- Parsers for dialects in environment.
  -- Stored separately to avoid errors when opening dialect.
  dialectParsers : Std.HashMap DialectName (Array DeclParser) := {}
  -- The parser context represents the state of the parser.
  parserState : ParserState := {}
  -- Map for elaborating operations and functions
  syntaxElabMap : SyntaxElabMap
  -- String position in file.
  pos : String.Pos
  -- Errors found in elaboration.
  errors : Array (Syntax × Message) := #[]
  -- Contains the dialect being defined and old parser state (if any)
  currentDialect : Option (Syntax × DialectName × ParserState) := none

namespace DeclState

protected
def modifyEnv (f : Environment → Environment) (s : DeclState) :=
  { s with env := f s.env }

def modifyParserState (f : ParserState → ParserState) (s : DeclState) :=
  { s with parserState := f s.parserState }

def addDialect! (dialect : Dialect) (s : DeclState) : DeclState :=
  match s.parserState.parsingContext.mkDialectParsers dialect with
  | .error msg =>
    @panic _ ⟨s⟩ s!"Could not add open dialect: {eformat msg |>.pretty}"
  | .ok parsers =>
    { s with
      env := s.env.addDialect dialect,
      dialectParsers := s.dialectParsers.insert dialect.name parsers
      syntaxElabMap := addDialectSyntaxElabs s.syntaxElabMap dialect
      }

def addDialects! (dialects : Array Dialect) (s : DeclState) : DeclState :=
  dialects.foldl (·.addDialect!) s

end DeclState

@[reducible]
def DeclM := ReaderT DeclContext (StateM DeclState)

namespace DeclM

instance : ElabClass DeclM where
  getInputContext := return (←read).inputContext
  getEnv := return (←get).env
  getParserState := return (←get).parserState
  getErrorCount := return (←get).errors.size
  logErrorMessage stx msg :=
    modify fun s => { s with errors := s.errors.push (stx, msg) }

def runInitializer (action : DeclM Unit) : DeclState :=
  (action DeclContext.empty { pos := 0, env := .empty, syntaxElabMap := {}}).snd

end DeclM

def declareEmptyDialect (name : DialectName) : DeclM Dialect := do
  let d := { name }
  modify fun s => { s with
    env := s.env.addDialect d
    dialectParsers := s.dialectParsers.insert name #[]
  }
  pure d

def updateEnv (f : Environment → Environment) : DeclM Unit := do
  modify (·.modifyEnv f)

def getDialect (name : String) : DeclM Dialect := do
  let some d := (← getEnv).dialects[name]?
    | panic! "Unknown dialect {name}"
  return d

def addDeclToEnv (name : DialectName) (decl : Decl) : DeclM Unit := do
  updateEnv (·.addDecl! name decl)

def updateParserState (f : ParserState → ParserState) : DeclM Unit := do
  modify (·.modifyParserState f)

/--
Opens the dialect (not must not already be open)
-/
def openDialect (dialect : DialectName) : DeclM Unit := do
  if dialect ∈ (←get).env.openDialects then
    panic! s!"Dialect {dialect} already open"
    return
  let d ← getDialect dialect
  modify fun s =>
    { s with
      env := s.env.openDialect dialect,
      parserState :=
        if dialect ∈ s.parserState.openDialects then
          s.parserState
        else
          let parsers := s.dialectParsers.getD dialect #[]
          s.parserState.openDialect dialect d.syncats parsers
    }

/--
Opens the dialect in the parser so it is visible to parser, but not
part of environment.  This is used for dialect definitions.
-/
def openParserDialect (dialect : DialectName) : DeclM Unit := do
  let d ← getDialect dialect
  assert! dialect ∉ (←getParserState).openDialects
  modify fun s =>
    { s with
      parserState :=
        let parsers := s.dialectParsers.getD dialect #[]
        s.parserState.openDialect dialect d.syncats parsers
    }

def declareAtomicCat (catIdent : QualifiedIdent) (p : Parser) : DeclM Unit := do
  addDeclToEnv catIdent.dialect (.syncat { name := catIdent.name })
  assert! catIdent.dialect ∈ (←getEnv).openDialects
  updateParserState (·.addFixedParser catIdent p)

def declareCat (cat : QualifiedIdent) (argNames : Array String := #[]): DeclM Unit := do
  let d ← getDialect cat.dialect
  if cat.name ∈ d.cache then
    panic! s!"declareCat Category {eformat cat} already declared"
  let decl := { name := cat.name, argNames }
  addDeclToEnv cat.dialect (.syncat decl)
  if cat ∈ (← getParserState).categoryMap then
    panic! s!"declareCat 2 Category {eformat cat} already declared"
  if d.name ∈ (←getEnv).openDialects then
    updateParserState (·.addSynCat cat.dialect decl)

def addDecl (dialect : DialectName) (decl : Decl) (dp : DeclParser) (se : SyntaxElaborator) : DeclM Unit := do
  modify fun s => { s with
    env := s.env.addDecl! dialect decl
    dialectParsers := s.dialectParsers.alter dialect fun c => (c.getD #[]).push dp
    parserState := s.parserState.extendDeclParser dialect dp
    syntaxElabMap := addSyntaxElab s.syntaxElabMap dialect decl.name se
  }

def declareOp (dialect : DialectName) (decl : OpDecl) : DeclM Unit := do
  match (←getParserState).parsingContext.opDeclParser dialect decl with
  | .error msg =>
    panic! (eformat msg).pretty
  | .ok dp =>
    addDecl dialect (.op decl) dp (opDeclElaborator decl)

def declareMetadata (dialect : String) (decl : MetadataDecl) := do
  addDeclToEnv dialect (.metadata decl)

end Elab
