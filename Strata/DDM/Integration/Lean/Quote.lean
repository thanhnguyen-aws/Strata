/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Lean.Elab.Term

namespace Strata

open Lean

private def quoteOption (a : Option Term) : Term :=
  match a with
  | none => Syntax.mkCApp ``Option.none #[]
  | some a => Syntax.mkCApp ``Option.some #[a]

private def quoteArray (a : Array Term) : Term :=
  if a.size <= 8 then
    let terms := a
    Syntax.mkCApp (Name.mkStr2 "Array" ("mkArray" ++ toString a.size)) terms
  else
    let e := Syntax.mkCApp ``Array.mkEmpty #[quote a.size]
    a.foldl (init := e) fun t a => Syntax.mkCApp ``Array.push #[t, a]

section
open Lean.Elab

/--
Lift a DDM AST constructor to the syntax level with the correct number of arguments.

For example, `astQuote! ArgF.ident (quote e)` returns syntax for (ArgF.ident ann e).
-/
syntax:max (name := astQuoteElab) "astQuote!" ident term:max* : term

@[term_elab astQuoteElab]
def astQuoteElabImpl : Term.TermElab := fun stx _expectedType => do
  let a := stx.getArgs
  assert! a.size = 3
  let ident := a[1]!
  assert! ident.isIdent
  let ctor ← realizeGlobalConstNoOverloadWithInfo ident
  let cv ← getConstVal ctor
  let argc := cv.type.getForallBinderNames.length
  let termList := a[2]!
  assert! termList.isOfKind nullKind
  let terms := termList.getArgs
  if argc ≠ terms.size then
    throwErrorAt ident "Expected {argc} arguments; found {terms.size} arguments."
  let eltType := mkApp (mkConst ``TSyntax) (toExpr [`term])
  let a ← terms.mapM_off (init := #[]) fun ts => Term.elabTerm ts (some eltType)
  return mkApp2 (mkConst ``Lean.Syntax.mkCApp) (toExpr ctor) (arrayToExpr eltType a)

end

namespace SyntaxCat

protected def quote (cat : SyntaxCat) : Term :=
  let r := quoteArray <| cat.args.map fun x => x.quote
  astQuote! SyntaxCat.mk (quote cat.name) r
termination_by sizeOf cat
decreasing_by
  simp [sizeOf_spec cat]
  decreasing_tactic

instance : Quote SyntaxCat where
  quote := SyntaxCat.quote

end SyntaxCat

namespace TypeExpr

protected def quote : TypeExpr → Term
| .ident nm a =>
  astQuote! ident (quote nm) (quoteArray (a.map (·.quote)))
| .bvar idx =>
  astQuote! bvar (quote idx)
| .fvar idx a =>
  astQuote! fvar (quote idx) (quoteArray (a.map (·.quote)))
| .arrow a r =>
  astQuote! arrow a.quote r.quote
termination_by e => e

instance : Quote TypeExpr where
  quote := TypeExpr.quote

end TypeExpr

mutual

protected def Expr.quote : Expr → Term
| .bvar s => astQuote! Expr.bvar (quote s)
| .fvar idx => astQuote! Expr.fvar (quote idx)
| .fn ident => astQuote! Expr.fn (quote ident)
| .app f a => astQuote! Expr.app f.quote a.quote
termination_by e => sizeOf e

protected def Arg.quote : Arg → Term
| .op o => Syntax.mkCApp ``Arg.op #[o.quote]
| .expr e     => Syntax.mkCApp ``Arg.expr #[e.quote]
| .type e     => Syntax.mkCApp ``Arg.type #[quote e]
| .cat e      => Syntax.mkCApp ``Arg.cat #[quote e]
| .ident e    => Syntax.mkCApp ``Arg.ident #[quote e]
| .num e    => Syntax.mkCApp ``Arg.num #[quote e]
| .decimal e => Syntax.mkCApp ``Arg.decimal #[quote e]
| .strlit e   => Syntax.mkCApp ``Arg.strlit #[quote e]
| .option a => Syntax.mkCApp ``Arg.option #[quoteOption (a.attach.map (fun ⟨e, _⟩ => e.quote))]
| .seq a => Syntax.mkCApp ``Arg.seq #[quoteArray (a.map (·.quote))]
| .commaSepList a => Syntax.mkCApp ``Arg.commaSepList #[quoteArray (a.map (·.quote))]
termination_by a => sizeOf a

def Operation.quote (op : Operation) : Term :=
  let r := quoteArray (op.args.map (·.quote))
  Syntax.mkCApp ``Operation.mk #[quote op.name, r]
termination_by sizeOf op
decreasing_by
  simp [Operation.sizeOf_spec]
  decreasing_tactic

end

instance : Quote Arg where
  quote := Arg.quote

instance : Quote Expr where
  quote := Expr.quote

instance: Quote Operation where
  quote := Operation.quote

namespace PreType

protected def quote : PreType → Term
| .ident nm a =>
  Syntax.mkCApp ``ident #[quote nm, quoteArray (a.map (·.quote))]
| .bvar idx => Syntax.mkCApp ``bvar #[quote idx]
| .fvar idx a =>
  Syntax.mkCApp ``fvar #[quote idx, quoteArray (a.map (·.quote))]
| .arrow a r => Syntax.mkCApp ``arrow #[a.quote, r.quote]
| .funMacro i r =>
  Syntax.mkCApp ``funMacro #[quote i, r.quote]

instance : Quote PreType where
  quote := PreType.quote

end PreType

namespace MetadataArg

protected def quote : MetadataArg → Term
  | .bool b    => Syntax.mkCApp ``bool #[quote b]
  | .num n     => Syntax.mkCApp ``num #[quote n]
  | .catbvar n => Syntax.mkCApp ``catbvar #[quote n]
  | .option ma => Syntax.mkCApp ``option #[quoteOption (ma.attach.map fun ⟨a, _⟩ => a.quote)]

instance : Quote MetadataArg where
  quote := MetadataArg.quote

end MetadataArg

instance : Quote MetadataAttr where
  quote a := Syntax.mkCApp ``MetadataAttr.mk #[quote a.ident, quote a.args]

instance : Quote Metadata where
  quote m := Syntax.mkCApp ``Metadata.ofArray #[quote m.toArray]

namespace ArgDeclKind

instance : Quote ArgDeclKind where
  quote
  | .type tp => Syntax.mkCApp ``type #[quote tp]
  | .cat c => Syntax.mkCApp ``cat #[quote c]

end ArgDeclKind

instance ArgDecl.instQuote : Quote ArgDecl where
  quote b := Syntax.mkCApp ``mk #[quote b.ident, quote b.kind, quote b.metadata]

namespace SyntaxDefAtom

protected def quote : SyntaxDefAtom → Term
| .ident v p => Syntax.mkCApp ``ident #[quote v, quote p]
| .str l     => Syntax.mkCApp ``str #[quote l]
| .indent n a => Syntax.mkCApp ``indent #[quote n, quoteArray (a.map (·.quote))]

instance : Quote SyntaxDefAtom where
  quote := SyntaxDefAtom.quote

end SyntaxDefAtom

namespace SyntaxDef

instance : Quote SyntaxDef where
  quote s := Syntax.mkCApp ``SyntaxDef.mk #[quote s.atoms, quote s.prec]

end SyntaxDef

instance : Quote ArgDecls where
  quote a :=  Syntax.mkCApp ``ArgDecls.ofArray #[quote a.toArray]

instance : Quote SynCatDecl where
  quote d :=  Syntax.mkCApp ``SynCatDecl.mk #[quote d.name, quote d.argNames]

instance : Quote OpDecl where
  quote d := Syntax.mkCApp ``OpDecl.mk1 #[
    quote d.name,
    quote d.argDecls,
    quote d.category,
    quote d.syntaxDef,
    quote d.metadata
  ]

instance : Quote TypeDecl where
  quote d := Syntax.mkCApp ``TypeDecl.mk #[quote d.name, quote d.argNames]

instance : Quote FunctionDecl where
  quote d := Syntax.mkCApp ``FunctionDecl.mk #[
    quote d.name,
    quote d.argDecls,
    quote d.result,
    quote d.syntaxDef,
    quote d.metadata
  ]

namespace MetadataArgType

protected def quote : MetadataArgType → Term
| .bool     => mkCIdent ``bool
| .num      => mkCIdent ``num
| .ident    => mkCIdent ``ident
| .opt tp => Syntax.mkCApp ``opt #[tp.quote]

instance : Quote MetadataArgType where
  quote := MetadataArgType.quote

end MetadataArgType

instance : Quote MetadataArgDecl where
  quote d := Syntax.mkCApp ``MetadataArgDecl.mk #[quote d.ident, quote d.type]

instance : Quote MetadataDecl where
  quote d := Syntax.mkCApp ``MetadataDecl.mk #[quote d.name, quote d.args]

instance : Quote Decl where
  quote
  | .syncat d => Syntax.mkCApp ``Decl.syncat #[quote d]
  | .op d => Syntax.mkCApp ``Decl.op #[quote d]
  | .type d => Syntax.mkCApp ``Decl.type #[quote d]
  | .function d =>  Syntax.mkCApp ``Decl.function #[quote d]
  | .metadata d => Syntax.mkCApp ``Decl.metadata #[quote d]

instance : Quote Dialect where
  quote d : Term :=
    Syntax.mkCApp ``Dialect.ofArray #[
        quote d.name,
        quote d.imports,
        quote d.declarations
      ]

namespace DialectMap

instance : Quote DialectMap where
  quote d := Syntax.mkCApp ``DialectMap.ofList! #[quote d.toList]

end DialectMap

instance : Quote Program where
  quote p : Term :=
    Syntax.mkCApp ``Program.create #[
      quote p.dialects,
      quote p.dialect,
      quote p.commands
    ]

end Strata
