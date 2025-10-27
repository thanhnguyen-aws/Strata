/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.BuiltinDialects.Init

namespace Strata

open Elab

def headerDialect : Dialect := BuiltinM.create! "StrataHeader" #[initDialect] do
  let Ident : ArgDeclKind := .cat <| .atom q`Init.Ident
  let Command := q`Init.Command

  declareOp {
     name := "dialectCommand",
     argDecls := .ofArray #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "dialect", .ident 0 0, .str ";"],
  }
  declareOp {
     name := "programCommand",
     argDecls := .ofArray #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "program", .ident 0 0, .str ";"],
  }
