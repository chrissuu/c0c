/-
Elaboration

Desugars the any syntactic sugar of C0 and makes some conveniences as to
allow for better proof automation by Boole and relevant backends.

Currently, the following are elaborated:
1. Assignment ops
2. Unary ops (!, ~, -)
3. For loops
4. Typedefs
5. &&, || operators

Depending on whether we want to allow a "do-faithful-translation" functionality,
we may want to have a flag that turns the elaborator on and off.

Since typechecker (mostly) works on the elaborated AST, we can still resume
typechecking on the elaborated AST, but lowering to Boole happens on the original
AST.

Author: Chris Su <chrjs@cmu.edu>
-/

import C0VC.Ast
import C0VC.Utils.SrcSpan
import Std.Data.HashMap

open C0VC.Ast
open C0VC.Utils.SrcSpan
open Std.HashMap

abbrev Env := Std.HashMap String Tau

namespace C0VC.Elab
partial def countUnopOfType (acc : Nat) (type : UnOp) (mexp : MarkedExpr) :=
  match mexp.node with
  | .unop type' mexp' => if type = type' then countUnopOfType (acc + 1) type mexp' else (acc, mexp)
  | _ => (acc, mexp)

def mkElabExpr (node : Expr) (span : Option SrcSpan) : MarkedExpr :=
  MarkedExpr.mk node span

def mkElabStm (node : Stm) (span : Option SrcSpan) : MarkedStm :=
  MarkedStm.mk node span

def mkElabAnno (node : Anno) (span : Option SrcSpan) : MarkedAnno :=
  MarkedAnno.mk node span

partial def elabMExpr (mexp : MarkedExpr) :=
  match mexp.node with
  | .binop op lhs rhs =>
    match op with
    | .land =>
      mkElabExpr
        (.ternary (elabMExpr lhs) (elabMExpr rhs) (mkElabExpr .falseLit mexp.span))
        mexp.span
    | .lor =>
      mkElabExpr
        (.ternary (elabMExpr lhs) (mkElabExpr .trueLit mexp.span) (elabMExpr rhs))
        mexp.span
    | _ => mkElabExpr (.binop op (elabMExpr lhs) (elabMExpr rhs)) mexp.span
  | .unop op mexp' =>
    match op with
    | .bang =>
      let (numBangs, reducedMexp) := countUnopOfType 0 .bang mexp'
      if numBangs % 2 = 0 then mkElabExpr (elabMExpr reducedMexp).node mexp.span
      else mkElabExpr (.unop .bang (elabMExpr reducedMexp)) mexp.span
    | .bitNot =>
      let (numBitNot, reducedMexp) := countUnopOfType 0 .bitNot mexp'
      if numBitNot % 2 = 0 then mkElabExpr (elabMExpr reducedMexp).node mexp.span
      else mkElabExpr (.unop .bitNot (elabMExpr reducedMexp)) mexp.span

      -- parity collapsing for this is probably not safe to do, so for now ignore parity collapsing
    | .negative =>
      match mexp'.node with
      | .intLit n => mkElabExpr (.intLit (-n)) mexp.span
      | _ => mkElabExpr (.binop .sub (mkElabExpr (.intLit 0) mexp.span) (elabMExpr mexp')) mexp.span

  | .ternary test thenBranch elseBranch =>
    mkElabExpr (.ternary (elabMExpr test) (elabMExpr thenBranch) (elabMExpr elseBranch)) mexp.span
  | .call fname args =>
    mkElabExpr (.call fname (List.map elabMExpr args)) mexp.span
  | _ => mexp

def assignOpToBinOp : AssignOp → Option BinOp
  | .assign => none
  | .plusEq => some .plus
  | .subEq => some .sub
  | .mulEq => some .mul
  | .divEq => some .div
  | .modEq => some .mod
  | .bitAndEq => some .bitAnd
  | .xorEq => some .xor
  | .bitOrEq => some .bitOr
  | .shlEq => some .shl
  | .shrEq => some .shr

partial def resolveTypeName (env : Env) (seen : Std.HashSet String) : Tau → Except String Tau
  | .typeName name =>
      if seen.contains name then
        .error s!"cyclic typedef involving `{name}`"
      else
        match env.get? name with
        | some tau => resolveTypeName env (seen.insert name) tau
        | none => .error s!"unknown typedef `{name}`"
  | tau => .ok tau

def elabTypeName (env : Env) (tau : Tau) : Except String Tau :=
  resolveTypeName env {} tau

partial def elabMStm (env : Env) (mstm : MarkedStm) : Except String MarkedStm := do
  match mstm.node with
  | .assign varName val => .ok (mkElabStm (.assign varName (elabMExpr val)) mstm.span)
  | .ifLit test thenBranch elseBranch =>
    let thenBranch' ← elabMStm env thenBranch
    let elseBranch' ← elabMStm env elseBranch
    .ok (mkElabStm (.ifLit (elabMExpr test) thenBranch' elseBranch') mstm.span)
  | .whileLit test body =>
    let body' ← elabMStm env body
    .ok (mkElabStm (.whileLit (elabMExpr test) body') mstm.span)
  | .ret valOpt =>
    match valOpt with
    | some val => .ok (mkElabStm (.ret (some (elabMExpr val))) mstm.span)
    | none => .ok (mkElabStm (.ret none) mstm.span)
  | .seq first rest =>
    let first' ← elabMStm env first
    let rest' ← elabMStm env rest
    let span := spanCoverOpt first.span rest.span
    .ok (mkElabStm (.seq first' rest') span)
  | .declare varName tau value =>
    let t ← elabTypeName env tau
    let value' ← elabMStm env value
    .ok (mkElabStm (.declare varName t value') mstm.span)
  | .asop varName op value =>
    match assignOpToBinOp op with
    | none => .ok (mkElabStm (.assign varName (elabMExpr value)) mstm.span)
    | some binop =>
      let lhs := mkElabExpr (.var varName) mstm.span
      let rhs := mkElabExpr (.binop binop lhs (elabMExpr value)) mstm.span
      .ok (mkElabStm (.assign varName rhs) mstm.span)
  | .forLit init test update body =>
    let bodySpan := spanCoverOpt body.span update.span
    let whileSpan := spanCoverOpt test.span bodySpan
    let forSpan := spanCoverOpt init.span whileSpan
    let desugaredBody := mkElabStm (.seq body update) bodySpan
    let desugaredWhile := mkElabStm (.whileLit test desugaredBody) whileSpan
    match init.node with
    | .declare varName tau initBody =>
      let scopedFor := mkElabStm (.declare varName tau (mkElabStm (.seq initBody desugaredWhile) forSpan)) forSpan
      elabMStm env scopedFor
    | _ =>
      let desugaredFor := mkElabStm (.seq init desugaredWhile) forSpan
      elabMStm env desugaredFor
  | .expr e => .ok (mkElabStm (.expr (elabMExpr e)) mstm.span)
  | .assert test => .ok (mkElabStm (.assert (elabMExpr test)) mstm.span)
  | .error e => .ok (mkElabStm (.error (elabMExpr e)) mstm.span)
  | .incr varName =>
    let lhs := mkElabExpr (.var varName) mstm.span
    let one := mkElabExpr (.intLit 1) mstm.span
    let rhs := mkElabExpr (.binop .plus lhs one) mstm.span
    .ok (mkElabStm (.assign varName rhs) mstm.span)
  | .decr varName =>
    let lhs := mkElabExpr (.var varName) mstm.span
    let one := mkElabExpr (.intLit 1) mstm.span
    let rhs := mkElabExpr (.binop .sub lhs one) mstm.span
    .ok (mkElabStm (.assign varName rhs) mstm.span)
  | _ => .ok mstm

def elabMAnno (a : MarkedAnno) :=
  match a.node with
  | .requires precondition => mkElabAnno (.requires (elabMExpr precondition)) a.span
  | .ensures postcondition => mkElabAnno (.ensures (elabMExpr postcondition)) a.span
  | .asserts e => mkElabAnno (.asserts (elabMExpr e)) a.span
  | .loopInvariant e => mkElabAnno (.loopInvariant (elabMExpr e)) a.span

def elabParams (params : List Param) (env : Env) : Except String (List Param) :=
  List.mapM (λ (tau, paramName) => do
    let tau' ← elabTypeName env tau
    .ok (tau', paramName))
  params

def elabGDecl (gdecl : GDecl) (env : Env) : Except String (GDecl × Env) :=
  match gdecl with
  | .fdefn retType fname params body annotations =>
    do
      let retType' ← elabTypeName env retType
      let params' ← elabParams params env
      let body' ← List.mapM (elabMStm env) body
      let annotations' ← List.mapM (elabMStm env) annotations
      .ok
        ( .fdefn retType' fname params' body' annotations'
        , env
        )
  | .typedef tau alias =>
    match elabTypeName (env.insert alias tau) tau with
    | .ok t => .ok (.typedef t alias, env.insert alias t)
    | .error err => .error err
  | _ => .ok (gdecl, env)

def elabProgram (program : Ast.Program) : Except String Ast.Program :=
  match List.foldlM
    (m := Except String)
    (λ (progAcc, envAcc, lineNum) gdecl => do
      let (elabbedGdecl, envAcc') ← elabGDecl gdecl envAcc
      dbg_trace s!"Line {lineNum} is ok!"
      let isFdefn := match elabbedGdecl with | .fdefn _ _ _ _ _ => true | _ => false
      pure (if isFdefn then elabbedGdecl::progAcc else progAcc, envAcc', lineNum + 1))
    ([], {}, 0)
    program with
  | .ok (elabbedProgram, _, _) =>
    .ok (List.reverse elabbedProgram)
  | .error err => .error err

end C0VC.Elab
