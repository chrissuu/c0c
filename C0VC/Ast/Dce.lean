/-
DCE (Dead Code Elimination)

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Using initialized variables after control flow removes it from context is valid
via the typechecker but not valid by downstream passes. By implementing a
DCE pass right after typechecking and using this AST to lower to Tree,
we allow for downstream passes to not panic.

This means that if you care about program to look roughly 1-1 between C0/C1 and Boole,
the lowering should happen on the AST before elaboration and not on this DCE AST.

Author: Chris Su <chrjs@cmu.edu>
-/

import C0VC.Ast.TypedAst

namespace C0VC.Dce

partial def dceMStm (mstm : C0VC.TypedAst.TypedStm) : C0VC.TypedAst.TypedStm × Bool :=
  match mstm.node with
  | .ret _ => (mstm, true)
  | .seq first rest =>
      let (first', firstReturns) := dceMStm first
      if firstReturns then
        (first', true)
      else
        let (rest', restReturns) := dceMStm rest
        ({ mstm with node := .seq first' rest' }, restReturns)
  | .ifLit test thenBranch elseBranch =>
      let (thenBranch', thenReturns) := dceMStm thenBranch
      let (elseBranch', elseReturns) := dceMStm elseBranch
      ({ mstm with node := .ifLit test thenBranch' elseBranch' }, thenReturns && elseReturns)
  | .whileLit test body =>
      let (body', _) := dceMStm body
      ({ mstm with node := .whileLit test body' }, false)
  | .declare varName type value =>
      let (value', valueReturns) := dceMStm value
      ({ mstm with node := .declare varName type value' }, valueReturns)
  | _ => (mstm, false)

def dceBody (body : List C0VC.TypedAst.TypedStm) : List C0VC.TypedAst.TypedStm :=
  match body with
  | [] => []
  | stm :: rest =>
      let (stm', stmReturns) := dceMStm stm
      if stmReturns then
        [stm']
      else
        stm' :: dceBody rest

def dceFunctionDef (fdefn : C0VC.TypedAst.FunctionDef) : C0VC.TypedAst.FunctionDef :=
  { fdefn with body := dceBody fdefn.body }

def removeAfterReturns (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  List.map dceFunctionDef program

def run (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  removeAfterReturns program

end C0VC.Dce
