import C0VC.Ast
open C0VC.Ast
namespace C0VC.Dce
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

partial def dceMStm (mstm : Ast.MarkedStm) : Ast.MarkedStm × Bool :=
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
  | .forLit init test update body =>
      let (init', initReturns) := dceMStm init
      if initReturns then
        (init', true)
      else
        let (body', _) := dceMStm body
        let (update', _) := dceMStm update
        ({ mstm with node := .forLit init' test update' body' }, false)
  | _ => (mstm, false)

def dceBody (body : List Ast.MarkedStm) : List Ast.MarkedStm :=
  match body with
  | [] => []
  | stm :: rest =>
      let (stm', stmReturns) := dceMStm stm
      if stmReturns then
        [stm']
      else
        stm' :: dceBody rest

def dceGDecl (gdecl : Ast.GDecl) : Ast.GDecl :=
  match gdecl with
  | .fdecl .. => gdecl
  | .fdefn retType fname params body annotations =>
      .fdefn retType fname params (dceBody body) annotations
  | .typedef .. => gdecl

def removeAfterReturns (program : Ast.Program) : Ast.Program :=
  List.map dceGDecl program

def run (program : Ast.Program) : Ast.Program :=
  removeAfterReturns program

end C0VC.Dce
