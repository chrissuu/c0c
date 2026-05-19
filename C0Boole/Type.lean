import C0Boole.Ast
import Std.Data.HashMap

open C0Boole.Ast
open Std.HashMap

namespace C0Boole.Typechecker
structure FnInfo where
  retType : Tau
  fname : String
  params : List Param

abbrev FEnv := Std.HashMap String FnInfo

def collectFEnv (program : Ast.Program) : FEnv :=
  program.foldl
    (fun env gdecl =>
      match gdecl with
      | .fdecl retType fname params _ =>
          env.insert fname { retType := retType, fname := fname, params := params }
      | .fdefn retType fname params _ _ =>
          env.insert fname { retType := retType, fname := fname, params := params }
      | _ => env)
    {}

structure VarInfo where
  name : String
  varType : Tau

abbrev VEnv := Std.HashMap String VarInfo

def insertVEnv (venv : VEnv) (name : String) (varType : Tau) : VEnv :=
  venv.insert name { name := name, varType := varType }

def tauEq : Tau → Tau → Bool
  | .int, .int => true
  | .char, .char => true
  | .string, .string => true
  | .bool, .bool => true
  | .void, .void => true
  | .typeName lhs, .typeName rhs => lhs == rhs
  | _, _ => false

def binopType : BinOp → Tau
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => .int
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq
  | .land
  | .lor => .bool

partial def tcExprType (mexpr : Ast.MarkedExpr) (venv : VEnv) : Except String Tau := do
  match mexpr.node with
  | .var name =>
    match venv.get? name with
    | some info => .ok info.varType
    | none => .error s!"Used {name} before defined"
  | .intLit _ => .ok .int
  | .trueLit
  | .falseLit => .ok .bool
  | .charLit _ => .ok .char
  | .stringLit _ => .ok .string
  | .binop op lhs rhs =>
    let _ ← tcExprType lhs venv
    let _ ← tcExprType rhs venv
    .ok (binopType op)
  | .unop op operand =>
    let _ ← tcExprType operand venv
    match op with
    | .bang => .ok .bool
    | .bitNot
    | .negative => .ok .int
  | .ternary _ thenVal elseVal =>
    let thenType ← tcExprType thenVal venv
    let elseType ← tcExprType elseVal venv
    if tauEq thenType elseType then
      .ok thenType
    else
      .error "ternary branches have different types"
  | .length arrayLike =>
    let _ ← tcExprType arrayLike venv
    .ok .int
  | .call fname _ =>
    .error s!"Cannot infer return type for function call {fname}"
  | .result
  | .hastag =>
    .error "Cannot infer type for annotation-only expression"

partial def tcMExpr (mexpr : Ast.MarkedExpr) (venv : VEnv) : Except String Unit := do
  match mexpr.node with
  | .var name =>
    if venv.contains name then
      .ok ()
    else .error s!"Used {name} before defined"
  | .binop _ lhs rhs =>
    let _ ← tcMExpr lhs venv
    let _ ← tcMExpr rhs venv
    .ok ()
  | .unop _ operand =>
    let _ ← tcMExpr operand venv
    .ok ()

  |.ternary test thenVal elseVal =>
    let _ ← tcMExpr test venv
    let _ ← tcMExpr thenVal venv
    let _ ← tcMExpr elseVal venv
    .ok ()

  | .call _ args =>
    args.forM (fun arg => tcMExpr arg venv)

  -- TODO
  | .length arrayLike =>
    tcMExpr arrayLike venv

  | .intLit _
  | .trueLit
  | .falseLit
  | .charLit _
  | .stringLit _
  | .result
  | .hastag
    => .ok ()

partial def tcMStm (mstm : Ast.MarkedStm) (venv : VEnv) : Except String VEnv := do
  match mstm.node with
  | .assign varName val =>
    if not (venv.contains varName) then
      .error s!"variable {varName} used before decl"

    let _ ← tcMExpr val venv
    .ok venv

  | .ifLit test thenBranch elseBranch =>
    let _ ← tcMExpr test venv
    let venv' ← tcMStm thenBranch venv
    let venv'' ← tcMStm elseBranch venv'
    .ok venv''

  | .whileLit test body =>
    let _ ← tcMExpr test venv
    tcMStm body venv

  | .declare varName varType value =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"

    match value.node with
    -- we need to be able to handle shapes like:
    -- .declare x tau (.assign x rhs), while correctly handling (rejecting)
    -- programs with stms such as `int x = x;`, where x is declared for the first time.

    -- TODO: maybe there's a cleaner way to do this.
    | .assign assignedName val =>
      if assignedName == varName then
        let _ ← tcMExpr val venv
        .ok (insertVEnv venv varName varType)
      else
        .error s!"declaration initializer assigned {assignedName}, expected {varName}"
    | .nop =>
      .ok (insertVEnv venv varName varType)
    | _ =>
      let _ ← tcMStm value venv
      .ok (insertVEnv venv varName varType)

  | .defn varName varType =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"

    .ok (insertVEnv venv varName varType)

  | .ret valOpt =>
    match valOpt with
    | some val =>
      let _ ← tcMExpr val venv
      .ok venv
    | none => .ok venv

  | .seq first rest =>
    let venv' ← tcMStm first venv
    tcMStm rest venv'

  | .asop varName _ value =>
    if venv.contains varName then
      let _ ← tcMExpr value venv
      .ok venv
    else
      .error s!"Used {varName} before defined"

  | .forLit init test update body =>
    let venv' ← tcMStm init venv
    let _ ← tcMExpr test venv'
    let venv'' ← tcMStm body venv'
    tcMStm update venv''

  | .expr e =>
    let _ ← tcMExpr e venv
    .ok venv

  | .assert test =>
    let _ ← tcMExpr test venv
    .ok venv

  | .error e =>
    let _ ← tcMExpr e venv
    .ok venv

  | .nop =>
    .ok venv

  -- TODO
  | .annotation a =>
    match a.node with
    | .requires e
    | .ensures e
    | .asserts e
    | .loopInvariant e =>
      let _ ← tcMExpr e venv
      .ok venv

  | .incr varName
  | .decr varName =>
    if venv.contains varName then
      .ok venv
    else
      .error s!"Used {varName} before defined"

def tcGDecl (gdecl : Ast.GDecl) : Except String Unit := do
  match gdecl with
  | .fdefn (params := params) (body := body) .. =>
    let venv ← params.foldlM
      (fun env (varType, name) =>
        if env.contains name then
          .error s!"variable {name} declared more than once"
        else
          .ok (insertVEnv env name varType))
      {}
    let _ ← List.foldlM (λ venv mstm => tcMStm mstm venv) venv body
    .ok ()
  | .fdecl .. => .ok ()
  | .typedef .. => .ok ()

partial def tcReturnMStm (expected : Tau) (mstm : Ast.MarkedStm) (venv : VEnv) :
    Except String (Bool × VEnv) := do
  match mstm.node with
  | .ret valOpt =>
    match valOpt with
    | some val =>
      let actual ← tcExprType val venv
      if tauEq actual expected then
        .ok (true, venv)
      else
        .error "return type does not match function return type"
    | none =>
      if tauEq expected .void then
        .ok (true, venv)
      else
        .error "return type does not match function return type"
  | .declare varName varType value =>
    let venv' := insertVEnv venv varName varType
    let (hasReturn, venv'') ← tcReturnMStm expected value venv'
    .ok (hasReturn, venv'')
  | .defn varName varType =>
    .ok (false, insertVEnv venv varName varType)
  | .seq first rest =>
    let (firstReturn, venv') ← tcReturnMStm expected first venv
    let (restReturn, venv'') ← tcReturnMStm expected rest venv'
    .ok (firstReturn || restReturn, venv'')
  | .ifLit _ thenBranch elseBranch =>
    let (thenReturn, venv') ← tcReturnMStm expected thenBranch venv
    let (elseReturn, venv'') ← tcReturnMStm expected elseBranch venv'
    .ok (thenReturn || elseReturn, venv'')
  | .whileLit _ body =>
    tcReturnMStm expected body venv
  | .forLit init _ update body =>
    let (_, venv') ← tcReturnMStm expected init venv
    let (bodyReturn, venv'') ← tcReturnMStm expected body venv'
    let (updateReturn, venv''') ← tcReturnMStm expected update venv''
    .ok (bodyReturn || updateReturn, venv''')
  | _ => .ok (false, venv)

def tcControlFlow (gdecl : Ast.GDecl) (_venv : VEnv) : Except String Unit := do
  match gdecl with
  | .fdefn (retType := retType) (params := params) (body := body) .. =>
    let venv ← params.foldlM
      (fun venv (varType, name) =>
        if venv.contains name then
          .error s!"variable {name} declared more than once"
        else
          .ok (insertVEnv venv name varType))
      {}
    let (containsReturn, _) ← body.foldlM
      (fun (found, venv) mstm => do
        let (found', venv') ← tcReturnMStm retType mstm venv
        .ok (found || found', venv'))
      (false, venv)
    if containsReturn then
      .ok ()
    else
      .error "Could not find a return statement in function definition"

  | _ => .ok ()

def tc (program : Ast.Program) : Except String Unit := do
  List.forM program (λ gdecl => do
    let _ ← tcGDecl gdecl
    let _ ← tcControlFlow gdecl {}
    .ok ())

end C0Boole.Typechecker
