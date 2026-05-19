import C0C.Ast
import Std.Data.HashMap

open C0C.Ast
open Std.HashMap

namespace C0C.Typechecker
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

def collectFnNames (program : Ast.Program) : List String :=
  program.filterMap
    (fun gdecl =>
      match gdecl with
      | .fdecl (fname := fname) .. =>
        some fname
      | .fdefn (fname := fname) .. =>
        some fname
      | _ => none
    )

def tcMainFn (program : Ast.Program) : Except String Unit := do
  let fnNames := collectFnNames program
  let mainFns := fnNames.filter (λ fname => fname == "main")
  let _ ← match List.length mainFns with
    | 0 => .error "Could not find a main function"
    | 1 => .ok ()
    | _ => .error "Found more than one main function"
  let fenv := collectFEnv program
  match fenv.get? "main" with
  | some info =>
    if info.params.isEmpty then
      .ok ()
    else
      .error "main function must not take parameters"

  -- TODO: this case should never happen, consider panicking
  | none => .error "Could not find a main function"

structure VarInfo where
  name : String
  varType : Tau
  initialized : Bool

abbrev VEnv := Std.HashMap String VarInfo

def insertVEnv (venv : VEnv) (name : String) (varType : Tau) (initialized : Bool) : VEnv :=
  venv.insert name { name := name, varType := varType, initialized := initialized }

def markVEnvInitialized (venv : VEnv) (name : String) : Except String VEnv :=
  match venv.get? name with
  | some info => .ok (venv.insert name { info with initialized := true })
  | none => .error s!"variable {name} used before decl"

def tcVarDeclared (venv : VEnv) (name : String) : Except String VarInfo :=
  match venv.get? name with
  | some info => .ok info
  | none => .error s!"variable {name} used before decl"

def tcVarReadable (venv : VEnv) (name : String) : Except String VarInfo :=
  match venv.get? name with
  | some info =>
    if info.initialized then
      .ok info
    else
      .error s!"variable {name} used before initialized"
  | none => .error s!"Used {name} before defined"

def mergeVEnvAfterBranches (before thenEnv elseEnv : VEnv) : VEnv :=
  before.toList.foldl
    (fun env (name, info) =>
      match thenEnv.get? name, elseEnv.get? name with
      | some thenInfo, some elseInfo =>
          env.insert name { info with initialized := info.initialized || (thenInfo.initialized && elseInfo.initialized) }
      | _, _ => env)
    before

def initializeAllVEnv (venv : VEnv) : VEnv :=
  venv.toList.foldl
    (fun env (name, info) => env.insert name { info with initialized := true })
    venv

def minInt32 : Int := -2147483648

def maxInt32 : Int := -1 * minInt32

def intLitInRange (n : Int) : Bool :=
  minInt32 <= n && n <= maxInt32

def tcIntLitRange (n : Int) : Except String Unit :=
  if intLitInRange n then
    .ok ()
  else
    .error s!"integer literal {n} is outside int range"

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
    let info ← tcVarReadable venv name
    .ok info.varType
  | .intLit n =>
    let _ ← tcIntLitRange n
    .ok .int
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
  | .ternary test thenVal elseVal =>
    let testType ← tcExprType test venv
    if not (tauEq testType .bool) then
      .error "ternary condition must have type Tau.bool"
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

def tcExprHasType (mexpr : Ast.MarkedExpr) (venv : VEnv) (expected : Tau) (ctx : String) :
    Except String Unit := do
  let actual ← tcExprType mexpr venv
  if tauEq actual expected then
    .ok ()
  else
    .error s!"{ctx} must have type {Ast.Print.ppTau expected}"

def tcAssignVar (venv : VEnv) (varName : String) (val : Ast.MarkedExpr) : Except String VEnv := do
  let varInfo ← tcVarDeclared venv varName
  let actualType ← tcExprType val venv
  if tauEq varInfo.varType actualType then
    markVEnvInitialized venv varName
  else
    .error s!"assigning to {varName} an expression of different type"

partial def tcMExpr (mexpr : Ast.MarkedExpr) (venv : VEnv) : Except String Unit := do
  match mexpr.node with
  | .var name =>
    let _ ← tcVarReadable venv name
    .ok ()
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

  | .intLit n =>
    tcIntLitRange n
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
    tcAssignVar venv varName val

  | .ifLit test thenBranch elseBranch =>
    let _ ← tcExprHasType test venv .bool "if condition"
    let thenEnv ← tcMStm thenBranch venv
    let elseEnv ← tcMStm elseBranch venv
    .ok (mergeVEnvAfterBranches venv thenEnv elseEnv)

  | .whileLit test body =>
    let _ ← tcExprHasType test venv .bool "while condition"
    let _ ← tcMStm body venv
    .ok venv

  | .declare varName varType value =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"
    let venv' := insertVEnv venv varName varType false
    let venv'' ← tcMStm value venv'
    .ok (venv''.erase varName)

  | .defn varName varType =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"

    .ok (insertVEnv venv varName varType false)

  | .ret valOpt =>
    match valOpt with
    | some val =>
      let _ ← tcMExpr val venv
      .ok (initializeAllVEnv venv)
    | none => .ok (initializeAllVEnv venv)

  | .seq first rest =>
    let venv' ← tcMStm first venv
    tcMStm rest venv'

  | .asop varName _ value =>
    let _ ← tcVarReadable venv varName
    let _ ← tcMExpr value venv
    markVEnvInitialized venv varName

  | .forLit init test update body =>
    let venv' ← tcMStm init venv
    let _ ← tcExprHasType test venv' .bool "for condition"
    let venv'' ← tcMStm body venv'
    tcMStm update venv''

  | .expr e =>
    let _ ← tcMExpr e venv
    .ok venv

  | .assert test =>
    let _ ← tcExprHasType test venv .bool "assert condition"
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
    let _ ← tcVarReadable venv varName
    markVEnvInitialized venv varName

def tcGDecl (gdecl : Ast.GDecl) : Except String Unit := do
  match gdecl with
  | .fdefn (params := params) (body := body) .. =>
    let venv ← params.foldlM
      (fun env (varType, name) =>
        if env.contains name then
          .error s!"variable {name} declared more than once"
        else
          .ok (insertVEnv env name varType true))
      {}
    let _ ← List.foldlM (λ venv mstm => tcMStm mstm venv) venv body
    .ok ()
  | .fdecl .. => .ok ()
  | .typedef .. => .ok ()

partial def tcReturnMStm (expected : Tau) (mstm : Ast.MarkedStm) (venv : VEnv) :
    Except String (Bool × VEnv) := do
  match mstm.node with
  | .assign varName val =>
    let venv' ← tcAssignVar venv varName val
    .ok (false, venv')
  | .ret valOpt =>
    match valOpt with
    | some val =>
      let actual ← tcExprType val venv
      if tauEq actual expected then
        .ok (true, initializeAllVEnv venv)
      else
        .error "return type does not match function return type"
    | none =>
      if tauEq expected .void then
        .ok (true, initializeAllVEnv venv)
      else
        .error "return type does not match function return type"
  | .declare varName varType value =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"
    let venv' := insertVEnv venv varName varType false
    let (hasReturn, venv'') ← tcReturnMStm expected value venv'
    .ok (hasReturn, venv''.erase varName)
  | .defn varName varType =>
    .ok (false, insertVEnv venv varName varType false)
  | .seq first rest =>
    let (firstReturn, venv') ← tcReturnMStm expected first venv
    let (restReturn, venv'') ← tcReturnMStm expected rest venv'
    .ok (firstReturn || restReturn, venv'')
  | .ifLit _ thenBranch elseBranch =>
    let (thenReturn, venv') ← tcReturnMStm expected thenBranch venv
    let (elseReturn, venv'') ← tcReturnMStm expected elseBranch venv
    .ok (thenReturn && elseReturn, mergeVEnvAfterBranches venv venv' venv'')
  | .whileLit _ body =>
    tcReturnMStm expected body venv
  | .forLit init _ update body =>
    let (_, venv') ← tcReturnMStm expected init venv
    let (bodyReturn, venv'') ← tcReturnMStm expected body venv'
    let (updateReturn, venv''') ← tcReturnMStm expected update venv''
    .ok (bodyReturn || updateReturn, venv''')
  | .asop varName _ value =>
    let _ ← tcVarReadable venv varName
    let _ ← tcExprType value venv
    let venv' ← markVEnvInitialized venv varName
    .ok (false, venv')
  | .incr varName
  | .decr varName =>
    let _ ← tcVarReadable venv varName
    let venv' ← markVEnvInitialized venv varName
    .ok (false, venv')
  | _ => .ok (false, venv)

def tcControlFlow (gdecl : Ast.GDecl) (_venv : VEnv) : Except String Unit := do
  match gdecl with
  | .fdefn (retType := retType) (params := params) (body := body) .. =>
    let venv ← params.foldlM
      (fun venv (varType, name) =>
        if venv.contains name then
          .error s!"variable {name} declared more than once"
        else
          .ok (insertVEnv venv name varType true))
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
  let _ ← tcMainFn program

  List.forM program (λ gdecl => do
    let _ ← tcGDecl gdecl
    let _ ← tcControlFlow gdecl {}
    .ok ())

end C0C.Typechecker
