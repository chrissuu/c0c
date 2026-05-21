import C0VC.Ast.TypedAst
import C0VC.LLVM.Tree
import C0VC.Utils.Label
import C0VC.Utils.Temp

import Std.Data.HashMap

namespace C0VC.LLVM.Tree.Trans
open C0VC.LLVM.Tree
open C0VC.Utils.Label
open C0VC.Utils.Temp

abbrev TempEnv := Std.HashMap String Temp

-- TODO: consider wrapping env meta things into here / change to StateM
structure Env where
  tempEnv : TempEnv
  tc : TempCounter
  lc : LabelCounter

def translateTau : C0VC.TypedAst.Tau → Tree.Tau
  | .int | .char => .int
  | .bool => .bool
  | .string => panic! "[Error] strings are not yet handled"
  | .void => .void

def defaultValOfTau : C0VC.TypedAst.Tau → Tree.Expr
  | .int => .const .int 0
  | .bool => .const .bool 0
  | .void => .const .void 0

  -- TODO
  | .char
  | .string => .const .int 0


def translateBinOp (op: C0VC.TypedAst.BinOp) : Tree.BinOp :=
  match op with
  | .plus => .plus
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .lt => .lt
  | .lte => .lte
  | .gt => .gt
  | .gte => .gte
  | .eq => .eq
  | .neq => .neq
  | .bitAnd => .bitAnd
  | .xor => .xor
  | .bitOr => .bitOr
  | .shl => .shl
  | .shr => .shr

def tauOfBinOp : C0VC.TypedAst.BinOp → Tree.Tau
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .bool
  | _ => .int

partial def translateExpr
  (mexpr : C0VC.TypedAst.MarkedExpr)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × Tree.Expr × TempEnv × TempCounter × LabelCounter :=
  match mexpr.node with
  | .var name =>
    match env.get? name with
    | some temp => ([], .temp temp, env, tc, lc)
    | _ =>
      let (temp, tc') := Temp.bumpAndCreate tc
      ([], .temp temp, env.insert name temp, tc', lc)

  | .intLit val => ([], .const .int (Int32.ofInt val), env, tc, lc)

  | .binop op lhs rhs =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsLhs, transLhs, env', tc'', lc') := translateExpr lhs env tc' lc
    let (cmdsRhs, transRhs, env'', tc''', lc'') := translateExpr rhs env' tc'' lc'
    let cmd :=

      -- in C0, division/modulus by zero is not undefined behavior and instead always
      -- raises a runtime exception.

      -- TODO: Currently, we call a wrapper for div/mod ops
      -- but to save a function call, we may not want to do this.
      -- benchmark LLVM's inliner opt to see if this gets inlined otherwise, we should
      -- not call this wrapper for all div/mod ops
      match op with
      | .div => .move tempRes (.runtimeCall .checkedDiv [transLhs, transRhs])
      | .mod => .move tempRes (.runtimeCall .checkedMod [transLhs, transRhs])
      | _ => .move tempRes (.binop (translateBinOp op) transLhs transRhs)

    (cmdsLhs ++ cmdsRhs ++ [cmd]
    , .temp tempRes
    , env''
    , tc'''
    , lc'')

  -- TODO: LLVM supports select. is this really something we want to elaborate?
  | .ternary test thenVal elseVal =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsTest, transTest, env', tc'', lc') := translateExpr test env tc' lc
    let (labelThen, lc'') := Label.bumpAndCreate lc'
    let (labelElse, lc''') := Label.bumpAndCreate lc''

    let (cmdsThen, transThen, env'', tc''', lc''') := translateExpr thenVal env' tc'' lc'''
    let (cmdsElse, transElse, env''', tc'''', lc'''') := translateExpr elseVal env'' tc''' lc'''
    let (labelDone, lc''''') := Label.bumpAndCreate lc''''

    ([.declare tempRes (translateTau mexpr.tau)]
    ++ cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ [.move tempRes transThen]
    ++ [.goto labelDone]
    ++ [.label labelElse]
    ++ cmdsElse
    ++ [.move tempRes transElse]
    ++ [.goto labelDone]
    ++ [.label labelDone]

    , .temp tempRes
    , env'''
    , tc''''
    , lc'''''
    )

  | .trueLit => ([], .const .bool 1, env, tc, lc)
  | .falseLit => ([], .const .bool 0, env, tc, lc)

  -- TODO: fix this. definitely not the correct handling of chars
  | .charLit c => ([], .const .int (Int32.ofNat c.toNat), env, tc, lc)

  | .call fname args =>
    let (argCmds, argExps, env', tc', lc') := List.foldr
      (λ arg (cmdsAcc, expsAcc, envAcc, tcAcc, lcAcc) =>
        let (cmds, exp, env'', tc''', lc'') := translateExpr arg envAcc tcAcc lcAcc
        (cmds ++ cmdsAcc, exp :: expsAcc, env'', tc''', lc'')
      )
      ([], [], env, tc, lc)
      args
    let (tempRes, tc'') := Temp.bumpAndCreate tc'
    (argCmds ++ [.move tempRes (.call fname argExps)], .temp tempRes, env', tc'', lc')

  -- TODO
  | .length _ => ([], .const .int 0, env, tc, lc)
  | .result => ([], .const .int 0, env, tc, lc)
  | .hastag => ([], .const .int 0, env, tc, lc)
  | .stringLit _ => ([], .const .int 0, env, tc, lc)

partial def translateStm
  (mstm : C0VC.TypedAst.MarkedStm)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  match mstm.node with
  | .assign varName val =>
    let (cmds, expr, env', tc', lc') := translateExpr val env tc lc
    match env.get? varName with
    | some temp =>
      (cmds ++ [.move temp expr], env', tc', lc')
    | none =>
      let (temp, tc') := Temp.bumpAndCreate tc
      (cmds ++ [.move temp expr], env', tc', lc')

  | .ifLit test thenBranch elseBranch =>
    let (cmdsTest, transTest, env', tc', lc') := translateExpr test env tc lc
    let (cmdsThen, env'', tc'', lc'') := translateStm thenBranch env' tc' lc'
    let (cmdsElse, env''', tc''', lc''') := translateStm elseBranch env'' tc'' lc''

    let (labelThen, lc'''') := Label.bumpAndCreate lc'''
    let (labelElse, lc''''') := Label.bumpAndCreate lc''''
    let (labelDone, lc'''''') := Label.bumpAndCreate lc'''''

    (cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ [.goto labelDone]
    ++ [.label labelElse]
    -- TODO: if this is empty, consider not emitting to remove redundant labels
    ++ cmdsElse
    ++ [.goto labelDone]
    ++ [.label labelDone]
    , env'''
    , tc'''
    , lc''''''
    )

  | .whileLit test body =>
    let (cmdsTest, transTest, env', tc', lc') := translateExpr test env tc lc
    let (cmdsBody, env'', tc'', lc'') := translateStm body env' tc' lc'

    let (labelGuard, lc''') := Label.bumpAndCreateNamed lc'' "cond"
    let (labelBody, lc'''') := Label.bumpAndCreateNamed lc''' "body"
    let (labelDone, lc''''') := Label.bumpAndCreateNamed lc'''' "end"

    ([ .goto labelGuard
    , .label labelGuard]
    ++ cmdsTest
    ++ [ .ite transTest labelBody labelDone
       , .label labelBody]
    ++ cmdsBody
    ++ [ .goto labelGuard
       , .label labelDone]
    , env''
    , tc''
    , lc''''')

  | .ret valOpt =>
    match valOpt with
    | some retVal =>
      let (cmdsRetVal, transRetVal, env', tc', lc') := translateExpr retVal env tc lc
      (cmdsRetVal ++ [.ret (some transRetVal)], env', tc', lc')
    | none => ([.ret none], env, tc, lc)


  | .seq first rest =>
    let (cmdsFirst, env', tc', lc') := translateStm first env tc lc
    let (cmdsRest, env'', tc'', lc'') := translateStm rest env' tc' lc'

    (cmdsFirst ++ cmdsRest
    , env''
    , tc''
    , lc'')

  -- TODO: weave in type info into TempEnv
  | .declare varName _ value =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let (cmdsValue, env', tc'', lc') := translateStm value (env.insert varName temp) tc' lc
    (cmdsValue, env'.erase varName, tc'', lc')

  | .defn varName tau =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let defaultVal := defaultValOfTau tau
    ([.move temp defaultVal], env.insert varName temp, tc', lc)

  | .expr mexpr =>
    let (cmds, _, env', tc', lc') := translateExpr mexpr env tc lc
    (cmds, env', tc', lc')

  | .nop => ([], env, tc, lc)

  -- TODO
  | .assert _ => panic! "[Error] unimplemented (assert)"
  | .error _ => panic! "[Error] unimplemented (error)"
  | .annotation _ => panic! "[Error] unimplemented (annotation)"

def translateParam (param : C0VC.TypedAst.Param) : Tree.Arg :=
  let (tau, name) := param

  -- TODO: make this cleaner. why are we creating temp from name? seems dangerous
  (translateTau tau, Temp.fromName name)

def translateFunctionDef (fdefn : C0VC.TypedAst.FunctionDef) : Tree.FunctionDef :=
  let params := fdefn.params
  let (temps, tc) := Temp.bumpAndCreateK 0 params.length
  let paramsTemps := List.zip params temps
  let (params', seededEnv) := List.foldr
    -- TODO: i don't really like this, since it assumes that in the downstream pass, function args will preserve temp.name and also
    -- explicitly emit %temp.name
    (λ ((tau, varName), temp) (paramsAcc, envAcc) => ((translateTau tau, temp)::paramsAcc, envAcc.insert varName temp))
    ([], {})
    paramsTemps

  let (cmds, _, _, _) := (List.foldl
    (λ (cmdsAcc, envAcc, tcAcc, lcAcc) mstm =>
      let (cmds, env', tc', lc') := translateStm mstm envAcc tcAcc lcAcc
      (cmdsAcc ++ cmds, env', tc', lc')
    )
    ([], seededEnv, tc, 0)
    fdefn.body)
  ( fdefn.fname
  , translateTau fdefn.retType
  , params'
  , cmds)

def translate (program : C0VC.TypedAst.Program) : Tree.Program :=
  List.map translateFunctionDef program

end C0VC.LLVM.Tree.Trans
