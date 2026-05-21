import C0VC.LLVM.Tree
import C0VC.LLVM.IR
import C0VC.LLVM.Runtime
import C0VC.Utils.Temp
import C0VC.Utils.Label
import Std.Data.HashMap

open C0VC.LLVM.Tree
open C0VC.LLVM.IR
open C0VC.Utils.Temp
open C0VC.Utils.Label
open Std.HashMap
open C0VC.LLVM.Runtime

namespace C0VC.LLVM.Codegen

structure FunctionInfo where
  retTau : IR.Tau
  argsTau : List IR.Tau
deriving Inhabited

abbrev FEnv := Std.HashMap String FunctionInfo

structure TempInfo where
  temp : Temp
  tau : IR.Tau
  isPtr : Bool
deriving Inhabited

abbrev TEnv := Std.HashMap String TempInfo

def ppTempInfo (tInfo : TempInfo) : String :=
  s!"{tInfo.temp.name} : {IR.Print.ppTau tInfo.tau}"

def translateBinOp : Tree.BinOp → IR.BinOp
  | .plus => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .sdiv
  | .mod => .srem
  | .bitAnd => .and
  | .xor => .xor
  | .bitOr => .or
  | .shl => .shl
  | .shr => .ashr
  | .lt => .slt
  | .lte => .sle
  | .gt => .sgt
  | .gte => .sge
  | .eq => .eq
  | .neq => .ne

def isCmpOp : Tree.BinOp → Bool
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => false
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => true

def tauOfBinOp : Tree.BinOp → IR.Tau
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => .i32
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .i1

def runtimeFunctionInfo (fn : Runtime.Fn) : FunctionInfo :=
  { retTau := Runtime.retTau fn, argsTau := Runtime.argsTau fn }

def isAtom : Tree.Expr → Bool
  | .const _ _ | .temp _ => true
  | _ => false

def translateTau : Tree.Tau → IR.Tau
  | .int => .i32
  | .bool => .i1
  | .void => .void

def translateExpr (expr : Tree.Expr) (tc : TempCounter) (fenv : FEnv) (tenv : TEnv): List IR.Stm × IR.Val × IR.Tau × TempCounter × TEnv :=
  match expr with
  | .const tau val =>
    ( []
    , .bitVec (BitVec.ofInt 32 (Int32.toInt val))
    , translateTau tau
    , tc
    , tenv)

  | .temp var =>
    -- Look-up var in env and if it exists, use it.
    -- Not existing in the env is an impossible case, since this implies it is used before
    -- being defined.
    match tenv.get? var.name with
    | some tempInfo =>
      match tempInfo.isPtr with
      | true =>
        let (temp, tc') := Temp.bumpAndCreate tc
        ( [ .load (.var temp) tempInfo.tau (.ptr tempInfo.temp) ]
        , .var temp
        , tempInfo.tau
        , tc'
        , tenv)

      | false =>
        ( []
        , .var tempInfo.temp
        , tempInfo.tau
        , tc
        , tenv)

    | none => panic! s!"[Error] saw a var ({var.name}) used before being defined"

  | .binop op lhs rhs =>
    let tau : IR.Tau := if isCmpOp op then .i1 else .i32
    let (stmsLhs, transLhs, _, tc', tenv') := translateExpr lhs tc fenv tenv
    let (stmsRhs, transRhs, _, tc'', tenv'') := translateExpr rhs tc' fenv tenv'
    let (temp, tc''') := Temp.bumpAndCreate tc''
    ( stmsLhs ++ stmsRhs ++ [ .assign (.var temp) (.binop (translateBinOp op) tau transLhs transRhs) ]
    , .var temp
    , tauOfBinOp op
    , tc'''
    , tenv''
    )

  | .call fname args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let fInfo := fenv.get! fname
    let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
    match retTau with
    | .void =>
      ( stms ++ [.callVoid fname (List.zip argsTau transArgs)]
      , .void
      , retTau
      , tc'
      , tenv'
      )
    | _ =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [ .assign (.var temp) (.call retTau fname (List.zip argsTau transArgs)) ]
      , .var temp
      , retTau
      , tc''
      , tenv'
      )

  | .runtimeCall fn args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let fname := Runtime.name fn
    let fInfo := runtimeFunctionInfo fn
    let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
    match retTau with
    | .void =>
      ( stms ++ [.callVoid fname (List.zip argsTau transArgs)]
      , .void
      , retTau
      , tc'
      , tenv'
      )
    | _ =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [ .assign (.var temp) (.call retTau fname (List.zip argsTau transArgs)) ]
      , .var temp
      , retTau
      , tc''
      , tenv'
      )

def mkFenv (program : Tree.Program) : FEnv :=
  List.foldl
  (λ env (fname, tau, args, _) =>
    env.insert fname (FunctionInfo.mk (translateTau tau)
    (List.map (λ (tau, _) => translateTau tau) args))
  )
  {}
  program

-- MOVE CONVENTIONS:
-- If dest exists in env:
--    if it's a ptr type, update ptr type, don't do anything else
--    if it's not a ptr type, update env with the temp which stores the src
-- If dest doesn't exist in env:
--    create a new ptr which houses this src

-- USAGE RULES:
-- When consuming a temp:
--    if it's a ptr, then we must create a new temp, load from ptr, and then use this new temp
--    if it's not a ptr, then ensure that we're only reading reg/value, and consume it

def isOfPtr (temp : Temp) (tenv : TEnv) : Bool :=
  match tenv.get? temp.name with
  | some tInfo => tInfo.isPtr
  | _ => false

def translateCmd
  (cmd : Tree.Command)
  (tc : TempCounter)
  (lc : LabelCounter)
  (fenv : FEnv)
  (tenv : TEnv)
: List IR.Stm × TempCounter × LabelCounter × TEnv :=
  match cmd with
  | .declare dest tau =>
    let (ptr, tc') := Temp.bumpAndCreate tc
    let tau' := translateTau tau
    ( [ .alloca (.ptr ptr) tau' ]
    , tc'
    , lc
    , tenv.insert dest.name (TempInfo.mk ptr tau' true)
    )

  | .move dest src =>
    -- transVal will be an atom (i.e., reg, imm) at this point
    let (stms, transVal, tau, tc', tenv') := translateExpr src tc fenv tenv
    let bindDestToValue (value : IR.Val) (tcBase : TempCounter) (tenvBase : TEnv) :=
      match value with
      | .var t =>
        let destTempInfo := TempInfo.mk t tau false
        ( stms
        , none
        , tcBase
        , tenvBase.insert dest.name destTempInfo)

      | .bitVec _ =>
        let (ptr, tcNext) := Temp.bumpAndCreate tcBase
        let destTempInfo := TempInfo.mk ptr tau true
        ( stms ++ [ Stm.alloca (.ptr ptr) tau ]
        , some ptr
        , tcNext
        , tenvBase.insert dest.name destTempInfo)

      | _ => panic! "[Error] after translating expr type, expect REG/IMM but found something else"
    let (stms', ptrOpt, tc'', tenv'') :=
      match tenv'.get? dest.name with
      | some destTempInfo =>
        match destTempInfo.isPtr with
        | true =>
          ( stms
          , some destTempInfo.temp
          , tc'
          , tenv')

        | false =>
          -- since dest is not a pointer type, update tenv to carry this src's value
          bindDestToValue transVal tc' tenv'

      | none =>
        -- dest is a new temp, so update tenv here as well
        bindDestToValue transVal tc' tenv'

    let destIsPtr := Option.isSome ptrOpt

    ( stms' ++
      if destIsPtr then [ .store tau transVal (.ptr ptrOpt.get!) ] else []
    , tc''
    , lc
    , tenv'')

  | .ite test thenBranch elseBranch =>
    let (stms, transTest, _, tc', tenv') := translateExpr test tc fenv tenv

    ( stms ++ [ .brIte transTest thenBranch elseBranch]
    , tc'
    , lc
    , tenv'
    )

  | .goto l =>

    ( [.brJump l]
    , tc
    , lc
    , tenv
    )

  | .label l =>

    ( [.label l]
    , tc
    , lc
    , tenv
    )

  | .ret valOpt =>
    match valOpt with
    | some expr =>
      let (stms, transExpr, _, tc', tenv') := translateExpr expr tc fenv tenv

      ( stms ++ [ .ret transExpr ]
      , tc'
      , lc
      , tenv'
      )

    | none =>

      ( [.ret .void ]
      , tc
      , lc
      , tenv
      )

def translateArg (arg : Tree.Arg) : IR.Arg :=
  let (tau, temp) := arg
  (translateTau tau, temp.name)

def translateArgs (args : List Tree.Arg) : List IR.Arg := List.map translateArg args

def translateFdefn (fdefn : Tree.FunctionDef) (fenv : FEnv) : IR.FunctionDef :=
  let (fname, tau, args, cmds) := fdefn

  -- TODO: once again, this is pretty dangerous, since it sort of breaks the Temp.bumpAndCreate invariant
  let seededTc := List.foldl
    (λ tcAcc (_, _) =>
      let (_, tc) := Temp.bumpAndCreate tcAcc
      tc
    )
    0
    args

  let (stms, seededTEnv', tc') := List.foldr
    (λ (tau, temp) (stmsAcc, tenvAcc, tcAcc) =>
      let (ptr, tc') := Temp.bumpAndCreate tcAcc
      let alloca : IR.Stm := .alloca (.ptr ptr) (translateTau tau)
      let store : IR.Stm := .store (translateTau tau) (.var temp) (.ptr ptr)
      (alloca::store::stmsAcc, (tenvAcc.insert temp.name (TempInfo.mk ptr (translateTau tau) true), tc')
    ))
    ([], {}, seededTc)
    args

  let (transCmds, _, _, _) :=
    List.foldl
    (λ (stmsAcc, tcAcc, lcAcc, tenvAcc) cmd =>
      let (stms, tc', lc', tenv') := translateCmd cmd tcAcc lcAcc fenv tenvAcc
      (stmsAcc ++ stms, tc', lc', tenv')
    )
    (stms, tc', 0, seededTEnv')
    cmds

  ( fname
  , translateTau tau
  , translateArgs args
  , transCmds)


def translate (program : Tree.Program) : IR.Program :=
  let fenvInit := mkFenv program

  let transProgram :=
    List.foldl
    (λ fdefnAcc fdefn =>
      let (transFdefn) := translateFdefn fdefn fenvInit
      (fdefnAcc ++ [transFdefn])
    )
    []
    program

  transProgram

end C0VC.LLVM.Codegen
