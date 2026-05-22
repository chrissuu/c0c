import C0VC.Ast.ParsedAst
import C0VC.LLVM.IR
import C0VC.LLVM.Runtime
open C0VC
open C0VC.Ast
open C0VC.LLVM.IR
open C0VC.LLVM.Runtime

namespace C0VC.LLVM.EmitLlvm

def emitTau : IR.Tau → String
  | .i1 => "i1"
  | .i8 => "i8"
  | .i32 => "i32"
  | .void => "void"

def emitBinOp : IR.BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .sdiv => "sdiv"
  | .srem => "srem"
  | .and => "and"
  | .xor => "xor"
  | .or => "or"
  | .shl => "shl"
  | .ashr => "ashr"
  | .slt => "slt"
  | .sgt => "sgt"
  | .sle => "sle"
  | .sge => "sge"
  | .eq => "eq"
  | .ne => "ne"

def isCmpOp : IR.BinOp → Bool
  | .add
  | .sub
  | .mul
  | .sdiv
  | .srem
  | .and
  | .xor
  | .or
  | .shl
  | .ashr => false
  | .slt
  | .sgt
  | .sle
  | .sge
  | .eq
  | .ne => true

def emitArgs (args : List IR.Arg) : String :=
  ", ".intercalate (List.map (λ (tau, varName) => s!"{emitTau tau} %{varName}") args)

mutual
partial def emitFEvals (args : List (IR.Tau × IR.Val)) : String :=
  ", ".intercalate (List.map
  (λ (tau, arg) => s!"{emitTau tau} {emitVal arg}") args)


partial def emitVal : IR.Val → String
  | .void => ""
  | .var t => s!"%{t.name}"
  | .ptr t => s!"%{t.name}"
  | .bitVec bv => toString (Int32.ofInt (bv.toInt))
end

def emitExpr : IR.Expr → String
  | .binop op tau lhs rhs =>
    s!"{if isCmpOp op then "icmp " else ""}{emitBinOp op} {emitTau tau} {emitVal lhs}, {emitVal rhs}"
  | .call tau fname args =>
    s!"call {emitTau tau} @{fname}({emitFEvals args})"

def emitStm (retTau : IR.Tau) : IR.Stm → String
  | .assign dest src  => s!"{emitVal dest} = {emitExpr src}"

  | .callVoid fname args =>
    s!"call void @{fname}({emitFEvals args})"

  | .label l =>
    s!"{l.name}:"

  | .brJump l =>
    s!"br label %{l.name}"

  | .brIte val thenBranch elseBranch =>
    s!"br i1 {emitVal val}, label %{thenBranch.name}, label %{elseBranch.name}"

  | .ret val =>
    match retTau with
    | .void => s!"ret void"
    | _ => s!"ret {emitTau retTau} {emitVal val}"

  | .alloca ptr tau =>
    s!"{emitVal ptr} = alloca {emitTau tau}"

  | .store tau val ptr =>
    s!"store {emitTau tau} {emitVal val}, ptr {emitVal ptr}"

  | .load dest tau ptr =>
    s!"{emitVal dest} = load {emitTau tau}, ptr {emitVal ptr}"

def emitFdefn (fdefn : IR.FunctionDef) : String :=
  let (fname, tau, args, stms) := fdefn
  let emitStms := stms.map (emitStm tau)
  let markIndent := stms.map (fun stm => match stm with | .label _ => false | _ => true)

  let formattedEmitStm :=
    (List.zip markIndent emitStms)
      |> List.map (fun (indent, rawEmitStm) =>
        if indent then "\t" ++ rawEmitStm else rawEmitStm)
      |> String.intercalate "\n"

  let fname' := if String.Slice.beq fname "main" then "_c0_main" else fname

  s!"define {emitTau tau} "
  ++ s!"@{fname'}({emitArgs args}) "
  ++ "{"
  ++ "\n"
  ++ formattedEmitStm
  ++ "\n"
  ++ "}"

def emitParamTaus (taus : List IR.Tau) : String :=
  ", ".intercalate (taus.map emitTau)

def emitRuntimeDecl (fn : Runtime.Fn) : String :=
  s!"declare {emitTau (Runtime.retTau fn)} @{Runtime.name fn}({emitParamTaus (Runtime.argsTau fn)})"

def runtimeDecls : String :=
  String.intercalate "\n" (Runtime.all.map emitRuntimeDecl)

def emit (program : IR.Program) (fileName : String): IO Unit :=
  let rawProgram := "\n\n".intercalate (List.map emitFdefn program)
  IO.FS.writeFile fileName (runtimeDecls ++ "\n\n" ++ rawProgram)

end C0VC.LLVM.EmitLlvm
