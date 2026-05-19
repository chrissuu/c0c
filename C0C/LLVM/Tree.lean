/-
Tree Representation

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/
import C0C.Utils.Temp
import C0C.Utils.Label

namespace C0C.LLVM.Tree

open C0C.Utils.Temp
open C0C.Utils.Label

-- TODO: maybe consider deduplicating this definition against AST.BinOp?
inductive BinOp where
  | plus
  | sub
  | mul
  | div
  | mod
  | lt
  | lte
  | gt
  | gte
  | eq
  | neq
  | bitAnd
  | xor
  | bitOr
  | shl
  | shr
deriving Inhabited

inductive Tau where
  | int
  | bool
  | void
deriving Inhabited

inductive Expr where
  -- TODO: consider changing val type to val opt type to support voids
  -- eventually, will have to move this type to something more expressive
  -- than ints to be able to support chars/strings/etc
  | const (tau : Tau) (val : Int32)
  | temp (t : Temp)
  | binop (op : BinOp) (lhs : Expr) (rhs : Expr)
  | call (fname : String) (args : List Expr)
deriving Inhabited

inductive Command where
  | move (dest : Temp) (src : Expr)
  | ite (test : Expr) (thenBranch : Label) (elseBranch : Label)
  | goto (label : Label)
  | label (l : Label)
  | ret (valOpt : Option Expr)
deriving Inhabited

abbrev Arg := Tau × Temp
abbrev FunctionDef := String × Tau × List Arg × List Command
abbrev Program := List FunctionDef

namespace Print

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

def ppBinOp : BinOp → String
  | .plus => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .lt => "<"
  | .lte => "<="
  | .gt => ">"
  | .gte => ">="
  | .eq => "=="
  | .neq => "!="
  | .bitAnd => "&"
  | .xor => "^"
  | .bitOr => "|"
  | .shl => "<<"
  | .shr => ">>"

def ppTau : Tau → String
  | .int => "int"
  | .bool => "bool"
  | .void => "void"

def ppArg (arg : Arg) : String :=
  let (tau, temp) := arg
  s!"{ppTau tau} {temp.name}"

partial def ppExpr : Expr → String
  -- TODO: print the type of the const?
  | .const _ val => toString val
  | .temp t => t.name
  | .binop op lhs rhs => s!"({ppExpr lhs} {ppBinOp op} {ppExpr rhs})"
  | .call fname args => s!"call {fname}({String.intercalate ", " (List.map ppExpr args)})"

def ppCommand : Command → String
  | .move dest src => s!"{dest.name} <- {ppExpr src};"
  | .ite test thenBranch elseBranch =>
      s!"if ({ppExpr test}) goto {thenBranch.name} else goto {elseBranch.name}"
  | .goto label => s!"goto {label.name};"
  | .label l => s!"{l.name}:"
  | .ret valOpt =>
      match valOpt with
      | some val => s!"return {ppExpr val};"
      | none => "return;"

def ppFunctionDef (fdef : FunctionDef) : String :=
  let (fname, tau, args, commands) := fdef
  s!"{ppTau tau} {fname}({String.intercalate ", " (List.map ppArg args)})\n{String.intercalate "\n" (List.map ppCommand commands)}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n" (program.map ppFunctionDef)

mutual
partial def ppExprRaw (indentLevel : Nat) : Expr → String
  | .const tau val =>
      s!"{spaces indentLevel}Const({val}):{ppTau tau}"
  | .temp t =>
      s!"{spaces indentLevel}Temp({t.name})"
  | .binop op lhs rhs =>
      s!"{spaces indentLevel}Binop({ppBinOp op},\n{ppExprRaw (indentLevel + 1) lhs},\n{ppExprRaw (indentLevel + 1) rhs}\n{spaces indentLevel})"
  | .call fname args =>
      let argsStr := String.intercalate ",\n" (args.map (ppExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}Call({fname}, [\n{argsStr}\n{spaces indentLevel}])"

partial def ppCommandRaw (indentLevel : Nat) : Command → String
  | .move dest src =>
      s!"{spaces indentLevel}Move({dest.name},\n{ppExprRaw (indentLevel + 1) src}\n{spaces indentLevel})"
  | .ite test thenBranch elseBranch =>
      s!"{spaces indentLevel}Ite(\n{ppExprRaw (indentLevel + 1) test},\n{spaces (indentLevel + 1)}{thenBranch.name},\n{spaces (indentLevel + 1)}{elseBranch.name}\n{spaces indentLevel})"
  | .goto label =>
      s!"{spaces indentLevel}Goto({label.name})"
  | .label l =>
      s!"{spaces indentLevel}Label({l.name})"
  | .ret valOpt =>
      match valOpt with
      | some val =>
          s!"{spaces indentLevel}Ret(\n{ppExprRaw (indentLevel + 1) val}\n{spaces indentLevel})"
      | none =>
          s!"{spaces indentLevel}Ret(None)"
end

def ppFunctionDefRaw (fdef : FunctionDef) : String :=
  let (fname, tau, args, commands) := fdef
  let argsStr := String.intercalate ", " (args.map ppArg)
  let cmdsStr := String.intercalate "\n" (commands.map (ppCommandRaw 1))
  s!"Fdefn({ppTau tau}, {fname}, [{argsStr}], [\n{cmdsStr}\n])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppFunctionDefRaw)}"

end Print

instance : ToString BinOp where
  toString := Print.ppBinOp

instance : ToString Expr where
  toString := Print.ppExpr

instance : ToString Command where
  toString := Print.ppCommand

instance : ToString Program where
  toString := Print.ppProgram

end C0C.LLVM.Tree
