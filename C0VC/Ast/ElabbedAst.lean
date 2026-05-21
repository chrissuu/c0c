/-
Elaborated AST Core Definitions

This AST is the post-elaboration surface for later compiler phases. It omits
syntax that should be desugared away before typechecking/lowering, such as
assignment operators, for loops, increment/decrement, unary operators, short
circuit operators, and typedef declarations.
-/
import C0VC.Utils.SrcSpan

open C0VC.Utils.SrcSpan

namespace C0VC.ElabbedAst

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
  | char
  | string
  | bool
  | void
deriving Inhabited

mutual
inductive Expr where
  | var (name : String)
  | intLit (val : Int)
  | binop (op : BinOp) (lhs : MarkedExpr) (rhs : MarkedExpr)
  | ternary (test : MarkedExpr) (thenVal : MarkedExpr) (elseVal : MarkedExpr)
  | trueLit
  | falseLit
  | charLit (char : Char)
  | stringLit (string : String)
  | call (fname : String) (args : List MarkedExpr)
  | length (arrayLike : MarkedExpr)
  | result
  | hastag

structure MarkedExpr where
  node : Expr
  span : Option SrcSpan
end

mutual
inductive Anno where
  | requires (precondition : MarkedExpr)
  | ensures (postcondition : MarkedExpr)
  | asserts (e : MarkedExpr)
  | loopInvariant (e : MarkedExpr)

structure MarkedAnno where
  node : Anno
  span : Option SrcSpan
end

mutual
inductive Stm where
  | assign (varName : String) (val : MarkedExpr)
  | ifLit (test : MarkedExpr) (thenBranch : MarkedStm) (elseBranch : MarkedStm)
  | whileLit (test : MarkedExpr) (body : MarkedStm)
  | ret (valOpt : Option MarkedExpr)
  | seq (first : MarkedStm) (rest : MarkedStm)
  | declare (varName : String) (type : Tau) (value : MarkedStm)
  | defn (varName : String) (type : Tau)
  | expr (e : MarkedExpr)
  | assert (test : MarkedExpr)
  | error (e : MarkedExpr)
  | nop
  | annotation (a : MarkedAnno)

structure MarkedStm where
  node : Stm
  span : Option SrcSpan
end

abbrev Param := Tau × String

structure FunctionDef where
  retType : Tau
  fname : String
  params : List Param
  body : List MarkedStm
  annotations : List MarkedStm

abbrev Program := List FunctionDef

namespace Print

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
  | .string => "string"
  | .char => "char"
  | .int => "int"
  | .bool => "bool"
  | .void => "void"

private def indent (str : String) : String :=
  str.splitOn "\n"
    |> List.map (fun line => "  " ++ line)
    |> String.intercalate "\n"

mutual
partial def ppExpr : Expr → String
  | .var id => id
  | .intLit n => toString n
  | .trueLit => "true"
  | .falseLit => "false"
  | .stringLit s => s
  | .charLit c => toString c
  | .binop op lhs rhs =>
      s!"({ppMarkedExpr lhs} {ppBinOp op} {ppMarkedExpr rhs})"
  | .ternary test thenBranch elseBranch =>
      s!"({ppMarkedExpr test} ? {ppMarkedExpr thenBranch} : {ppMarkedExpr elseBranch})"
  | .call fname args =>
      let argsStr := String.intercalate ", " (args.map ppMarkedExpr)
      s!"{fname}({argsStr})"
  | .length arrayLike => s!"\\length ({ppMarkedExpr arrayLike})"
  | .result => "\\result"
  | .hastag => "\\hastag"

partial def ppMarkedExpr (e : MarkedExpr) : String :=
  ppExpr e.node
end

mutual
def ppAnno : Anno → String
  | .requires precondition => s!"//@requires ({ppMarkedExpr precondition})"
  | .ensures postcondition => s!"//@ensures ({ppMarkedExpr postcondition})"
  | .asserts e => s!"//@asserts ({ppMarkedExpr e})"
  | .loopInvariant e => s!"//@loop_invariant ({ppMarkedExpr e})"

def ppMarkedAnno (a : MarkedAnno) : String :=
  ppAnno a.node
end

mutual
partial def ppStm : Stm → String
  | .assign id e =>
      s!"{id} = {ppMarkedExpr e};"
  | .defn id tau =>
      s!"{ppTau tau} {id};"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"return {ppMarkedExpr e};"
      | none => "return;"
  | .nop =>
      "/* nop */"
  | .expr e =>
      s!"{ppMarkedExpr e};"
  | .assert test =>
      s!"assert({ppMarkedExpr test});"
  | .error e =>
      s!"error({ppMarkedExpr e});"
  | .declare id tau body =>
      let bodyStr := ppStm body.node
      if bodyStr.isEmpty || bodyStr == "/* nop */" then
        s!"{ppTau tau} {id};"
      else
        s!"{ppTau tau} {id};\n{bodyStr}"
  | .seq s1 s2 =>
      s!"{ppMarkedStm s1}\n{ppMarkedStm s2}"
  | .ifLit cond thenBranch elseBranch =>
      let thenStr := indent (ppMarkedStm thenBranch)
      let elseStr := ppMarkedStm elseBranch
      if elseStr == "/* nop */" then
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n}"
      else
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n} else \{\n{indent elseStr}\n}"
  | .whileLit cond body =>
      s!"while ({ppMarkedExpr cond}) \{\n{indent (ppMarkedStm body)}\n}"
  | .annotation a => s!"{ppMarkedAnno a}"

partial def ppMarkedStm (s : MarkedStm) : String :=
  ppStm s.node
end

def ppStms (stms : List MarkedStm) : String :=
  String.intercalate "" (stms.map fun stm => indent (ppMarkedStm stm) ++ "\n")

def ppParam : Param → String
  | (tau, id) => s!"{ppTau tau} {id}"

def ppParams (params : List Param) : String :=
  let paramsStr := String.intercalate ", " (params.map ppParam)
  s!"({paramsStr})"

def ppAnnos (annos : List MarkedStm) : String :=
  let annosStr := String.intercalate ", " (annos.map ppMarkedStm)
  s!"[{annosStr}]"

def ppFunctionDef (fdefn : FunctionDef) : String :=
  if fdefn.body.isEmpty then
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n}"
  else
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n{ppStms fdefn.body}}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppFunctionDef)

end Print

end C0VC.ElabbedAst
