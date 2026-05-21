import C0VC.Ast.ElabbedAst

namespace C0VC.TypedAst

abbrev Tau := C0VC.ElabbedAst.Tau
abbrev BinOp := C0VC.ElabbedAst.BinOp
abbrev Param := Tau × String

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
  tau : Tau
end

mutual
inductive Anno where
  | requires (precondition : MarkedExpr)
  | ensures (postcondition : MarkedExpr)
  | asserts (e : MarkedExpr)
  | loopInvariant (e : MarkedExpr)

structure MarkedAnno where
  node : Anno
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
end

structure FunctionDef where
  retType : Tau
  fname : String
  params : List Param
  body : List MarkedStm
  annotations : List MarkedStm

abbrev Program := List FunctionDef

end C0VC.TypedAst
