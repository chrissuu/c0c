import C0VC.Ast.ElabbedAst

namespace C0VC.TypedAst

abbrev Tau := C0VC.ElabbedAst.Tau
abbrev BinOp := C0VC.ElabbedAst.BinOp
abbrev Param := Tau × String

mutual
inductive Expr where
  | var (name : String)
  | intLit (val : Int)
  | binop (op : BinOp) (lhs : TypedExpr) (rhs : TypedExpr)
  | ternary (test : TypedExpr) (thenVal : TypedExpr) (elseVal : TypedExpr)
  | trueLit
  | falseLit
  | charLit (char : Char)
  | stringLit (string : String)
  | call (fname : String) (args : List TypedExpr)
  | length (arrayLike : TypedExpr)
  | result
  | hastag

structure TypedExpr where
  node : Expr
  tau : Tau
end

mutual
inductive Anno where
  | requires (precondition : TypedExpr)
  | ensures (postcondition : TypedExpr)
  | asserts (e : TypedExpr)
  | loopInvariant (e : TypedExpr)

structure TypedAnno where
  node : Anno
end

mutual
inductive Stm where
  | assign (varName : String) (val : TypedExpr)
  | ifLit (test : TypedExpr) (thenBranch : TypedStm) (elseBranch : TypedStm)
  | whileLit (test : TypedExpr) (body : TypedStm)
  | ret (valOpt : Option TypedExpr)
  | seq (first : TypedStm) (rest : TypedStm)
  | declare (varName : String) (type : Tau) (value : TypedStm)
  | defn (varName : String) (type : Tau)
  | expr (e : TypedExpr)
  | assert (test : TypedExpr)
  | error (e : TypedExpr)
  | nop
  | annotation (a : TypedAnno)

structure TypedStm where
  node : Stm
end

structure FunctionDef where
  retType : Tau
  fname : String
  params : List Param
  body : List TypedStm
  annotations : List TypedStm

abbrev Program := List FunctionDef

end C0VC.TypedAst
