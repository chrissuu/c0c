import C0VC.LLVM.IR

namespace C0VC.LLVM.Runtime

inductive Fn where
  | checkedDiv
  | checkedMod
deriving Inhabited, BEq

def name : Fn → String
  | .checkedDiv => "__c0vc_checked_div"
  | .checkedMod => "__c0vc_checked_mod"

def retTau : Fn → IR.Tau
  | .checkedDiv
  | .checkedMod => .i32

def argsTau : Fn → List IR.Tau
  | .checkedDiv
  | .checkedMod => [.i32, .i32]

def all : List Fn :=
  [.checkedDiv, .checkedMod]

end C0VC.LLVM.Runtime
