import C0VC.LLVM.IR

namespace C0VC.LLVM.Runtime

inductive Fn where
  | checkedDiv
  | checkedMod
  | checkedShl
  | checkedShr
deriving Inhabited, BEq

def name : Fn → String
  | .checkedDiv => "__c0vc_checked_div"
  | .checkedMod => "__c0vc_checked_mod"
  | .checkedShl => "__c0vc_checked_shl"
  | .checkedShr => "__c0vc_checked_shr"

def retTau : Fn → IR.Tau
  | .checkedDiv
  | .checkedMod
  | .checkedShl
  | .checkedShr => .i32

def argsTau : Fn → List IR.Tau
  | .checkedDiv
  | .checkedMod
  | .checkedShl
  | .checkedShr => [.i32, .i32]

def all : List Fn :=
  [.checkedDiv, .checkedMod, .checkedShl, .checkedShr]

end C0VC.LLVM.Runtime
