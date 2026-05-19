namespace C0C.Utils.Label

structure Label where
  name : String
deriving Repr, DecidableEq, Inhabited

abbrev LabelCounter := Nat

def LabelCounter.bump lc :=
  lc + 1

def Label.create (lc : LabelCounter) : Label :=
  { name := s!"L{lc}" }

def Label.createNamed (lc : LabelCounter) (name : String) : Label :=
  { name := s!"L{lc}_{name}" }

def Label.bumpAndCreate (lc : LabelCounter) : Label × LabelCounter :=
  let lc' := LabelCounter.bump lc
  ({ name := s!"L{lc'}" }, lc')

def Label.bumpAndCreateNamed (lc : LabelCounter) (name : String) : Label × LabelCounter :=
  let lc' := LabelCounter.bump lc
  ({ name := s!"L{lc'}_{name}" }, lc')

end C0C.Utils.Label
