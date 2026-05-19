namespace C0C.Utils.Temp

structure Temp where
  name : String
deriving Repr, DecidableEq, Inhabited

abbrev TempCounter := Nat

def TempCounter.bump tc :=
  tc + 1

def Temp.fromName (name : String) : Temp :=
  { name := s!"{name}"}

def Temp.create (tc : TempCounter) : Temp :=
  { name := s!"t{tc}" }

def Temp.createNamed (tc : TempCounter) (name : String): Temp :=
  { name := s!"t{tc}_{name}" }

def Temp.bumpAndCreate (tc : TempCounter) : Temp × TempCounter :=
  let tc' := TempCounter.bump tc
  ({ name := s!"t{tc'}" }, tc')

def Temp.bumpAndCreateK (tc : TempCounter) (k : Nat) : List Temp × TempCounter :=
  let rec go (n : Nat) (tcAcc : TempCounter) (tempsAcc : List Temp) : List Temp × TempCounter :=
    match n with
    | 0 => (tempsAcc.reverse, tcAcc)
    | n' + 1 =>
      let (t, tc') := Temp.bumpAndCreate tcAcc
      go n' tc' (t :: tempsAcc)
  go k tc []

def Temp.bumpAndCreateNamed (tc : TempCounter) (name : String) : Temp × TempCounter :=
  let tc' := TempCounter.bump tc
  ({ name := s!"t{tc'}_{name}" }, tc')

end C0C.Utils.Temp
