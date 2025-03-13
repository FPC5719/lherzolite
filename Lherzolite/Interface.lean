inductive ITerm : Type (u + 1) where
  | Input  : String → Type u → ITerm
  | Output : String → Type u → ITerm
  | IRec   : String → List ITerm → ITerm

infix:50 "<~~" => ITerm.Input
infix:50 "~~>" => ITerm.Output
infix:50 "~=~" => ITerm.IRec

abbrev Interface : Type (u + 1) := List ITerm

def ITerm.size : ITerm → Nat
  | Input  _ _  => 1
  | Output _ _  => 1
  | IRec   _ ts => 1 + go ts
    where
      go : List ITerm → Nat
      | [] => 0
      | (t :: ts) => t.size + go ts

def ITerm.flip : ITerm → ITerm
  | Input  s α  => Output s α
  | Output s α  => Input  s α
  | IRec   s ts => IRec   s (go ts)
    where
      go : List ITerm → List ITerm
      | [] => []
      | (t :: ts) => t.flip :: go ts

example : Interface :=
  [ "In1"  <~~ UInt16
  , "Out1" ~~> UInt16
  , .flip $ "Port" ~=~ 
    [ "Ok"  <~~ Bool
    , "Val" ~~> UInt8
    ]
  ]
