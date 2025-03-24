def Bits (n : Nat) : Type := Vector Bool n

def Slice (n : Nat) : Type :=
  { s : Nat × Nat // match s with
    | (l, r) => l < n ∧ l ≥ r
  }

structure BitMask (n : Nat) : Type where
  care  : Bits n
  equal : Bits n
  pat   : List (Slice n)

def BitMask.Cont.{u}
      {n : Nat}
      (ρ : Type u)
      (α : Nat → Type u)
      (k : BitMask n) :
    Type u :=
  let rec go : List (Slice n) → Type u
          | [] => ρ
          | s :: xs => match s with
            | ⟨(l, r), _⟩ => α (l - r + 1) → go xs
  go k.pat

mutual

inductive MyDPair : Type where
| dpair : (k : BitMask m) → k.Cont (BitRepr n) BitRepr → MyDPair

inductive MyList : Type where
| nil : MyList
| cons : MyDPair → MyList → MyList

inductive BitRepr : Nat → Type where
  | const : Bits n → BitRepr n
  | dispatch :
      BitRepr m →
      MyList →
      BitRepr n →
      BitRepr n

end
