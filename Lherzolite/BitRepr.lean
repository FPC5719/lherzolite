import Parser
import Lherzolite.HList

open Parser Char

def Bits (n : Nat) : Type := Vector Bool n

inductive ABit where
| high
| low
| any

def ABits (n : Nat) : Type := Vector ABit n

def Bits.toABits (b : Bits n) : ABits n :=
  b.map fun
  | true  => .high
  | false => .low

def Slice (n : Nat) : Type :=
  { s : Nat × Nat // match s with
    | (l, r) => l < n ∧ l ≥ r
  }

def Slice.extend (δ : Nat) (le : n + δ ≤ m) (s : Slice n) : Slice m :=
  let ⟨(l, r), pn⟩ := s
  let pm : (l + δ < m) ∧ (l + δ ≥ r + δ) := by
    apply And.intro
    calc l + δ
      _ < n + δ := by simp [pn.left]
      _ ≤ m     := le
    simp [pn.right]
  ⟨(l + δ, r + δ), pm⟩

def SliceTy (s : Slice n) : Type :=
  match s with
  | ⟨(l, r), _⟩ => Bits (l - r + 1)

structure BitMask (n : Nat) : Type where
  care  : Bits n
  equal : Bits n
  pat   : List (Slice n)

instance : HAppend (BitMask n) (BitMask m) (BitMask (n + m)) where
  hAppend p q := {
    care  := Vector.append p.care  q.care ,
    equal := Vector.append p.equal q.equal,
    pat   := List.append
      (p.pat.map (Slice.extend m (Nat.le_refl (n + m))))
      (q.pat.map (Slice.extend 0 (Nat.le_add_left m n)))
  }

def BitMask.empty : BitMask 0 := {
  care  := Vector.mkEmpty 0,
  equal := Vector.mkEmpty 0,
  pat   := []
}

def PatArgsTy (pat : List (Slice n)) : Type 1 :=
  HList (pat.map SliceTy)

abbrev BitMask.Parser (α : Type) : Type :=
  SimpleParser Substring Char α

def BitMask.parser : BitMask.Parser ((n : Nat) × BitMask n) := do
  let seg : BitMask.Parser ((n : Nat) × BitMask n) := do
    let s := Parser.token '_'
    let b := do
      pure (← Parser.tokenList ['0', '1', '?']).toArray
    let res ← Parser.sepBy1 s (Parser.takeMany1 b)
    let resf := res.flatten.flatten.toVector
    let k : BitMask resf.size := {
      care  := resf.map fun
        | '0' | '1' => true
        | _         => false,
      equal := resf.map fun
        | '1' => true
        | _   => false,
      pat   := []
    }
    pure ⟨resf.size, k⟩
  let pseg : BitMask.Parser ((n : Nat) × BitMask n) := do
    let ⟨n, k⟩ ← Parser.token '(' *> seg <* Parser.token ')'
    match n with
    | 0 => pure ⟨0, k⟩
    | .succ m =>
      pure ⟨m.succ, { k with pat := [⟨(m, 0), by simp⟩] }⟩
  let resl ← takeMany1 $ pseg <|> seg
  let res : (n : Nat) × BitMask n := resl.foldl
    (fun ⟨n, kn⟩ ⟨m, km⟩ => ⟨n + m, kn ++ km⟩)
    ⟨0, BitMask.empty⟩
  pure res



inductive BitPrimOp : Type where
| and
| or
| xor

inductive BitRepr : Nat → Type 1 where
-- Bit literal
| literal :
    Bits n →
  BitRepr n
-- Primitive operators, grouped by bit width conversion
-- Concat
| concat :
    BitRepr m →
    BitRepr n →
  BitRepr (m + n)
-- Add with cin and cout
| add :
    BitRepr n →
    BitRepr n →
    BitRepr 1 →
  BitRepr (n + 1)
-- Bitwise complement
| not :
    BitRepr n →
  BitRepr n
-- Binary operators (and, or, xor)
| bin :
    BitPrimOp →
    BitRepr n →
    BitRepr n →
  BitRepr n
-- Unary reduce (and, or, xor)
| reduce :
    BitPrimOp →
    BitRepr n →
  BitRepr 1
-- Dispatch a value according to masks
| dispatch :
    BitRepr m →
    (k : BitMask m) →
    (PatArgsTy k.pat → BitRepr n) →
    BitRepr n →
  BitRepr n
