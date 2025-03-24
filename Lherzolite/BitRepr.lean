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

def SliceTy (s : Slice n) : Type :=
  match s with
  | ⟨(l, r), _⟩ => Bits (l - r + 1)

structure BitMask (n : Nat) : Type where
  care  : Bits n
  equal : Bits n
  pat   : List (Slice n)

def PatArgsTy (pat : List (Slice n)) : Type 1 :=
  HList (pat.map SliceTy)

abbrev BitMask.Parser (α : Type) : Type :=
  SimpleParser Substring Char α

def BitMask.parser : BitMask.Parser ((n : Nat) × BitMask n) := do
  let seg : BitMask.Parser _ :=
    let s := Parser.token '_'
    let b := Parser.tokenList ['0', '1', '?']
    Parser.sepBy1 s (Parser.takeMany1 b)
  let pseg : BitMask.Parser _ := do
    let _ ← Parser.token '('
    let sg ← seg
    let _ ← Parser.token ')'
    pure sg
  _





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
