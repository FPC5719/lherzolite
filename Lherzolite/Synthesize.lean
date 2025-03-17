-- Temporary Intermediate Representation
-- Should be replaced with safer version
abbrev TempRep : Type := String

-- A synthesized object
inductive Syn (α : Type) : Type where
| TempSyn : TempRep → Syn α


class SynthWidth (α : Type) where
  width : Nat

-- α is synthesizable
class Synth (α : Type) extends SynthWidth α where
  synth : α → Syn α

def Syn.coerce
      {α β : Type} [cα : SynthWidth α] [cβ : SynthWidth β]
      (x : Syn α)
      (_ : cα.width = cβ.width := by
        simp [SynthWidth.width]
      ) :
    Syn β :=
  match x with
  | .TempSyn rep => .TempSyn rep

def Syn.undefined
      {α : Type} [c : Synth α] : Syn α :=
  let xs := c.width.fold (fun _  _ s => s ++ "x") ""
  .TempSyn (s!"{c.width}'d" ++ xs)


structure Bits (n : Nat) : Type where
  bits : Vector Bool n

-- Bits is synthesizable
instance (n : Nat) : Synth (Bits n) where
  width := n
  synth (b : Bits n) :=
    let bin := b.bits.map fun
        | true  => "1"
        | false => "0"
    .TempSyn (bin.foldl String.append s!"{n}'b")

def Syn.slice
      {α : Type} [c : Synth α] (x : Syn α)
      (l r : Nat)
      (_ : l < c.width ∧ l ≥ r := by simp [SynthWidth.width]) :
    Syn (Bits (l - r + 1)) :=
  match x with
  | .TempSyn rep => .TempSyn (rep.append s!"[{l}:{r}]")

example :
    (Syn.TempSyn "8'b01001000" : Syn (Bits 8)).slice 5 3 =
    .TempSyn "8'b01001000[5:3]" := by
  simp!
  simp [Nat.repr, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, List.asString]

instance {α β : Type} [cα : Synth α] [cβ : Synth β] :
    HAppend (Syn α) (Syn β) (Syn (Bits (cα.width + cβ.width))) where
  hAppend := fun
  | .TempSyn a, .TempSyn b => .TempSyn ("{" ++ s!"{a},{b}" ++ "}")


class SynthEnum (α : Type) extends Synth α where
  -- TODO

class SynthInduct (τ : outParam Type) [SynthEnum τ] (α : Type) extends Synth α where
  inductType : τ → (ρ : Type) → Type
  synWrap : (ε : τ) → inductType ε α
  synUnwrap : {ρ : Type} → Syn α → ((ε : τ) → inductType ε ρ) → Syn ρ



-- Prototype
inductive Foo : Type where
| Foo1 : Bits 8 → Foo
| Foo2 : Bits 3 → Bits 6 → Foo

-- The following should be auto-generated
inductive FooEnum : Type where
| Foo1 : FooEnum
| Foo2 : FooEnum



instance : SynthEnum FooEnum where
  width := 1
  synth := fun
  | .Foo1 => .TempSyn "1'b0"
  | .Foo2 => .TempSyn "1'b1"
  -- TODO: SynthEnum methods

instance [c : SynthEnum FooEnum] : SynthInduct FooEnum Foo where
  width := 10
  synth := fun
  | .Foo1 (x : Bits 8) =>
    let synth_x [cx : Synth (Bits 8)] : Syn (Bits 8) := cx.synth x
    (c.synth .Foo1 ++ synth_x ++ (Syn.undefined : Syn (Bits 1))).coerce
  | .Foo2 x y => _

  inductType ε ρ := match ε with
  | .Foo1 => Syn (Bits 8) → Syn ρ
  | .Foo2 => Syn (Bits 3) → Syn (Bits 6) → Syn ρ

  synWrap ε := match ε with
  | .Foo1 => fun _   => .Todo
  | .Foo2 => fun _ _ => .Todo

  synUnwrap x _ := match x with
  | .Todo => .Todo
