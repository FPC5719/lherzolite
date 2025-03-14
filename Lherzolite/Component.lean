inductive Binding : Type where
  | Input
  | Output
  | Wire
  | Reg


inductive Component : Type → Type 2 where
  | Pure   : α → Component α
  | Bind   : Component α → (α → Component β) → Component β
  | Input  : String → Type → Component Binding
  | Output : String → Type → Component Binding
  | Assign : (dst : Binding) → (src : Binding) → Component Unit

instance : Monad Component where
  pure := .Pure
  bind := .Bind

example : Component Unit := do
  let a ← .Input "A" Bool
  let b ← .Output "B" Bool
  .Assign b a
  pure ()
