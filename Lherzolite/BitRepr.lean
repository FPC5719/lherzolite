class BitRepr (α : Type u) where
  width : ℕ
  toBV : α → BitVec width
  fromBV : BitVec width → α
  to_from_id : ∀ (bv : BitVec width), toBV (fromBV bv) = bv
  from_to_id : ∀ (x : α), fromBV (toBV x) = x
