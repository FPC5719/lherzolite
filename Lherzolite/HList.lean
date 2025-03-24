inductive HList : List (Type u) → Type (u + 1) where
| nil  : HList []
| cons : t → HList ts → HList (t :: ts)
