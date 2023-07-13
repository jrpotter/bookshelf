import Mathlib.Init.Algebra.Classes

/-! # Common.Algebra.Classes

Additional theorems and definitions useful in the context of algebraic classes.
-/

/--
`IsConnected X lt` means that the binary relation `lt` on `X` is connected, that
is, either `lt a b` or `lt b a` for any distinct `a` and `b`.
-/
class IsConnected (α : Type u) (lt : α → α → Prop) : Prop where
  connected : ∀ a b, a ≠ b → lt a b ∨ lt b a