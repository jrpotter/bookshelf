import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic

/-! # Common.Set.Peano

Data types and theorems used to define Peano systems.
-/

namespace Peano

/--
A `Peano system` is a triple `⟨N, S, e⟩` consisting of a set `N`, a function
`S : N → N`, and a member `e ∈ N` such that the following three conditions are
met:

1. `e ∉ ran S`.
2. `S` is one-to-one.
3. Every subset `A` of `N` containing `e` and closed under `S` is `N` itself.
-/
class System (N : Set α) (S : α → α) (e : α) where
  zero_range : e ∉ Set.range S
  injective : Function.Injective S
  induction : ∀ A, A ⊆ N ∧ e ∈ A ∧ (∀ a ∈ A, S a ∈ A) → A = N

instance : System (N := @Set.univ ℕ) (S := Nat.succ) (e := 0) where
  zero_range := by
    simp
  injective := by
    intro x₁ x₂ h
    injection h
  induction := by
    intro A h
    suffices Set.univ ⊆ A from Set.Subset.antisymm h.left this
    show ∀ n, n ∈ Set.univ → n ∈ A
    intro n hn
    induction n with
    | zero => exact h.right.left
    | succ n ih =>
      refine h.right.right n (ih ?_)
      simp

end Peano