import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

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
  maps_to : Set.MapsTo S N N
  mem : e ∈ N
  zero_range : e ∉ Set.range S
  injective : Function.Injective S
  induction : ∀ A, A ⊆ N ∧ e ∈ A ∧ (∀ a ∈ A, S a ∈ A) → A = N

instance : System (N := @Set.univ ℕ) (S := Nat.succ) (e := 0) where
  maps_to := by simp
  mem := by simp
  zero_range := by simp
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

/--
The unique (by virtue of the Recursion Theorem for `ω`) function that maps the
natural numbers to an arbitrary Peano system.
-/
def of_nat {e : α} [h : System N S e] : Nat → α
  | 0 => e
  | n + 1 => S (@of_nat _ _ _ _ h n)

/--
The `of_nat` function maps all natural numbers to the set `N` defined in the
provided Peano system.
-/
theorem nat_maps_to [h : System N S e]
  : Set.MapsTo (@of_nat _ _ _ _ h) Set.univ N := by
  unfold Set.MapsTo
  intro x hx
  unfold of_nat
  induction x with
  | zero => exact h.mem
  | succ x ih =>
    simp only
    by_cases hx' : x = 0
    · rw [hx']
      unfold of_nat
      exact h.maps_to h.mem
    · have ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hx'
      rw [hp] at ih ⊢
      simp only [Set.mem_univ, forall_true_left] at ih
      exact h.maps_to ih

/--
Let `⟨N, S, e⟩` be a Peano system. Then `⟨ω, σ, 0⟩` is isomorphic to
`⟨N, S, e⟩`, i.e., there is a function `h` mapping `ω` one-to-one onto `N` in a
way that preserves the successor operation
```
h(σ(n)) = S(h(n))
```
and the zero element
```
h(0) = e.
```
-/
theorem nat_isomorphism [h : System N S e]
  : let n2p := @of_nat _ _ _ _ h
    Set.BijOn n2p Set.univ N ∧
      (∀ n : ℕ, n2p n.succ = S (n2p n)) ∧ n2p 0 = e := by
  let n2p := @of_nat _ _ _ _ h
  refine ⟨⟨nat_maps_to, ?_, ?_⟩, ?_, rfl⟩
  · -- Prove `of_nat` is one-to-one.
    suffices ∀ n : ℕ, ∀ m, n2p m = n2p n → m = n by
      unfold Set.InjOn
      intro m _ n _
      exact this n m
    intro n
    induction n with
    | zero =>
      intro m hm
      by_contra nm
      have ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero nm
      rw [hp] at hm
      unfold of_nat at hm
      exact absurd ⟨n2p p, hm⟩ h.zero_range
    | succ n ih =>
      intro m hm
      by_cases nm : m = 0
      · rw [nm] at hm
        unfold of_nat at hm
        exact absurd ⟨n2p n, hm.symm⟩ h.zero_range
      · have ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero nm
        rw [hp] at hm
        unfold of_nat at hm
        have := h.injective hm
        rwa [← ih p this]
  · -- Prove `of_nat` is onto.
    suffices e ∈ Set.range n2p ∧ (∀ y, y ∈ Set.range n2p → S y ∈ Set.range n2p) by
      unfold Set.SurjOn
      simp only [Set.image_univ]
      have hN : Set.range n2p = N := by
        refine h.induction (Set.range n2p) ⟨?_, this⟩
        show ∀ t, t ∈ Set.range n2p → t ∈ N
        intro t ht
        unfold Set.range at ht
        simp only [Set.mem_setOf_eq] at ht
        have ⟨y, hy⟩ := ht
        rw [← hy]
        exact nat_maps_to (by simp)
      exact Eq.subset (id (Eq.symm hN))
    refine ⟨?_, ?_⟩
    · unfold Set.range
      simp only [Set.mem_setOf_eq]
      exact ⟨0, rfl⟩
    · intro y hy
      have ⟨n, hn⟩ := hy
      refine ⟨n + 1, ?_⟩
      unfold of_nat
      simp only [Nat.add_eq, Nat.add_zero]
      dsimp only at hn
      rw [hn]
  · intro _
    conv => left; unfold of_nat

end Peano