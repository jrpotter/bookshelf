import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Intervals.Basic

import Common.List.Basic

/-! # Common.Set.Intervals.Partition

Additional theorems and definitions useful in the context of sets.
-/

namespace Set.Intervals

open List

/--
A `Partition` is a finite subset of `[a, b]` containing points `a` and `b`.
-/
structure Partition (α : Type _) [Preorder α] [@DecidableRel α LT.lt] where
  /- The left-most endpoint of the partition. -/
  a : α
  /- The right-most endpoint of the partition. -/
  b : α
  /- The subdivision points. -/
  xs : List α
  /- Ensure the subdivision points are in sorted order. -/
  sorted_xs : Sorted LT.lt xs
  /- Ensure each subdivision point is in our defined interval. -/
  within_xs : ∀ x ∈ xs, x ∈ Ioo a b

namespace Partition

/--
An object `x` is a member of a `Partition` `p` if `x` is an endpoint of `p` or a
subdivision point of `p`.

Notice that being a member of `p` is different from being a member of some
(sub)interval determined by `p`.
-/
instance [Preorder α] [@DecidableRel α LT.lt] : Membership α (Partition α) where
  mem (x : α) (p : Partition α) := x = p.a ∨ x ∈ p.xs ∨ x = p.b

/--
Return the endpoints and subdivision points of a `Partition` as a sorted `List`.
-/
def toList [Preorder α] [@DecidableRel α LT.lt] (p : Partition α) : List α :=
  (p.a :: p.xs) ++ [p.b]

/--
`x` is a member of `Partition` `p` **iff** `x` is a member of `p.List`.
-/
theorem mem_self_iff_mem_toList [Preorder α] [@DecidableRel α LT.lt]
  (p : Partition α) : x ∈ p ↔ x ∈ p.toList := by
  apply Iff.intro
  · sorry
  · sorry

/--
Every member of a `Partition` is greater than or equal to its left-most point.
-/
theorem left_le_mem_self [Preorder α] [@DecidableRel α LT.lt]
  (p : Partition α) : ∀ x ∈ p, p.a ≤ x := by
  sorry

/--
Every member of a `Partition` is less than or equal to its right-most point.
-/
theorem right_ge_mem_self [Preorder α] [@DecidableRel α LT.lt]
  (p : Partition α) : ∀ x ∈ p, x ≤ p.b := by
  sorry

/-
Return the closed subintervals determined by the `Partition`.
-/
def closedSubintervals [Preorder α] [@DecidableRel α LT.lt]
  (p : Partition α) : List (Set α) :=
  p.toList.pairwise (fun x₁ x₂ => Icc x₁ x₂)

/-
Return the open subintervals determined by the `Partition`.
-/
def openSubintervals [Preorder α] [@DecidableRel α LT.lt]
  (p : Partition α) : List (Set α) :=
  p.toList.pairwise (fun x₁ x₂ => Ioo x₁ x₂)

/--
A member of an open subinterval of a `Partition` `p` is a member of the entire
open interval determined by `p`.
-/
theorem mem_open_subinterval_mem_open_interval
  [Preorder α] [@DecidableRel α LT.lt] {p : Partition α}
  (hI : I ∈ p.openSubintervals) (hy : y ∈ I) : y ∈ Ioo p.a p.b := by
  have ⟨i, ⟨x₁, ⟨x₂, ⟨hx₁, ⟨hx₂, hI'⟩⟩⟩⟩⟩ :=
    List.mem_pairwise_imp_exists_adjacent hI
  have hx₁' : p.a ≤ x₁ := by
    refine p.left_le_mem_self x₁ ?_
    rw [p.mem_self_iff_mem_toList]
    have : ↑i < p.toList.length := calc ↑i
      _ < p.toList.length - 1 := i.2
      _ < p.toList.length := by
        unfold List.length Partition.toList
        simp
    exact List.mem_iff_exists_get.mpr ⟨⟨↑i, this⟩, Eq.symm hx₁⟩
  have hx₂' : x₂ ≤ p.b := by
    refine p.right_ge_mem_self x₂ ?_
    rw [p.mem_self_iff_mem_toList]
    have : ↑i + 1 < p.toList.length := add_lt_add_right i.2 1
    exact List.mem_iff_exists_get.mpr ⟨⟨↑i + 1, this⟩, Eq.symm hx₂⟩
  have hx_sub := Set.Ioo_subset_Ioo hx₁' hx₂'
  rw [hI'] at hy
  exact Set.mem_of_subset_of_mem hx_sub hy

/--
A member of an open subinterval of a `Partition` `p` is a member of the entire
closed interval determined by `p`.
-/
theorem mem_open_subinterval_mem_closed_interval
  [Preorder α] [@DecidableRel α LT.lt] {p : Partition α}
  (hI : I ∈ p.openSubintervals) (hy : y ∈ I) : y ∈ Icc p.a p.b := by
  have := mem_open_subinterval_mem_open_interval hI hy
  exact Set.mem_of_subset_of_mem Set.Ioo_subset_Icc_self this

end Partition

end Set.Intervals