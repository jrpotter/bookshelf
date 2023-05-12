import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sort

import Common.List.Basic
import Common.Real.Basic

/-! # Common.Real.Geometry.StepFunction

A characterization of constructs surrounding step functions.
-/

namespace Real

open List

/-! ## Partition -/

/--
A `Partition` is some finite subset of `[a, b]` containing points `a` and `b`.

It is assumed that the points of the `Partition` are distinct and sorted. The
use of a `List` ensures finite-ness.
-/
structure Partition where
  xs : List ℝ
  sorted : Sorted LT.lt xs
  has_min_length : xs.length ≥ 2

namespace Partition

/--
The length of any list associated with a `Partition` is `> 0`.
-/
private lemma length_gt_zero (p : Partition) : p.xs.length > 0 :=
  calc p.xs.length
    _ ≥ 2 := p.has_min_length
    _ > 0 := by simp

/--
The length of any list associated with a `Partition` is `≠ 0`.
-/
instance (p : Partition) : NeZero (length p.xs) where
  out := LT.lt.ne' (length_gt_zero p)

/--
The left-most subdivision point of the `Partition`.
-/
def left (p : Partition) : ℝ :=
  p.xs.head (neq_nil_iff_length_gt_zero.mpr (length_gt_zero p))

/--
The right-most subdivision point of the `Partition`.
-/
def right (p : Partition) : ℝ :=
  p.xs.getLast (neq_nil_iff_length_gt_zero.mpr (length_gt_zero p))

/--
Define `∈` syntax for a `Partition`. We say a real is a member of a partition
provided it lies somewhere in closed interval `[a, b]`.
-/
instance : Membership ℝ Partition where
  mem (x : ℝ) (p : Partition) := p.left ≤ x ∧ x ≤ p.right

/--
Every subdivision point is `≥` the left-most point of the partition.
-/
theorem subdivision_point_geq_left {p : Partition} (h : x ∈ p.xs)
  : p.left ≤ x := by
  unfold left
  rw [head_eq_get_zero (exists_mem_iff_neq_nil.mp ⟨x, h⟩)]
  have ⟨i, hi⟩ := mem_iff_exists_get.mp h
  conv => rhs; rw [← hi]
  by_cases hz : i = (0 : Fin (length p.xs))
  · rw [hz]
    simp
  · refine le_of_lt (Sorted.rel_get_of_lt p.sorted ?_)
    rwa [← ne_eq, ← Fin.pos_iff_ne_zero i] at hz

/--
Every subdivision point is `≤` the right-most point of the partition.
-/
theorem subdivision_point_leq_right {p : Partition} (h : x ∈ p.xs)
  : x ≤ p.right := by
  unfold right
  have hx := exists_mem_iff_neq_nil.mp ⟨x, h⟩
  rw [getLast_eq_get_length_sub_one hx]
  have ⟨i, hi⟩ := mem_iff_exists_get.mp h
  conv => lhs; rw [← hi]
  have ⟨_, ⟨_, hs⟩⟩ := self_neq_nil_imp_exists_mem.mp hx
  by_cases hz : i = ⟨p.xs.length - 1, by rw [hs]; simp⟩
  · rw [hz]
  · refine le_of_lt (Sorted.rel_get_of_lt p.sorted ?_)
    rw [← ne_eq, Fin.ne_iff_vne] at hz
    rw [Fin.lt_iff_val_lt_val]
    exact lt_of_le_of_ne (le_tsub_of_add_le_right i.2) hz

/--
Every subdivision point of a `Partition` is itself a member of the `Partition`.
-/
theorem subdivision_point_mem_partition {p : Partition} (h : x ∈ p.xs)
  : x ∈ p := ⟨subdivision_point_geq_left h, subdivision_point_leq_right h⟩

end Partition

/-! ## Step Functions -/

/--
Any member of a subinterval of a partition `P` must also be a member of `P`.
-/
lemma mem_open_subinterval_imp_mem_partition {p : Partition}
  (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => Set.Ioo x₁ x₂))
  (hy : y ∈ I) : y ∈ p := by
  cases h : p.xs with
  | nil =>
    -- By definition, a partition must always have at least two points in the
    -- interval. Discharge the empty case.
    rw [h] at hI
    cases hI
  | cons x ys =>
    have ⟨i, x₁, ⟨x₂, ⟨hx₁, ⟨hx₂, hI'⟩⟩⟩⟩ :=
      List.mem_pairwise_imp_exists_adjacent hI
    have hx₁ : x₁ ∈ p.xs := by
      rw [hx₁]
      let j : Fin (List.length p.xs) := ⟨i.1, Nat.lt_of_lt_pred i.2⟩
      exact List.mem_iff_exists_get.mpr ⟨j, rfl⟩
    have hx₂ : x₂ ∈ p.xs := by
      rw [hx₂]
      let j : Fin (List.length p.xs) := ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩
      exact List.mem_iff_exists_get.mpr ⟨j, rfl⟩
    rw [hI'] at hy
    apply And.intro
    · calc p.left
        _ ≤ x₁ := (Partition.subdivision_point_mem_partition hx₁).left
        _ ≤ y := le_of_lt hy.left
    · calc y
        _ ≤ x₂ := le_of_lt hy.right
        _ ≤ p.right := (Partition.subdivision_point_mem_partition hx₂).right

/--
A function `f` is a `StepFunction` if there exists a `Partition` `p` such that
`f` is constant on every open subinterval of `p`.
-/
structure StepFunction where
  p : Partition
  f : ∀ x ∈ p, ℝ
  const_open_subintervals :
    ∀ (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => Set.Ioo x₁ x₂)),
      ∃ c : ℝ, ∀ (hy : y ∈ I),
        f y (mem_open_subinterval_imp_mem_partition hI hy) = c

namespace StepFunction

/--
The set definition of a `StepFunction` is the region between the constant values
of the function's subintervals and the real axis.
-/
def toSet (f : StepFunction) : Set ℝ² := sorry

end StepFunction

end Real