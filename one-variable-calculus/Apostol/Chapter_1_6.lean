/-
Chapter 1.6

The concept of area as a set function
-/
import Bookshelf.Real.Function.Step
import Bookshelf.Real.Geometry.Rectangle

namespace Real

/--
All *measurable sets*, i.e. sets in the plane to which an area can be assigned.

The existence of such a class is assumed in the axiomatic definition of area
introduced by Apostol. He denotes this set of sets as `𝓜`.
-/
axiom 𝓜 : Set (Set ℝ²)

/--
A set function mapping every *measurable set* to a value denoting its area.

The existence of such a function is assumed in the axiomatic definition of area
introduced by Apostol. He denotes this function as `a`.
-/
axiom area : ∀ ⦃x⦄, x ∈ 𝓜 → ℝ

/--
The nonnegative property.

For each set `S` in `𝓜`, we have `a(S) ≥ 0`.
-/
axiom area_ge_zero {S : Set ℝ²} (h : S ∈ 𝓜): area h ≥ 0

/--
The additive property (i).

If `S` and `T` are in `𝓜`, then `S ∪ T` in `𝓜`.
-/
axiom measureable_imp_union_measurable {S T : Set ℝ²} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜)
  : S ∪ T ∈ 𝓜

/--
The additive property (ii).

If `S` and `T` are in `𝓜`, then `S ∩ T` in `𝓜`.
-/
axiom measurable_imp_inter_measurable {S T : Set ℝ²} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜)
  : S ∩ T ∈ 𝓜

/--
The additive property (iii).

If `S` and `T` are in `𝓜`, then `a(S ∪ T) = a(S) + a(T) - a(S ∩ T)`.
-/
axiom union_area_eq_area_add_area_sub_inter_area
  {S T : Set ℝ²} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜)
  : area (measureable_imp_union_measurable hS hT) =
      area hS + area hT - area (measurable_imp_inter_measurable hS hT)

/--
The difference property (i).

If `S` and `T` are in `𝓜` with `S ⊆ T`, then `T - S` is in `𝓜`.
-/
axiom measureable_imp_diff_measurable
  {S T : Set ℝ²} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) (h : S ⊆ T)
  : T \ S ∈ 𝓜

/--
The difference property (ii).

If `S` and `T` are in `𝓜` with `S ⊆ T`, then `a(T - S) = a(T) - a(S)`.
-/
axiom diff_area_eq_area_sub_area
  {S T : Set ℝ²} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) (h : S ⊆ T)
  : area (measureable_imp_diff_measurable hS hT h) = area hT - area hS

/--
Invariance under congruence (i).

If a set `S` is in `𝓜` and if `T` is congruent to `S`, then `T` is also in `𝓜`..
-/
axiom measurable_congruent_imp_measurable
  {S T : Set ℝ²} (hS : S ∈ 𝓜) (h : congruent S T)
  : T ∈ 𝓜

/--
Invariance under congruence (ii).

If a set `S` is in `𝓜` and if `T` is congruent to `S`, then `a(S) = a(T)`.
-/
axiom congruent_imp_area_eq_area
  {S T : Set ℝ²} (hS : S ∈ 𝓜) (h : congruent S T)
  : area hS = area (measurable_congruent_imp_measurable hS h)

/--
Choice of scale (i).

Every rectangle `R` is in `𝓜`.
-/
axiom rectangle_measurable (R : Rectangle)
  : R.set_def ∈ 𝓜

/--
Choice of scale (ii).

If the edges of rectangle `R` have lengths `h` and `k`, then `a(R) = hk`.
-/
axiom rectangle_area_eq_mul_edge_lengths (R : Rectangle)
  : area (rectangle_measurable R) = R.width * R.height

/--
Every step region is measurable. This follows from the choice of scale axiom,
and the fact all step regions are equivalent to the union of a collection of
rectangles.
-/
theorem step_function_measurable (S : Function.Step) : S.set_def ∈ 𝓜 := by
  sorry

/--
Exhaustion property.

Let `Q` be a set that can be enclosed between two step regions `S` and `T`, so
that (1.1) `S ⊆ Q ⊆ T`. If there is one and only one number `k` which satisfies
the inequalities `a(S) ≤ k ≤ a(T)` for all step regions `S` and `T` satisfying
(1.1), then `Q` is measurable and `a(Q) = k`.
-/
def forall_subset_between_step_imp_le_between_area (k : ℝ) (Q : Set ℝ²) :=
  ∀ S T : Function.Step,
    (hS : S.set_def ⊆ Q) →
    (hT : Q ⊆ T.set_def) →
    area (step_function_measurable S) ≤ k ∧ k ≤ area (step_function_measurable T)

/--
Exhaustion property (i).

If there exists some `k` satisfying the description in the above `def`, then `Q`
is measurable.
-/
axiom exhaustion_exists_unique_imp_measurable (Q : Set ℝ²)
  : (∃ k : ℝ, forall_subset_between_step_imp_le_between_area k Q ∧
      (∀ x : ℝ, forall_subset_between_step_imp_le_between_area x Q → x = k))
  → Q ∈ 𝓜

/--
Exhaustion property (ii).

If there exists some `k` satisfying the description in the above `def`, then `Q`
satisfies `a(Q) = k`.
-/
axiom exhaustion_exists_unique_imp_area_eq (Q : Set ℝ²)
  : ∃ k : ℝ,
      (h : forall_subset_between_step_imp_le_between_area k Q ∧
        (∀ x : ℝ, forall_subset_between_step_imp_le_between_area x Q → x = k))
  → area (exhaustion_exists_unique_imp_measurable Q ⟨k, h⟩) = k

end Real
