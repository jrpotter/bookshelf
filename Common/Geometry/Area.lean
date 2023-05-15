import Common.Geometry.Basic
import Common.Geometry.Rectangle.Orthogonal
import Common.Geometry.StepFunction

/-! # Common.Geometry.Area

An axiomatic foundation for the concept of *area*. These axioms are those
outlined in [^1].

[^1]: Apostol, Tom M. Calculus, Vol. 1: One-Variable Calculus, with an
      Introduction to Linear Algebra. 2nd ed. Vol. 1. 2 vols. Wiley, 1991.
-/

namespace Geometry.Area

/--
All *measurable sets*, i.e. sets in the plane to which an area can be assigned.

The existence of such a class is assumed in the axiomatic definition of area
introduced by Apostol. He denotes this set of sets as `𝓜`.
-/
axiom 𝓜 : Set (Set Point)

/--
A set function mapping every *measurable set* to a value denoting its area.

The existence of such a function is assumed in the axiomatic definition of area
introduced by Apostol. He denotes this function as `a`.
-/
axiom area : ∀ ⦃x⦄, x ∈ 𝓜 → ℝ

/-! ## Nonnegative Property

For each set `S` in `𝓜`, we have `a(S) ≥ 0`.
-/

axiom area_ge_zero {S : Set Point} (h : S ∈ 𝓜): area h ≥ 0

/-! ## Additive Property

If `S` and `T` are in `𝓜`, then `S ∪ T` in `𝓜`, `S ∩ T` in `𝓜`, and
`a(S ∪ T) = a(S) + a(T) - a(S ∩ T)`.
-/

axiom measureable_imp_union_measurable {S T : Set Point}
  (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) : S ∪ T ∈ 𝓜

axiom measurable_imp_inter_measurable {S T : Set Point}
  (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) : S ∩ T ∈ 𝓜

axiom union_area_eq_area_add_area_sub_inter_area
  {S T : Set Point} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜)
  : area (measureable_imp_union_measurable hS hT) =
      area hS + area hT - area (measurable_imp_inter_measurable hS hT)

/-! ## Difference Property

If `S` and `T` are in `𝓜` with `S ⊆ T`, then `T - S` is in `𝓜` and
`a(T - S) = a(T) - a(S)`.
-/

axiom measureable_imp_diff_measurable
  {S T : Set Point} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) (h : S ⊆ T)
  : T \ S ∈ 𝓜

axiom diff_area_eq_area_sub_area
  {S T : Set Point} (hS : S ∈ 𝓜) (hT : T ∈ 𝓜) (h : S ⊆ T)
  : area (measureable_imp_diff_measurable hS hT h) = area hT - area hS

/-! ## Invariance Under Congruence

If a set `S` is in `𝓜` and if a set `T` is congruent to `S`, then `T` is also in
`𝓜` and `a(S) = a(T)`.
-/

axiom measurable_congruent_imp_measurable
  {S T : Set Point} (hS : S ∈ 𝓜) (h : congruent S T)
  : T ∈ 𝓜

axiom congruent_imp_area_eq_area
  {S T : Set Point} (hS : S ∈ 𝓜) (h : congruent S T)
  : area hS = area (measurable_congruent_imp_measurable hS h)

/-! ## Choice of Scale

(i) Every rectangle `R` is in `𝓜`.

(ii) If the edges of rectangle `R` have lengths `h` and `k`, then `a(R) = hk`.
-/

axiom rectangle_measurable (R : Rectangle.Skew)
  : R.toSet ∈ 𝓜

axiom rectangle_area_eq_mul_edge_lengths (R : Rectangle.Skew)
  : area (rectangle_measurable R) = R.width * R.height

/-! ## Exhaustion Property

Let `Q` be a set that can be enclosed between two step regions `S` and `T`, so
that (1.1) `S ⊆ Q ⊆ T`. If there is one and only one number `k` which satisfies
the inequalities `a(S) ≤ k ≤ a(T)` for all step regions `S` and `T` satisfying
(1.1), then `Q` is measurable and `a(Q) = k`.
-/

/--
Every step region is measurable. This follows from the choice of scale axiom,
and the fact all step regions are equivalent to the union of a collection of
rectangles.
-/
theorem step_function_measurable (S : StepFunction)
  : S.toSet ∈ 𝓜 := by
  sorry

def forallSubsetsBetween (k : ℝ) (Q : Set Point) :=
  ∀ S T : StepFunction,
  (hS : S.toSet ⊆ Q) →
  (hT : Q ⊆ T.toSet) →
  area (step_function_measurable S) ≤ k ∧ k ≤ area (step_function_measurable T)

axiom exhaustion_exists_unique_imp_measurable (Q : Set Point)
  : (∃! k : ℝ, forallSubsetsBetween k Q)
  → Q ∈ 𝓜

axiom exhaustion_exists_unique_imp_area_eq (Q : Set Point)
  : ∃ k : ℝ,
      (h : forallSubsetsBetween k Q ∧
        (∀ x : ℝ, forallSubsetsBetween x Q → x = k))
    → area (exhaustion_exists_unique_imp_measurable Q ⟨k, h⟩) = k

end Geometry.Area