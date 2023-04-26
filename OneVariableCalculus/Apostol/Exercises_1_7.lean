/-
Exercises 1.7
-/
import OneVariableCalculus.Real.Geometry.Area
import OneVariableCalculus.Real.Geometry.Rectangle

open Real
open Real.Geometry.Area

-- ========================================
-- The properties of area in this set of exercises are to be deduced from the
-- axioms for area stated in the foregoing section.
-- ========================================

-- ----------------------------------------
-- Exercise 1
--
-- Prove that each of the following sets is measurable and has zero area:
-- (a) A set consisting of a single point.
-- (b) A set consisting of a finite number of points in a plane.
-- (c) The union of a finite collection of line segments in a plane.
-- ----------------------------------------

example (p : Point)
  : p.set_def ∈ 𝓜
  ∧ ((h : p.set_def ∈ 𝓜) → area h = 0) :=
  sorry

example (S : Set Point) (hf : Set.Finite S)
  : (⋃ p ∈ S, p.set_def) ∈ 𝓜
  ∧ ((h : (⋃ p ∈ S, p.set_def) ∈ 𝓜) → area h = 0) :=
  sorry

example (S : Set LineSegment) (hf : Set.Finite S)
  : (⋃ s ∈ S, s.set_def) ∈ 𝓜
  ∧ ((h : (⋃ s ∈ S, s.set_def) ∈ 𝓜) → area h = 0) :=
  sorry

-- ----------------------------------------
-- Exercise 2
--
-- Every right triangular region is measurable because it can be obtained as the
-- intersection of two rectangles. Prove that every triangular region is
-- measurable and that its area is one half the product of its base and
-- altitude.
-- ----------------------------------------

-- # TODO

-- ----------------------------------------
-- Exercise 3
--
-- Prove that every trapezoid and every parallelogram is measurable and derive
-- the usual formulas for their areas.
-- ----------------------------------------

-- # TODO

-- ----------------------------------------
-- Exercise 4
--
-- A point `(x, y)` in the plane is called a *lattice point* if both coordinates
-- `x` and `y` are integers. Let `P` be a polygon whose vertices are lattice
-- points inside the polygon and `B` denotes the number on the boundary.
--
-- (a) Prove that the formula is valid for rectangles with sides parallel to the
-- coordinate axes.
-- (b) Prove that the formula is valid for right triangles and parallelograms.
-- (c) Use induction on the number of edges to construct a proof for general
-- polygons.
-- ----------------------------------------

-- # TODO

-- ----------------------------------------
-- Exercise 5
--
-- Prove that a triangle whose vertices are lattice points cannot be
-- equilateral.
--
-- [Hint: Assume there is such a triangle and compute its area in two ways,
-- using exercises 2 and 4.]
-- ----------------------------------------

-- # TODO

-- ----------------------------------------
-- Exercise 6
--
-- Let `A = {1, 2, 3, 4, 5}`, and let `𝓜` denote the class of all subsets of
-- `A`. (There are `32` altogether, counting `A` itself and the empty set `∅`.)
-- For each set `S` in `𝓜`, let `n(S)` denote the number of distinct elements in
-- `S`. If `S = {1, 2, 3, 4}` and `T = {3, 4, 5}`, compute `n(S ∪ T)`,
-- `n(S ∩ T)`, `n(S - T)`, and `n(T - S)`. Prove that the set function `n`
-- satisfies the first three axioms for area.
-- ----------------------------------------

-- # TODO
