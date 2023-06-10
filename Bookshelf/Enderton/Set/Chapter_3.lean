import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.ZFC.Basic

import Common.Set.Basic
import Common.Set.OrderedPair

/-! # Enderton.Chapter_3

Relations and Functions
-/

namespace Enderton.Set.Chapter_3

/--
If `x ∈ C` and `y ∈ C`, then `⟨x, y⟩ ∈ 𝒫 𝒫 C`.
-/
theorem theorem_3b {C : Set α} (hx : x ∈ C) (hy : y ∈ C)
  : Set.OrderedPair x y ∈ 𝒫 𝒫 C := by
  have hxs : {x} ⊆ C := Set.singleton_subset_iff.mpr hx
  have hxys : {x, y} ⊆ C := Set.mem_mem_imp_pair_subset hx hy
  exact Set.mem_mem_imp_pair_subset hxs hxys

/-- ### Exercise 5.1

Suppose that we attempted to generalize the Kuratowski definitions of ordered
pairs to ordered triples by defining
```
⟨x, y, z⟩* = {{x}, {x, y}, {x, y, z}}.
```
Show that this definition is unsuccessful by giving examples of objects `u`,
`v`, `w`, `x`, `y`, `z` with `⟨x, y, z⟩* = ⟨u, v, w⟩*` but with either `y ≠ v`
or `z ≠ w` (or both).
-/
theorem exercise_5_1 {x y z u v w : ℕ}
  (hx : x = 1) (hy : y = 1) (hz : z = 2)
  (hu : u = 1) (hv : v = 2) (hw : w = 2)
  : ({{x}, {x, y}, {x, y, z}} : Set (Set ℕ)) = {{u}, {u, v}, {u, v, w}}
  ∧ y ≠ v := by
  apply And.intro
  · rw [hx, hy, hz, hu, hv, hw]
    simp
  · rw [hy, hv]
    simp only

/-- ### Exercise 5.2a

Show that `A × (B ∪ C) = (A × B) ∪ (A × C)`.
-/
theorem exercise_5_2a {A B C : Set α}
  : Set.prod A (B ∪ C) = (Set.prod A B) ∪ (Set.prod A C) := by
  calc Set.prod A (B ∪ C)
    _ = { p | p.1 ∈ A ∧ p.2 ∈ B ∪ C } := rfl
    _ = { p | p.1 ∈ A ∧ (p.2 ∈ B ∨ p.2 ∈ C) } := rfl
    _ = { p | (p.1 ∈ A ∧ p.2 ∈ B) ∨ (p.1 ∈ A ∧ p.2 ∈ C) } := by
      ext x
      rw [Set.mem_setOf_eq]
      conv => lhs; rw [and_or_left]
    _ = { p | p ∈ Set.prod A B ∨ (p ∈ Set.prod A C) } := rfl
    _ = (Set.prod A B) ∪ (Set.prod A C) := rfl

/-- ### Exercise 5.2b

Show that if `A × B = A × C` and `A ≠ ∅`, then `B = C`.
-/
theorem exercise_5_2b {A B C : Set α}
  (h : Set.prod A B = Set.prod A C) (hA : Set.Nonempty A)
  : B = C := by
  by_cases hB : Set.Nonempty B
  · suffices B ⊆ C ∧ C ⊆ B from Set.Subset.antisymm_iff.mpr this
    have ⟨a, ha⟩ := hA
    apply And.intro
    · show ∀ t, t ∈ B → t ∈ C
      intro t ht
      have : (a, t) ∈ Set.prod A B := ⟨ha, ht⟩
      rw [h] at this
      exact this.right
    · show ∀ t, t ∈ C → t ∈ B
      intro t ht
      have : (a, t) ∈ Set.prod A C := ⟨ha, ht⟩
      rw [← h] at this
      exact this.right
  · have nB : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    rw [nB, Set.prod_right_emptyset_eq_emptyset, Set.ext_iff] at h
    rw [nB]
    by_contra nC
    have ⟨a, ha⟩ := hA
    have ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr (Ne.symm nC)
    exact (h (a, c)).mpr ⟨ha, hc⟩

end Enderton.Set.Chapter_3