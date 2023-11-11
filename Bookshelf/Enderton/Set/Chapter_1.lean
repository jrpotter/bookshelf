import Mathlib.Data.Set.Basic

/-! # Enderton.Set.Chapter_1

Introduction
-/

namespace Enderton.Set.Chapter_1

/-! ### Exercise 1.1

Which of the following become true when "∈" is inserted in place of the blank?
Which become true when "⊆" is inserted?
-/

/--
The `∅` does not equal the singleton set containing `∅`.
-/
lemma empty_ne_singleton_empty (h : ∅ = ({∅} : Set (Set α))) : False :=
  absurd h (Ne.symm $ Set.singleton_ne_empty (∅ : Set α))

/-- #### Exercise 1.1a

`{∅} ___ {∅, {∅}}`
-/
theorem exercise_1_1a
  : {∅} ∈ ({∅, {∅}} : Set (Set (Set α)))
  ∧ {∅} ⊆ ({∅, {∅}} : Set (Set (Set α))) := ⟨by simp, by simp⟩

/-- #### Exercise 1.1b

`{∅} ___ {∅, {{∅}}}`
-/
theorem exercise_1_1b
  : {∅} ∉ ({∅, {{∅}}}: Set (Set (Set (Set α))))
  ∧ {∅} ⊆ ({∅, {{∅}}}: Set (Set (Set (Set α)))) := by
  refine ⟨?_, by simp⟩
  intro h
  simp at h
  exact empty_ne_singleton_empty h

/-- #### Exercise 1.1c

`{{∅}} ___ {∅, {∅}}`
-/
theorem exercise_1_1c
  : {{∅}} ∉ ({∅, {∅}} : Set (Set (Set (Set α))))
  ∧ {{∅}} ⊆ ({∅, {∅}} : Set (Set (Set (Set α)))) := ⟨by simp, by simp⟩

/-- #### Exercise 1.1d

`{{∅}} ___ {∅, {{∅}}}`
-/
theorem exercise_1_1d
  : {{∅}} ∈ ({∅, {{∅}}} : Set (Set (Set (Set α))))
  ∧ ¬ {{∅}} ⊆ ({∅, {{∅}}} : Set (Set (Set (Set α)))) := by
  refine ⟨by simp, ?_⟩
  intro h
  simp at h
  exact empty_ne_singleton_empty h

/-- #### Exercise 1.1e

`{{∅}} ___ {∅, {∅, {∅}}}`
-/
theorem exercise_1_1e
  : {{∅}} ∉ ({∅, {∅, {∅}}} : Set (Set (Set (Set α))))
  ∧ ¬ {{∅}} ⊆ ({∅, {∅, {∅}}} : Set (Set (Set (Set α)))) := by
  apply And.intro
  · intro h
    simp at h
    rw [Set.ext_iff] at h
    have nh := h ∅
    simp at nh
    exact empty_ne_singleton_empty nh
  · intro h
    simp at h
    rw [Set.ext_iff] at h
    have nh := h {∅}
    simp at nh

/-- ### Exercise 1.2

Show that no two of the three sets `∅`, `{∅}`, and `{{∅}}` are equal to each
other.
-/
theorem exercise_1_2
  : ∅ ≠ ({∅} : Set (Set α))
  ∧ ∅ ≠ ({{∅}} : Set (Set (Set α)))
  ∧ {∅} ≠ ({{∅}} : Set (Set (Set α))) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro h
    exact empty_ne_singleton_empty h
  · intro h
    exact absurd h (Ne.symm $ Set.singleton_ne_empty ({∅} : Set (Set α)))
  · intro h
    simp at h
    exact empty_ne_singleton_empty h

/-- ### Exercise 1.3

Show that if `B ⊆ C`, then `𝓟 B ⊆ 𝓟 C`.
-/
theorem exercise_1_3 (h : B ⊆ C) : Set.powerset B ⊆ Set.powerset C := by
  intro x hx
  exact Set.Subset.trans hx h

/-- ### Exercise 1.4

Assume that `x` and `y` are members of a set `B`. Show that
`{{x}, {x, y}} ∈ 𝓟 𝓟 B`.
-/
theorem exercise_1_4 (x y : α) (hx : x ∈ B) (hy : y ∈ B)
  : {{x}, {x, y}} ∈ Set.powerset (Set.powerset B) := by
  unfold Set.powerset
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [Set.subset_def]
  intro z hz
  simp at hz
  apply Or.elim hz
  · intro h
    rwa [h, Set.mem_setOf_eq, Set.singleton_subset_iff]
  · intro h
    rw [h, Set.mem_setOf_eq]
    exact Set.union_subset
      (Set.singleton_subset_iff.mpr hx)
      (Set.singleton_subset_iff.mpr hy)

end Enderton.Set.Chapter_1
