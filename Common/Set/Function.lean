import Mathlib.Data.Set.Function

/-! # Common.Set.Function

Additional theorems around functions defined on sets.
-/

namespace Set.Function

/--
Produce a new function that swaps the outputs of the two specified inputs.
-/
def swap [DecidableEq α] (f : α → β) (x₁ x₂ : α) (x : α) : β :=
  if x = x₁ then f x₂ else
  if x = x₂ then f x₁ else
                 f x

/--
Swapping the same input yields the original function.
-/
@[simp]
theorem swap_eq_eq_self [DecidableEq α] {f : α → β} {x : α}
  : swap f x x = f := by
  refine funext ?_
  intro y
  unfold swap
  by_cases hy : y = x
  · rw [if_pos hy, hy]
  · rw [if_neg hy, if_neg hy]

/--
Swapping a function twice yields the original function.
-/
@[simp]
theorem swap_swap_eq_self [DecidableEq α] {f : α → β} {x₁ x₂ : α}
  : swap (swap f x₁ x₂) x₁ x₂ = f := by
  refine funext ?_
  intro y
  by_cases hc₁ : x₂ = x₁
  · rw [hc₁]
    simp
  rw [← Ne.def] at hc₁
  unfold swap
  by_cases hc₂ : y = x₁ <;>
  by_cases hc₃ : y = x₂
  · rw [if_pos hc₂, if_neg hc₁, if_pos rfl, ← hc₂]
  · rw [if_pos hc₂, if_neg hc₁, if_pos rfl, ← hc₂]
  · rw [if_neg hc₂, if_pos hc₃, if_pos rfl, ← hc₃]
  · rw [if_neg hc₂, if_neg hc₃, if_neg hc₂, if_neg hc₃]

/--
If `f : A → B`, then a swapped variant of `f` also maps `A` into `B`.
-/
theorem swap_MapsTo_self [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : MapsTo f A B)
  : MapsTo (swap f a₁ a₂) A B := by
  intro x hx
  unfold swap
  by_cases hc₁ : x = a₁ <;> by_cases hc₂ : x = a₂
  · rw [if_pos hc₁]
    exact hf ha₂
  · rw [if_pos hc₁]
    exact hf ha₂
  · rw [if_neg hc₁, if_pos hc₂]
    exact hf ha₁
  · rw [if_neg hc₁, if_neg hc₂]
    exact hf hx

/--
The converse of `swap_MapsTo_self`.
-/
theorem self_MapsTo_swap [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : MapsTo (swap f a₁ a₂) A B)
  : MapsTo f A B := by
  rw [← @swap_swap_eq_self _ _ _ f a₁ a₂]
  exact swap_MapsTo_self ha₁ ha₂ hf

/--
If `f : A → B`, then `f` maps `A` into `B` **iff** a swap of `f` maps `A` into
`B`.
-/
theorem self_iff_swap_MapsTo [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
  : MapsTo (swap f a₁ a₂) A B ↔ MapsTo f A B :=
  ⟨self_MapsTo_swap ha₁ ha₂, swap_MapsTo_self ha₁ ha₂⟩

/--
If `f : A → B` is one-to-one, then a swapped variant of `f` is also one-to-one.
-/
theorem swap_InjOn_self [DecidableEq α]
  {A : Set α} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : InjOn f A)
  : InjOn (swap f a₁ a₂) A := by
  intro x₁ hx₁ x₂ hx₂ h
  unfold swap at h
  by_cases hc₁ : x₁ = a₁ <;>
  by_cases hc₂ : x₁ = a₂ <;>
  by_cases hc₃ : x₂ = a₁ <;>
  by_cases hc₄ : x₂ = a₂
  · rw [hc₁, hc₃]
  · rw [hc₁, hc₃]
  · rw [hc₂, hc₄]
  · rw [if_pos hc₁, if_neg hc₃, if_neg hc₄, ← hc₂] at h
    exact hf hx₁ hx₂ h
  · rw [hc₁, hc₃]
  · rw [hc₁, hc₃]
  · rw [if_pos hc₁, if_neg hc₃, if_pos hc₄, ← hc₁, ← hc₄] at h
    exact hf hx₁ hx₂ h.symm
  · rw [if_pos hc₁, if_neg hc₃, if_neg hc₄] at h
    exact absurd (hf hx₂ ha₂ h.symm) hc₄
  · rw [hc₂, hc₄]
  · rw [if_neg hc₁, if_pos hc₂, if_pos hc₃, ← hc₂, ← hc₃] at h
    exact hf hx₁ hx₂ h.symm
  · rw [hc₂, hc₄]
  · rw [if_neg hc₁, if_pos hc₂, if_neg hc₃, if_neg hc₄] at h
    exact absurd (hf hx₂ ha₁ h.symm) hc₃
  · rw [if_neg hc₁, if_neg hc₂, if_pos hc₃, ← hc₄] at h
    exact hf hx₁ hx₂ h
  · rw [if_neg hc₁, if_neg hc₂, if_pos hc₃] at h
    exact absurd (hf hx₁ ha₂ h) hc₂
  · rw [if_neg hc₁, if_neg hc₂, if_neg hc₃, if_pos hc₄] at h
    exact absurd (hf hx₁ ha₁ h) hc₁
  · rw [if_neg hc₁, if_neg hc₂, if_neg hc₃, if_neg hc₄] at h
    exact hf hx₁ hx₂ h

/--
The converse of `swap_InjOn_self`.
-/
theorem self_InjOn_swap [DecidableEq α]
  {A : Set α} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : InjOn (swap f a₁ a₂) A)
  : InjOn f A := by
  rw [← @swap_swap_eq_self _ _ _ f a₁ a₂]
  exact swap_InjOn_self ha₁ ha₂ hf

/--
If `f : A → B`, then `f` is one-to-one **iff** a swap of `f` is one-to-one.
-/
theorem self_iff_swap_InjOn [DecidableEq α]
  {A : Set α} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
  : InjOn (swap f a₁ a₂) A ↔ InjOn f A :=
  ⟨self_InjOn_swap ha₁ ha₂, swap_InjOn_self ha₁ ha₂⟩

/--
If `f : A → B` is onto, then a swapped variant of `f` is also onto.
-/
theorem swap_SurjOn_self [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : SurjOn f A B)
  : SurjOn (swap f a₁ a₂) A B := by
  show ∀ x, x ∈ B → ∃ a ∈ A, swap f a₁ a₂ a = x
  intro x hx
  have ⟨a, ha⟩ := hf hx
  by_cases hc₁ : a = a₁
  · refine ⟨a₂, ha₂, ?_⟩
    unfold swap
    by_cases hc₂ : a₁ = a₂
    · rw [if_pos hc₂.symm, ← hc₂, ← hc₁]
      exact ha.right
    · rw [← Ne.def] at hc₂
      rw [if_neg hc₂.symm, if_pos rfl, ← hc₁]
      exact ha.right
  · by_cases hc₂ : a = a₂
    · unfold swap
      refine ⟨a₁, ha₁, ?_⟩
      rw [if_pos rfl, ← hc₂]
      exact ha.right
    · refine ⟨a, ha.left, ?_⟩
      unfold swap
      rw [if_neg hc₁, if_neg hc₂]
      exact ha.right

/--
The converse of `swap_SurjOn_self`.
-/
theorem self_SurjOn_swap [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : SurjOn (swap f a₁ a₂) A B)
  : SurjOn f A B := by
  rw [← @swap_swap_eq_self _ _ _ f a₁ a₂]
  exact swap_SurjOn_self ha₁ ha₂ hf

/--
If `f : A → B`, then `f` is onto **iff** a swap of `f` is onto.
-/
theorem self_iff_swap_SurjOn [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
  : SurjOn (swap f a₁ a₂) A B ↔ SurjOn f A B :=
  ⟨self_SurjOn_swap ha₁ ha₂, swap_SurjOn_self ha₁ ha₂⟩

/--
If `f : A → B` is a one-to-one correspondence, then a swapped variant of `f` is
also a one-to-one correspondence.
-/
theorem swap_BijOn_self [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : BijOn f A B)
  : BijOn (swap f a₁ a₂) A B := by
  have ⟨hf₁, hf₂, hf₃⟩ := hf
  exact ⟨
    swap_MapsTo_self ha₁ ha₂ hf₁,
    swap_InjOn_self ha₁ ha₂ hf₂,
    swap_SurjOn_self ha₁ ha₂ hf₃
  ⟩

/--
The converse of `swap_BijOn_self`.
-/
theorem self_BijOn_swap [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hf : BijOn (swap f a₁ a₂) A B)
  : BijOn f A B := by
  have ⟨hf₁, hf₂, hf₃⟩ := hf
  exact ⟨
    self_MapsTo_swap ha₁ ha₂ hf₁,
    self_InjOn_swap ha₁ ha₂ hf₂,
    self_SurjOn_swap ha₁ ha₂ hf₃
  ⟩

/--
If `f : A → B`, `f` is a one-to-one correspondence **iff** a swap of `f` is a
one-to-one correspondence.
-/
theorem self_iff_swap_BijOn [DecidableEq α]
  {A : Set α} {B : Set β} {f : α → β}
  (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
  : BijOn (swap f a₁ a₂) A B ↔ BijOn f A B :=
  ⟨self_BijOn_swap ha₁ ha₂, swap_BijOn_self ha₁ ha₂⟩

end Set.Function
