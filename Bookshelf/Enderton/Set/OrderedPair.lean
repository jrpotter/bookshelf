import Common.Set.Basic

/-! # Enderton.Set.OrderedPair

A representation of an ordered pair in basic set theory. Like `Set`, it is
assumed an ordered pair is homogeneous.
-/

/--
Kazimierz Kuratowski's definition of an ordered pair.
-/
def OrderedPair (x y : α) : Set (Set α) := {{x}, {x, y}}

namespace OrderedPair

/--
For any sets `x`, `y`, `u`, and `v`, `⟨u, v⟩ = ⟨x, y⟩` **iff** `u = x ∧ v = y`.
-/
theorem ext_iff {x y u v : α}
  : (OrderedPair x y = OrderedPair u v) ↔ (x = u ∧ y = v) := by
  unfold OrderedPair
  apply Iff.intro
  · intro h
    have hu := Set.ext_iff.mp h {u}
    have huv := Set.ext_iff.mp h {u, v}
    simp only [
      Set.mem_singleton_iff, Set.mem_insert_iff, true_or, or_true, iff_true
    ] at hu huv
    apply Or.elim hu <;> apply Or.elim huv

    · -- #### Case 1
      -- `{u} = {x}` and `{u, v} = {x}`.
      intro huv_x hu_x
      rw [Set.singleton_eq_singleton_iff] at hu_x
      rw [hu_x] at huv_x
      have hx_v := Set.pair_eq_singleton_mem_imp_eq_self huv_x
      rw [hu_x, hx_v] at h
      simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem] at h
      have := Set.pair_eq_singleton_mem_imp_eq_self $
        Set.pair_eq_singleton_mem_imp_eq_self h
      rw [← hx_v] at this
      exact ⟨hu_x.symm, this⟩

    · -- #### Case 2
      -- `{u} = {x}` and `{u, v} = {x, y}`.
      intro huv_xy hu_x
      rw [Set.singleton_eq_singleton_iff] at hu_x
      rw [hu_x] at huv_xy
      by_cases hx_v : x = v
      · rw [hx_v] at huv_xy
        simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem] at huv_xy
        have := Set.pair_eq_singleton_mem_imp_eq_self huv_xy.symm
        exact ⟨hu_x.symm, this⟩
      · rw [Set.ext_iff] at huv_xy
        have := huv_xy v
        simp only [
          Set.mem_singleton_iff, Set.mem_insert_iff, or_true, true_iff
        ] at this
        exact ⟨hu_x.symm, Or.elim this (absurd ·.symm hx_v) (·.symm)⟩

    · -- #### Case 3
      -- `{u} = {x, y}` and `{u, v} = {x}`.
      intro huv_x hu_xy
      rw [Set.ext_iff] at huv_x hu_xy
      have hu_x := huv_x u
      have hy_u := hu_xy y
      simp only [
        Set.mem_singleton_iff,
        Set.mem_insert_iff,
        true_or,
        true_iff,
        or_true,
        iff_true
      ] at hu_x hy_u 
      apply Or.elim huv
      · intro huv_x
        rw [← hu_x, Set.ext_iff] at huv_x
        have := huv_x v
        simp only [
          Set.mem_singleton_iff, Set.mem_insert_iff, or_true, true_iff
        ] at this
        exact ⟨hu_x.symm, by rwa [this]⟩
      · intro huv_xy
        rw [hu_x, Set.ext_iff] at huv_xy
        have := huv_xy v
        simp only [
          Set.mem_singleton_iff, Set.mem_insert_iff, or_true, true_iff
         ] at this
        apply Or.elim this
        · intro hv_x
          rw [hy_u, hu_x]
          exact ⟨rfl, hv_x.symm⟩
        · intro hv_y
          exact ⟨hu_x.symm, hv_y.symm⟩

    · -- #### Case 4
      -- `{u} = {x, y}` and `{u, v} = {x, y}`.
      intro huv_xy hu_xy
      rw [Set.ext_iff] at huv_xy hu_xy
      have hx_u := hu_xy x
      have hy_u := hu_xy y
      simp only [
        Set.mem_singleton_iff, Set.mem_insert_iff, true_or, iff_true, or_true
      ] at hx_u hy_u 
      have := huv_xy v
      simp only [
        Set.mem_singleton_iff, Set.mem_insert_iff, or_true, true_iff
      ] at this 
      apply Or.elim this
      · intro hv_x
        rw [hv_x, hx_u]
        exact ⟨rfl, hy_u⟩
      · intro hv_y
        exact ⟨hx_u, hv_y.symm⟩

  · intro h
    rw [h.left, h.right]

end OrderedPair