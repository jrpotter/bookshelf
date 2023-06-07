import Mathlib.Data.Set.Basic

import Common.Logic.Basic
import Common.Set.Basic

namespace Set

/--
Kazimierz Kuratowski's definition of an ordered pair.
-/
def OrderedPair (x y : α) : Set (Set α) := {{x}, {x, y}}

namespace OrderedPair

theorem ext_iff {x y u v : α}
  : (OrderedPair x y = OrderedPair u v) ↔ (x = u ∧ y = v) := by
  unfold OrderedPair
  apply Iff.intro
  · intro h
    have h' := h
    rw [Set.ext_iff] at h'
    have hu := h' {u}
    have huv := h' {u, v}
    simp only [mem_singleton_iff, mem_insert_iff, true_or, iff_true] at hu
    simp only [mem_singleton_iff, mem_insert_iff, or_true, iff_true] at huv
    apply Or.elim hu
    · apply Or.elim huv
      · -- #### Case 1
        -- `{u} = {x}` and `{u, v} = {x}`.
        intro huv_x hu_x
        rw [singleton_eq_singleton_iff] at hu_x
        rw [hu_x] at huv_x
        have hx_v := pair_eq_singleton_mem_imp_eq_self huv_x
        rw [hu_x, hx_v] at h
        simp only [mem_singleton_iff, insert_eq_of_mem] at h
        have := pair_eq_singleton_mem_imp_eq_self $
          pair_eq_singleton_mem_imp_eq_self h
        rw [← hx_v] at this
        exact ⟨hu_x.symm, this⟩
      · -- #### Case 2
        -- `{u} = {x}` and `{u, v} = {x, y}`.
        intro huv_xy hu_x
        rw [singleton_eq_singleton_iff] at hu_x
        rw [hu_x] at huv_xy
        by_cases hx_v : x = v
        · rw [hx_v] at huv_xy
          simp at huv_xy
          have := pair_eq_singleton_mem_imp_eq_self huv_xy.symm
          exact ⟨hu_x.symm, this⟩
        · rw [Set.ext_iff] at huv_xy
          have := huv_xy v
          simp at this
          apply Or.elim this
          · intro hv_x
            rw [hu_x, ← hv_x] at h
            simp at h
            have := pair_eq_singleton_mem_imp_eq_self $
              pair_eq_singleton_mem_imp_eq_self h
            exact ⟨hu_x.symm, this⟩
          · intro hv_y
            exact ⟨hu_x.symm, hv_y.symm⟩
    · apply Or.elim huv
      · -- #### Case 3
        -- `{u} = {x, y}` and `{u, v} = {x}`.
        intro huv_x hu_xy
        rw [Set.ext_iff] at huv_x
        have hu_x := huv_x u
        have hv_x := huv_x v
        simp only [mem_singleton_iff, mem_insert_iff, true_or, true_iff] at hu_x
        simp only [mem_singleton_iff, mem_insert_iff, or_true, true_iff] at hv_x
        rw [← hu_x] at hu_xy
        have := pair_eq_singleton_mem_imp_eq_self hu_xy.symm
        rw [hu_x, ← hv_x] at this
        exact ⟨hu_x.symm, this⟩
      · -- #### Case 4
        -- `{u} = {x, y}` and `{u, v} = {x, y}`.
        intro huv_xy hu_xy
        rw [Set.ext_iff] at hu_xy
        have hx_u := hu_xy x
        have hy_u := hu_xy y
        simp only [mem_singleton_iff, mem_insert_iff, true_or, iff_true] at hx_u
        simp only [mem_singleton_iff, mem_insert_iff, or_true, iff_true] at hy_u
        rw [hx_u, hy_u] at huv_xy
        simp only [mem_singleton_iff, insert_eq_of_mem] at huv_xy
        have := pair_eq_singleton_mem_imp_eq_self huv_xy
        rw [← this] at hy_u
        exact ⟨hx_u, hy_u⟩
  · intro h
    rw [h.left, h.right]

end OrderedPair

end Set