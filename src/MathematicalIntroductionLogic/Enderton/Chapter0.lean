/-
Chapter 0

Useful Facts About Sets
-/

import MathematicalIntroductionLogic.Tuple.Generic

variable {k m n : Nat}
variable (p : 1 ≤ m)
variable (q : n + (m - 1) = m + k)

private lemma n_eq_succ_k : n = k + 1 := by
  let ⟨m', h⟩ := Nat.exists_eq_succ_of_ne_zero $ show m ≠ 0 by
    intro h
    have ff : 1 ≤ 0 := h ▸ p
    ring_nf at ff
    exact ff.elim
  calc
    n = n + (m - 1) - (m - 1) := by rw [Nat.add_sub_cancel]
    _ = m' + 1 + k - (m' + 1 - 1) := by rw [q, h]
    _ = m' + 1 + k - m' := by simp
    _ = 1 + k + m' - m' := by rw [Nat.add_assoc, Nat.add_comm]
    _ = 1 + k := by simp
    _ = k + 1 := by rw [Nat.add_comm]

private lemma n_pred_eq_k : n - 1 = k := by
  have h : k + 1 - 1 = k + 1 - 1 := rfl
  conv at h => lhs; rw [←n_eq_succ_k p q]
  simp at h
  exact h

private lemma n_geq_one : 1 ≤ n := by
  rw [n_eq_succ_k p q]
  simp

private lemma min_comm_succ_eq : min (m + k) (k + 1) = k + 1 :=
  Nat.recOn k
    (by simp; exact p)
    (fun k' ih => calc min (m + (k' + 1)) (k' + 1 + 1)
      _ = min (m + k' + 1) (k' + 1 + 1) := by conv => rw [Nat.add_assoc]
      _ = min (m + k') (k' + 1) + 1 := Nat.min_succ_succ (m + k') (k' + 1)
      _ = k' + 1 + 1 := by rw [ih])

private lemma n_eq_min_comm_succ : n = min (m + k) (k + 1) := by
  rw [min_comm_succ_eq p]
  exact n_eq_succ_k p q

private lemma n_pred_m_eq_m_k : n + (m - 1) = m + k := by
  rw [←Nat.add_sub_assoc p, Nat.add_comm, Nat.add_sub_assoc (n_geq_one p q)]
  conv => lhs; rw [n_pred_eq_k p q]

private def cast_norm : GTuple α (n, m - 1) → Tuple α (m + k)
  | xs => cast (by rw [q]) xs.norm

private def cast_fst : GTuple α (n, m - 1) → Tuple α (k + 1)
  | xs => cast (by rw [n_eq_succ_k p q]) xs.fst

private def cast_take (ys : Tuple α (m + k)) :=
  cast (by rw [min_comm_succ_eq p]) (ys.take (k + 1))

/--
Lemma 0A

Assume that `⟨x₁, ..., xₘ⟩ = ⟨y₁, ..., yₘ, ..., yₘ₊ₖ⟩`. Then
`x₁ = ⟨y₁, ..., yₖ₊₁⟩`.
-/
theorem lemma_0a (xs : GTuple α (n, m - 1)) (ys : Tuple α (m + k))
  : (cast_norm q xs = ys) → (cast_fst p q xs = cast_take p ys) := by
  intro h
  suffices HEq
    (cast (_ : Tuple α n = Tuple α (k + 1)) xs.fst)
    (cast (_ : Tuple α (min (m + k) (k + 1)) = Tuple α (k + 1)) (Tuple.take ys (k + 1)))
    from eq_of_heq this
  congr
  · exact n_eq_min_comm_succ p q
  · rfl
  · exact n_eq_min_comm_succ p q
  · exact HEq.rfl
  · exact Eq.recOn
      (motive := fun _ h => HEq
        (_ : n + (n - 1) = n + k)
        (cast h (show n + (n - 1) = n + k by rw [n_pred_eq_k p q])))
      (show (n + (n - 1) = n + k) = (min (m + k) (k + 1) + (n - 1) = n + k) by
        rw [n_eq_min_comm_succ p q])
      HEq.rfl
  · exact n_geq_one p q
  · exact n_pred_eq_k p q
  · exact Eq.symm (n_eq_min_comm_succ p q)
  · exact n_pred_eq_k p q
  · rw [GTuple.self_fst_eq_norm_take]
    unfold cast_norm at h
    simp at h
    rw [←h, ←n_eq_succ_k p q]
    have h₂ := Eq.recOn
      (motive := fun x h => HEq
        (Tuple.take xs.norm n)
        (Tuple.take (cast (show Tuple α (n + (m - 1)) = Tuple α x by rw [h]) xs.norm) n))
      (show n + (m - 1) = m + k by rw [n_pred_m_eq_m_k p q])
      HEq.rfl
    exact Eq.recOn
      (motive := fun x h => HEq
        (cast h (Tuple.take xs.norm n))
        (Tuple.take (cast (_ : Tuple α (n + (m - 1)) = Tuple α (m + k)) xs.norm) n))
      (show Tuple α (min (n + (m - 1)) n) = Tuple α n by simp)
      h₂
