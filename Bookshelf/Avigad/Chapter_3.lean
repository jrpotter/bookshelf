/-! # Avigad.Chapter3

Propositions and Proofs
-/

/-! #### Exercise 1

Prove the following identities.
-/

namespace Avigad.Chapter3

namespace ex1

open or

variable (p q r : Prop)

-- Commutativity of ∧ and ∨
theorem and_comm' : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun ⟨hp, hq⟩ => show q ∧ p from ⟨hq, hp⟩)
    (fun ⟨hq, hp⟩ => show p ∧ q from ⟨hp, hq⟩)

theorem or_comm' : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => h.elim Or.inr Or.inl)
    (fun h => h.elim Or.inr Or.inl)

-- Associativity of ∧ and ∨
theorem and_assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, hq, hr⟩)
    (fun ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩)

theorem or_assoc' : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h₁ => h₁.elim
      (fun h₂ => h₂.elim Or.inl (Or.inr ∘ Or.inl))
      (Or.inr ∘ Or.inr))
    (fun h₁ => h₁.elim
      (Or.inl ∘ Or.inl)
      (fun h₂ => h₂.elim (Or.inl ∘ Or.inr) Or.inr))

-- Distributivity
theorem and_or_left : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun ⟨hp, hqr⟩ => hqr.elim (Or.inl ⟨hp, ·⟩) (Or.inr ⟨hp, ·⟩))
    (fun h₁ => h₁.elim
      (fun ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩)
      (fun ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩))

theorem or_and_left : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h => h.elim
      (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
      (fun ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩))
    (fun ⟨h₁, h₂⟩ => h₁.elim
      Or.inl
      (fun hq => h₂.elim Or.inl (fun hr => Or.inr ⟨hq, hr⟩)))

-- Other properties
theorem imp_imp_iff_and_imp : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h ⟨hp, hq⟩ => h hp hq)
    (fun h hp hq => h ⟨hp, hq⟩)

theorem or_imp : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h =>
      have h₁ : p → r := h ∘ Or.inl
      have h₂ : q → r := h ∘ Or.inr
      show (p → r) ∧ (q → r) from ⟨h₁, h₂⟩)
    (fun ⟨h₁, h₂⟩ h => h.elim h₁ h₂)

theorem nor_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h => ⟨h ∘ Or.inl, h ∘ Or.inr⟩)
    (fun h₁ h₂ => h₂.elim (absurd · h₁.left) (absurd · h₁.right))

theorem not_and_or_mpr : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h₁ h₂ => h₁.elim (absurd h₂.left ·) (absurd h₂.right ·)

theorem and_not_self : ¬(p ∧ ¬p) :=
  fun h => absurd h.left h.right

theorem not_imp_o_and_not : p ∧ ¬q → ¬(p → q) :=
  fun ⟨hp, nq⟩ hpq => absurd (hpq hp) nq

theorem false_elim_self : ¬p → (p → q) :=
  fun np hp => absurd hp np

theorem not_or_imp_imp : (¬p ∨ q) → (p → q) :=
  fun npq hp => npq.elim (absurd hp ·) id

theorem or_false_iff : p ∨ False ↔ p :=
  Iff.intro (fun hpf => hpf.elim id False.elim) Or.inl

theorem and_false_iff : p ∧ False ↔ False :=
  Iff.intro (fun ⟨_, hf⟩ => hf) False.elim

theorem imp_imp_not_imp_not : (p → q) → (¬q → ¬p) :=
  fun hpq nq hp => absurd (hpq hp) nq

end ex1

/-! #### Exercise 2

Prove the following identities. These require classical reasoning.
-/

namespace ex2

open Classical

variable (p q r s : Prop)

theorem imp_or_mp (hp : p) : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  fun h => (h hp).elim
    (fun hr => Or.inl (fun _ => hr))
    (fun hs => Or.inr (fun _ => hs))

theorem not_and_iff_or_not : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun npq => (em p).elim
    (fun hp => (em q).elim
      (fun hq => False.elim (npq ⟨hp, hq⟩))
      Or.inr)
    Or.inl

theorem not_imp_mp : ¬(p → q) → p ∧ ¬q :=
  fun h =>
    have lhs : p := byContradiction
      fun np => h (fun (hp : p) => absurd hp np)
    ⟨lhs, fun hq => h (fun _ => hq)⟩

theorem not_or_of_imp : (p → q) → (¬p ∨ q) :=
  fun hpq => (em p).elim (fun hp => Or.inr (hpq hp)) Or.inl

theorem not_imp_not_imp_imp : (¬q → ¬p) → (p → q) :=
  fun h hp => byContradiction
    fun nq => absurd hp (h nq)

theorem or_not : p ∨ ¬p := em p

theorem imp_imp_imp : (((p → q) → p) → p) :=
  fun h => byContradiction
    fun np =>
      suffices hp : p from absurd hp np
      h (fun (hp : p) => absurd hp np)

end ex2

/-! #### Exercise 3

Prove `¬(p ↔ ¬p)` without using classical logic.
-/

namespace ex3

variable (p : Prop)

theorem iff_not_self (hp : p) : ¬(p ↔ ¬p) :=
  fun h => absurd hp (Iff.mp h hp)

end ex3

end Avigad.Chapter3