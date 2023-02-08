/- Exercises 5.8
 -
 - Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/

import tactic.rcases

-- Exercise 1
--
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you
-- can now with tactic proofs, using also `rw` and `simp` as appropriate.
section ex_1_3_1

variables p q r : Prop

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  split,
  { rintro ⟨p, q⟩, exact ⟨q, p⟩ },
  { rintro ⟨q, p⟩, exact ⟨p, q⟩ },
end

example : p ∨ q ↔ q ∨ p :=
begin
  split,
  { rintro (p | q),
    { exact or.inr p },
    { exact or.inl q },
  },
  { rintro (q | p),
    { exact or.inr q },
    { exact or.inl p },
  },
end

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  split,
  { rintro ⟨⟨p, q⟩, r⟩, exact ⟨p, q, r⟩ },
  { rintro ⟨p, q, r⟩, exact ⟨⟨p, q⟩, r⟩ },
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  split,
  { rintro ((p | q) | r),
    { exact or.inl p },
    { exact or.inr (or.inl q) },
    { exact or.inr (or.inr r) },
  },
  { rintro (p | q | r),
    { exact or.inl (or.inl p) },
    { exact or.inl (or.inr q) },
    { exact or.inr r },
  },
end

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  split,
  { rintro ⟨p, (q | r)⟩,
    { exact or.inl ⟨p, q⟩ },
    { exact or.inr ⟨p, r⟩ },
  },
  { rintro (⟨p, q⟩ | ⟨p, r⟩),
    { exact ⟨p, or.inl q⟩ },
    { exact ⟨p, or.inr r⟩ },
  },
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
  split,
  { rintro (p | ⟨q, r⟩),
    { exact ⟨or.inl p, or.inl p⟩ },
    { exact ⟨or.inr q, or.inr r⟩ },
  },
  { rintro ⟨(p | q), (p | r)⟩;
    exact or.inl p <|> exact or.inr ⟨q, r⟩,
  },
end

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
  split,
  { rintros h ⟨hp, hq⟩, exact h hp hq },
  { intros h hp hq, exact h ⟨hp, hq⟩ },
end

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
  split,
  { intros h₁,
    split,
    { intro p, exact h₁ (or.inl p) },
    { intro q, exact h₁ (or.inr q) },
  },
  { rintros ⟨hp, hq⟩ h,
    apply or.elim h,
    { intro p, exact hp p },
    { intro q, exact hq q },
  },
end

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  split,
  { intro h,
    split,
    { intro hp, apply h, exact or.inl hp },
    { intro hq, apply h, exact or.inr hq },
  },
  { rintros ⟨np, nq⟩ (p | q),
    { apply np, assumption },
    { apply nq, assumption },
  },
end

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
  rintro (np | nq) ⟨hp, hq⟩,
  { apply np, assumption },
  { apply nq, assumption },
end

example : ¬(p ∧ ¬p) :=
begin
  rintro ⟨hp, np⟩,
  exact absurd hp np
end

example : p ∧ ¬q → ¬(p → q) :=
begin
  rintro ⟨hp, nq⟩ hpq,
  apply nq,
  exact hpq hp
end

example : ¬p → (p → q) :=
begin
  intros np hp,
  exact absurd hp np,
end

example : (¬p ∨ q) → (p → q) :=
begin
  rintros (np | hq) hp,
  { exact absurd hp np },
  { exact hq },
end

example : p ∨ false ↔ p :=
begin
  split,
  { rintro (hp | hf),
    { exact hp },
    { exact false.elim hf },
  },
  { intro hp,
    exact or.inl hp,
  },
end

example : p ∧ false ↔ false :=
begin
  split,
  { rintro ⟨hp, hf⟩, assumption },
  { intro hf, exact false.elim hf },
end

example : (p → q) → (¬q → ¬p) :=
begin
  rintro hpq nq hp,
  apply nq,
  exact absurd (hpq hp) nq,
end

end ex_1_3_1

section ex_1_3_2

open classical

variables p q r s : Prop

example (hp : p) : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
  intro h,
  apply or.elim (h hp),
  { intro hr, exact or.inl (assume hp, hr) },
  { intro hs, exact or.inr (assume hp, hs) }
end

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin
  intro h₁,
  apply or.elim (classical.em p),
  { intro hp,
    apply or.elim (classical.em q),
    { assume hq, exact false.elim (h₁ ⟨hp, hq⟩) },
    { assume nq, exact or.inr nq },
  },
  { intro np,
    exact or.inl np,
  },
end

example : ¬(p → q) → p ∧ ¬q :=
begin
  intro h₁,
  split,
  { by_contradiction np, apply h₁, intro hp, exact absurd hp np },
  { intro hq, apply h₁, intro hp, exact hq },
end

example : (p → q) → (¬p ∨ q) :=
begin
  intro hpq,
  apply or.elim (classical.em p),
  { assume hp, exact or.inr (hpq hp) },
  { assume np, exact or.inl np },
end

example : (¬q → ¬p) → (p → q) :=
begin
  intros hqp hp,
  by_contradiction nq,
  exact absurd hp (hqp nq),
end

example : p ∨ ¬p :=
by apply classical.em

example : (((p → q) → p) → p) :=
begin
  intro h,
  apply or.elim (classical.em p),
  { intro hp, assumption },
  { intro np, apply h, intro hp, exact absurd hp np },
end

end ex_1_3_2

section ex_1_3_3

variable p : Prop

example (hp : p) : ¬(p ↔ ¬p) :=
begin
  intro h₁,
  cases h₁ with h₂,
  exact absurd hp (h₂ hp),
end

end ex_1_3_3

section ex_1_4_1

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
begin
  split,
  { intro h,
    split,
    { intro hx, exact and.left (h hx) },
    { intro hx, exact and.right (h hx) },
  },
  { intros h hx,
    have hl : ∀ (x : α), p x, from and.left h,
    have hr : ∀ (x : α), q x, from and.right h,
    exact ⟨hl hx, hr hx⟩
  },
end

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
begin
  intros h₁ h₂ hx,
  exact h₁ hx (h₂ hx)
end

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  rintro (h₁ | h₂),
  { intro hx, exact or.inl (h₁ hx) },
  { intro hx, exact or.inr (h₂ hx) },
end

end ex_1_4_1

section ex_1_4_2

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
begin
  intro hα,
  split,
  { intro hαr, apply hαr, exact hα },
  { intros hr hα, exact hr },
end

section

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
begin
  split,
  { intro h₁,
    apply or.elim (classical.em r),
    { intro hr, exact or.inr hr },
    { intro nr,
      exact or.inl begin
        intro hx,
        have h₂ : p hx ∨ r, from h₁ hx,
        apply or.elim h₂,
        { intro hp, exact hp },
        { intro hr, exact absurd hr nr },
      end
    },
  },
  { assume h₁ hx,
    apply or.elim h₁,
    { assume h₂, exact or.inl (h₂ hx) },
    { assume hr, exact or.inr hr },
  },
end

end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
  split,
  { intros h hr hx, exact h hx hr },
  { intros h hx hr, exact h hr hx },
end

end ex_1_4_2

section ex_1_4_3

open classical

variables (men : Type*) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
begin
  apply or.elim (classical.em (shaves barber barber)),
  { intro hb,
    apply iff.elim_left (h barber) hb,
    exact hb,
  },
  { intro nb,
    have s, from iff.elim_right (h barber) nb,
    exact absurd s nb
  },
end

end ex_1_4_3

section ex_1_4_5

open classical

variables (α : Type*) (p q : α → Prop)
variables r s : Prop

example : (∃ x : α, r) → r :=
begin
  rintro ⟨hx, hr⟩,
  exact hr,
end

example (a : α) : r → (∃ x : α, r) :=
begin
  intro hr,
  exact ⟨a, hr⟩
end

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
begin
  split,
  { rintro ⟨hx, ⟨hp, hr⟩⟩, exact ⟨⟨hx, hp⟩, hr⟩ },
  { rintro ⟨⟨hx, hp⟩, hr⟩, exact ⟨hx, ⟨hp, hr⟩⟩ },
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin
  split,
  { rintro ⟨hx, (hp | hq)⟩,
    { exact or.inl ⟨hx, hp⟩ },
    { exact or.inr ⟨hx, hq⟩ },
  },
  { rintro (⟨hx, hp⟩ | ⟨hx, hq⟩),
    { exact ⟨hx, or.inl hp⟩ },
    { exact ⟨hx, or.inr hq⟩ },
  },
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
  split,
  { rintros ha ⟨hx, np⟩, exact absurd (ha hx) np },
  { intros he hx, by_contradiction np, exact he ⟨hx, np⟩ },
end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
begin
  split,
  { rintro ⟨hx, hp⟩ h, exact absurd hp (h hx) },
  { intro h₁,
    by_contradiction h₂,
    apply h₁,
    intros hx hp,
    exact h₂ ⟨hx, hp⟩,
  },
end

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
  split,
  { intros h hx hp,
    exact h ⟨hx, hp⟩
  },
  { rintros h ⟨hx, hp⟩,
    exact absurd hp (h hx)
  },
end

lemma forall_negation : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
begin
  split,
  { intro h₁,
    by_contradiction h₂,
    exact h₁ (λ (x : α), begin
      by_contradiction np,
      exact h₂ ⟨x, np⟩
    end)
  },
  { rintros ⟨hx, np⟩ h, exact absurd (h hx) np },
end

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := forall_negation α p

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
begin
  split,
  { rintros h ⟨hx, hp⟩, exact h hx hp },
  { intros h hx hp,
    exact h ⟨hx, hp⟩
  },
end

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
begin
  split,
  { rintros ⟨hx, hp⟩ h, apply hp, exact h hx },
  { intro h₁,
    apply or.elim (classical.em (∀ x, p x)),
    { intro h₂, exact ⟨a, (assume hp, h₁ h₂)⟩ },
    { intro h₂,
      have h₃ : (∃ x, ¬p x), from iff.elim_left (forall_negation α p) h₂,
      exact let ⟨hx, hp⟩ := h₃ in ⟨hx, (assume hp', absurd hp' hp)⟩,
    },
  },
end

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
begin
  split,
  { rintros ⟨hx, h⟩ hr, exact ⟨hx, h hr⟩ },
  { intro h,
    apply or.elim (classical.em r),
    { intro hr,
      exact let ⟨hx, hp⟩ := h hr in ⟨hx, (assume hr, hp)⟩
    },
    { intro nr, exact ⟨a, (assume hr, absurd hr nr)⟩ },
  },
end

end ex_1_4_5

-- Exercise 2
--
-- Use tactic combinators to obtain a one line proof of the following:
section ex_2

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by simp *

end ex_2
