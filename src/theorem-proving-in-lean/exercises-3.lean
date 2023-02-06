/- Exercises 3.7
 -
 - Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/

-- Exercise 1
--
-- Prove the following identities, replacing the "sorry" placeholders with
-- actual proofs.
section ex_1

open or

variables p q r : Prop

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume ⟨p, q⟩, ⟨q, p⟩)
    (assume ⟨q, p⟩, ⟨p, q⟩)
example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume h, h.elim
      (assume hp : p, inr hp)
      (assume hq : q, inl hq))
    (assume h, h.elim
      (assume hq : q, inr hq)
      (assume hp : p, inl hp))

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume ⟨⟨p, q⟩, r⟩, ⟨p, q, r⟩)
    (assume ⟨p, q, r⟩, ⟨⟨p, q⟩, r⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume h₁, h₁.elim
      (assume h₂, h₂.elim (assume p, inl p) (assume q, inr (inl q)))
      (assume r, inr (inr r)))
    (assume h₁, h₁.elim
      (assume p, inl (inl p))
      (assume h₂, h₂.elim (assume q, inl (inr q)) (assume r, inr r)))

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume ⟨hp, hqr⟩, hqr.elim
      (assume hq, inl ⟨hp, hq⟩)
      (assume hr, inr ⟨hp, hr⟩))
    (assume h₁, h₁.elim
      (assume ⟨hp, hq⟩, ⟨hp, inl hq⟩)
      (assume ⟨hp, hr⟩, ⟨hp, inr hr⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume h, h.elim
      (assume hp, ⟨inl hp, inl hp⟩)
      (assume ⟨hq, hr⟩, ⟨inr hq, inr hr⟩))
    (assume ⟨h₁, h₂⟩, h₁.elim
      (assume hp, inl hp)
      (assume hq, h₂.elim (assume hp, inl hp) (assume hr, inr ⟨hq, hr⟩)))

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume h ⟨hp, hq⟩, h hp hq)
    (assume h hp hq, h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume h,
      have h₁ : p → r, from (assume hp, h (or.inl hp)),
      have h₂ : q → r, from (assume hq, h (or.inr hq)),
      ⟨h₁, h₂⟩)
    (assume ⟨hpr, hqr⟩, assume hpq, hpq.elim hpr hqr)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h, and.intro
      (assume hp, h (inl hp))
      (assume hq, h (inr hq)))
    (assume h₁ h₂, h₂.elim
      (assume hp, have np : ¬p, from h₁.left, absurd hp np)
      (assume hq, have nq : ¬q, from h₁.right, absurd hq nq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume h₁ h₂,
  h₁.elim
    (assume np : ¬p, have hp : p, from h₂.left, absurd hp np)
    (assume nq : ¬q, have hq : q, from h₂.right, absurd hq nq)

example : ¬(p ∧ ¬p) :=
  assume h,
  have hp : p, from h.left,
  have np : ¬p, from h.right,
  absurd hp np

example : p ∧ ¬q → ¬(p → q) :=
  assume ⟨hp, nq⟩ hpq,
  absurd (hpq hp) nq

example : ¬p → (p → q) :=
  assume np hp,
  absurd hp np

example : (¬p ∨ q) → (p → q) :=
  assume npq hp,
  npq.elim
    (assume np, absurd hp np)
    (assume hq, hq)

example : p ∨ false ↔ p :=
  iff.intro
    (assume hpf, hpf.elim
      (assume hp, hp)
      (assume hf, false.elim hf))
    (assume hp, inl hp)

example : p ∧ false ↔ false :=
  iff.intro
    (assume ⟨hp, hf⟩, hf)
    (assume hf, false.elim hf)

example : (p → q) → (¬q → ¬p) :=
  assume hpq nq hp,
  absurd (hpq hp) nq

end ex_1

-- Example 2
--
-- Prove the following identities, replacing the “sorry” placeholders with
-- actual proofs. These require classical reasoning.
section ex_2

open classical

variables p q r s : Prop

example (hp : p) : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume h₁,
  or.elim (h₁ hp)
    (assume hr, or.inl (assume hp, hr))
    (assume hs, or.inr (assume hp, hs))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume npq,
  or.elim (em p)
    (assume hp, or.elim (em q)
      (assume hq, false.elim (npq ⟨hp, hq⟩))
      (assume nq, or.inr nq))
    (assume np, or.inl np)

example : ¬(p → q) → p ∧ ¬q :=
  assume h₁,
  and.intro
    (by_contradiction (
      assume np,
      h₁ (λ (hp : p), absurd hp np)
    ))
    (assume hq, h₁ (λ (hp : p), hq))

example : (p → q) → (¬p ∨ q) :=
  assume hpq,
  or.elim (em p)
    (assume hp, or.inr (hpq hp))
    (assume np, or.inl np)

example : (¬q → ¬p) → (p → q) :=
  assume h₁ hp,
  by_contradiction (assume nq, absurd hp (h₁ nq))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  assume h₁,
  by_contradiction (
    assume np,
    suffices hp : p, from absurd hp np,
    h₁ (λ (hp : p), absurd hp np)
  )

end ex_2

-- Example 3
--
-- Prove `¬(p ↔ ¬p)` without using classical logic.
section ex_3

variable p : Prop

example (hp : p) : ¬(p ↔ ¬p) :=
  assume h,
  absurd hp (iff.elim_left h (hp))

end ex_3
