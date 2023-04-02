/-
Chapter 5

Tactics
-/

-- Exercise 1
--
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you
-- can now with tactic proofs, using also `rw` and `simp` as appropriate.
namespace ex1

-- Exercises 3.1

section ex3_1

variable (p q r : Prop)

-- Commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · intro
    | Or.inl hp => exact Or.inr hp
    | Or.inr hq => exact Or.inl hq
  · intro
    | Or.inl hq => exact Or.inr hq
    | Or.inr hp => exact Or.inl hp

-- Associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · intro
    | Or.inl (Or.inl hp) => exact Or.inl hp
    | Or.inl (Or.inr hq) => exact Or.inr (Or.inl hq)
    | Or.inr         hr  => exact Or.inr (Or.inr hr)
  · intro
    | Or.inl         hp  => exact Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => exact Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => exact Or.inr hr

-- Distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩
  · intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro
    | Or.inl      hp  => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  · intro
    | ⟨Or.inl hp,         _⟩ => exact Or.inl hp
    | ⟨Or.inr  _, Or.inl hp⟩ => exact Or.inl hp
    | ⟨Or.inr hq, Or.inr hr⟩ => exact Or.inr ⟨hq, hr⟩

-- Other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · intro h ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hpr, hqr⟩ h
    apply Or.elim h
    · intro hp
      exact hpr hp
    · intro hq
      exact hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨np, nq⟩
    intro
    | Or.inl hp => exact absurd hp np
    | Or.inr hq => exact absurd hq nq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl np => intro h; exact absurd h.left np
  | Or.inr nq => intro h; exact absurd h.right nq

example : ¬(p ∧ ¬p) := by
  intro ⟨hp, np⟩
  exact absurd hp np

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, nq⟩ h
  exact absurd (h hp) nq

example : ¬p → (p → q) := by
  intro np hp
  exact absurd hp np

example : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl np => intro hp; exact absurd hp np
  | Or.inr hq => exact fun _ => hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  · intro
    | Or.inl hp => exact hp
    | Or.inr ff => exact False.elim ff
  · intro hp
    exact Or.inl hp

example : p ∧ False ↔ False := by
  apply Iff.intro
  · intro ⟨_, ff⟩
    exact ff
  · intro ff
    exact False.elim ff

example : (p → q) → (¬q → ¬p) := by
  intro hpq nq hp
  exact absurd (hpq hp) nq

end ex3_1

-- Exercises 3.2

section ex3_2

open Classical

variable (p q r s : Prop)

example (hp : p) : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro h
  apply (h hp).elim
  · intro hr
    exact Or.inl (fun _ => hr)
  · intro hs
    exact Or.inr (fun _ => hs)

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  apply (em p).elim
  · intro hp
    apply (em q).elim
    · intro hq
      exact False.elim (h ⟨hp, hq⟩)
    · intro nq
      exact Or.inr nq
  · intro np
    exact Or.inl np

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  apply And.intro
  · apply byContradiction
    intro np
    apply h
    intro hp
    exact absurd hp np
  · intro hq
    apply h
    intro _
    exact hq

example : (p → q) → (¬p ∨ q) := by
  intro hpq
  apply (em p).elim
  · intro hp
    exact Or.inr (hpq hp)
  · intro np
    exact Or.inl np

example : (¬q → ¬p) → (p → q) := by
  intro hqp hp
  apply byContradiction
  intro nq
  exact absurd hp (hqp nq)

example : p ∨ ¬p := by apply em

example : (((p → q) → p) → p) := by
  intro h
  apply (em p).elim
  · intro hp
    exact hp
  · intro np
    apply h
    intro hp
    exact absurd hp np

end ex3_2

-- Exercises 3.3

section ex3_3

variable (p : Prop)

example (hp : p) : ¬(p ↔ ¬p) := by
  intro h
  exact absurd hp (h.mp hp)

end ex3_3

-- Exercises 4.1

section ex4_1

variable (α : Type _)
variable (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hx; exact And.left (h hx)
    · intro hx; exact And.right (h hx)
  · intro h hx
    have lhs : ∀ (x : α), p x := And.left h
    have rhs : ∀ (x : α), q x := And.right h
    exact ⟨lhs hx, rhs hx⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h₁ h₂ hx
  exact h₁ hx (h₂ hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | Or.inl h => intro hx; exact Or.inl (h hx)
  | Or.inr h => intro hx; exact Or.inr (h hx)

end ex4_1

-- Exercises 4.2

section ex4_2

variable (α : Type _)
variable (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro ha
  apply Iff.intro
  · intro har
    apply har
    exact ha
  · intro hr _
    exact hr

section

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  · intro h
    apply (em r).elim
    · intro hr
      exact Or.inr hr
    · intro nr
      apply Or.inl
      · intro hx
        apply (h hx).elim
        · exact id
        · intro hr
          exact absurd hr nr
  · intro h₁ hx
    apply h₁.elim
    · intro h₂
      exact Or.inl (h₂ hx)
    · intro hr
      exact Or.inr hr

end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  · intro h hr hx
    exact h hx hr
  · intro h hx hr
    exact h hr hx

end ex4_2

-- Exercises 4.3

section ex4_3

open Classical

variable (men : Type _)
variable (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  apply (em (shaves barber barber)).elim
  · intro hb
    exact absurd hb ((h barber).mp hb)
  · intro nb
    exact absurd ((h barber).mpr nb) nb

end ex4_3

-- Exercises 4.5

section ex4_5

open Classical

variable (α : Type _)
variable (p q : α → Prop)
variable (r s : Prop)

example : (∃ _ : α, r) → r := by
  intro ⟨_, hr⟩
  exact hr

example (a : α) : r → (∃ _ : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro ⟨hx, hp, hr⟩
    exact ⟨⟨hx, hp⟩, hr⟩
  · intro ⟨⟨hx, hp⟩, hr⟩
    exact ⟨hx, hp, hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro
    | ⟨hx, Or.inl hp⟩ => exact Or.inl ⟨hx, hp⟩
    | ⟨hx, Or.inr hq⟩ => exact Or.inr ⟨hx, hq⟩
  · intro
    | Or.inl ⟨hx, hp⟩ => exact ⟨hx, Or.inl hp⟩
    | Or.inr ⟨hx, hq⟩ => exact ⟨hx, Or.inr hq⟩

example : (∀ x, p x) ↔ ¬(∃ x, ¬p x) := by
  apply Iff.intro
  · intro ha ⟨hx, np⟩
    exact absurd (ha hx) np
  · intro he hx
    apply byContradiction
    intro np
    exact he ⟨hx, np⟩

example : (∃ x, p x) ↔ ¬(∀ x, ¬p x) := by
  apply Iff.intro
  · intro ⟨hx, hp⟩ h
    exact absurd hp (h hx)
  · intro h₁
    apply byContradiction
    intro h₂
    apply h₁
    intro hx hp
    exact h₂ ⟨hx, hp⟩

example : (¬∃ x, p x) ↔ (∀ x, ¬p x) := by
  apply Iff.intro
  · intro h hx hp
    exact h ⟨hx, hp⟩
  · intro h ⟨hx, hp⟩
    exact absurd hp (h hx)

theorem forall_negation : (¬∀ x, p x) ↔ (∃ x, ¬p x) := by
  apply Iff.intro
  · intro h₁
    apply byContradiction
    intro h₂
    exact h₁ (fun (x : α) => by
      apply byContradiction
      intro np
      exact h₂ ⟨x, np⟩)
  · intro ⟨hx, np⟩ h
    exact absurd (h hx) np

example : (¬∀ x, p x) ↔ (∃ x, ¬p x) := forall_negation α p

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  · intro h ⟨hx, hp⟩
    exact h hx hp
  · intro h hx hp
    exact h ⟨hx, hp⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  · intro ⟨hx, hp⟩ h
    apply hp
    exact h hx
  · intro h₁
    apply (em (∀ x, p x)).elim
    · intro h₂
      exact ⟨a, fun _ => h₁ h₂⟩
    · intro h₂
      have ⟨hx, np⟩ : (∃ x, ¬p x) := (forall_negation α p).mp h₂
      exact ⟨hx, fun hp => absurd hp np⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  · intro ⟨hx, h⟩ hr
    exact ⟨hx, h hr⟩
  · intro h
    apply (em r).elim
    · intro hr
      have ⟨hx, hp⟩ := h hr
      exact ⟨hx, fun _ => hp⟩
    · intro nr
      exact ⟨a, fun hr => absurd hr nr⟩

end ex4_5

end ex1

-- Exercise 2
--
-- Use tactic combinators to obtain a one line proof of the following:
namespace ex2

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by simp [*]

end ex2
