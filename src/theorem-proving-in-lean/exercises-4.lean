/- Exercises 4.6
 -
 - Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/
import data.int.basic
import data.nat.basic
import data.real.basic

-- Exercise 1
--
-- Prove these equivalences. You should also try to understand why the reverse
-- implication is not derivable in the last example.
section ex_1

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  iff.intro
    ( assume h,
      and.intro
        (assume x, and.left (h x))
        (assume x, and.right (h x)))
    (assume ⟨h₁, h₂⟩ x, ⟨h₁ x, h₂ x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume h₁ h₂ x,
  have px : p x, from h₂ x,
  h₁ x px

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume h₁ x,
  h₁.elim
    (assume h₂, or.inl (h₂ x))
    (assume h₂, or.inr (h₂ x))

-- The implication in the above example cannot be proven in the other direction
-- because it may be the case predicate `p x` holds for certain values of `x`
-- but not others that `q x` may hold for (and vice versa).

end ex_1

-- Exercise 2
--
-- It is often possible to bring a component of a formula outside a universal
-- quantifier, when it does not depend on the quantified variable. Try proving
-- these (one direction of the second of these requires classical logic).
section ex_2

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) :=
  assume ha,
  iff.intro (assume h, h ha) (assume hr ha, hr)

-- Ensure we do not use classical logic in the first or third subproblems.
section

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (assume h₁, or.elim (classical.em r)
      (assume hr, or.inr hr)
      (assume nr, or.inl (λ (x : α), or.elim (h₁ x)
        (assume hp, hp)
        (assume hr, absurd hr nr))))
    (assume h₁, or.elim h₁
      (assume h₂, (λ (x : α), or.inl (h₂ x)))
      (assume hr, (λ (x : α), or.inr hr)))
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  iff.intro
    (assume h₁ hr hx, h₁ hx hr)
    (assume h₁ hx hr, h₁ hr hx)

end ex_2

-- Exercise 3
--
-- Consider the "barber paradox," that is, the claim that in a certain town
-- there is a (male) barber that shaves all and only the men who do not shave
-- themselves. Prove that this is a contradiction.
section ex_3

open classical

variables (men : Type*) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
    have b : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
    or.elim (classical.em (shaves barber barber))
      (assume b', absurd b' (iff.elim_left b b'))
      (assume b', absurd (iff.elim_right b b') b')

end ex_3

-- Exercise 4
--
-- Remember that, without any parameters, an expression of type `Prop` is just
-- an assertion. Fill in the definitions of `prime` and `Fermat_prime` below,
-- and construct each of the given assertions. For example, you can say that
-- there are infinitely many primes by asserting that for every natural number
-- `n`, there is a prime number greater than `n.` Goldbach’s weak conjecture
-- states that every odd number greater than `5` is the sum of three primes.
-- Look up the definition of a Fermat prime or any of the other statements, if
-- necessary.
section ex_4

def prime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ (m : ℕ), (1 < m ∧ m < n) → n % m ≠ 0

def infinitely_many_primes : Prop :=
  ∀ (n : ℕ), (∃ (m : ℕ), m > n ∧ prime m)

def Fermat_prime (n : ℕ) : Prop :=
  ∃ (m : ℕ), n = 2^(2^m) + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ (n : ℕ), (∃ (m : ℕ), m > n ∧ Fermat_prime m)

def goldbach_conjecture : Prop :=
  ∀ (n : ℕ), even n ∧ n > 2 → (∃ (x y : ℕ), prime x ∧ prime y ∧ x + y = n)

def Goldbach's_weak_conjecture : Prop :=
  ∀ (n : ℕ), odd n ∧ n > 5 → (∃ (x y z : ℕ), prime x ∧ prime y ∧ prime z ∧ x + y + z = n)

def Fermat's_last_theorem : Prop :=
  ∀ (n : ℕ), n > 2 → (∀ (a b c : ℕ), a^n + b^n ≠ c^n)

end ex_4

-- Exercise 5
--
-- Prove as many of the identities listed in Section 4.4 as you can.
section ex_5

open classical

variables (α : Type*) (p q : α → Prop)
variables r s : Prop

example : (∃ x : α, r) → r :=
  assume ⟨hx, hr⟩,
  hr

example (a : α) : r → (∃ x : α, r) :=
  assume hr,
  exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume ⟨hx, ⟨hp, hr⟩⟩, ⟨exists.intro hx hp, hr⟩)
    (assume ⟨⟨hx, hp⟩, hr⟩, exists.intro hx ⟨hp, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
    (assume ⟨hx, hpq⟩, hpq.elim
      (assume hp, or.inl (exists.intro hx hp))
      (assume hq, or.inr (exists.intro hx hq)))
    (assume h, h.elim
      (assume ⟨hx, hp⟩, exists.intro hx (or.inl hp))
      (assume ⟨hx, hq⟩, exists.intro hx (or.inr hq)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  iff.intro
    (assume h ⟨hx, np⟩, np (h hx))
    (assume h hx, classical.by_contradiction (
      assume np,
      h (exists.intro hx np)
    ))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  iff.intro
    (assume ⟨hx, hp⟩ h, absurd hp (h hx))
    (assume h, classical.by_contradiction (
      assume h',
      h (λ (x : α), assume hp, h' (exists.intro x hp))
    ))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (assume h hx hp, h (exists.intro hx hp))
    (assume h ⟨hx, hp⟩, absurd hp (h hx))

lemma forall_negation : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (assume h, classical.by_contradiction (
      assume h',
      h (λ (x : α), classical.by_contradiction (
        assume np,
        h' (exists.intro x np)
      ))
    ))
    (assume ⟨hx, np⟩ h, absurd (h hx) np)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  forall_negation α p

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    (assume h ⟨hx, hp⟩, h hx hp)
    (assume h hx hp, h ⟨hx, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (assume ⟨hx, hp⟩ h, hp (h hx))
    (assume h₁, or.elim (classical.em (∀ x, p x))
      (assume h₂, exists.intro a (assume hp, h₁ h₂))
      (assume h₂,
        have h₃ : (∃ x, ¬p x), from iff.elim_left (forall_negation α p) h₂,
        match h₃ with
          ⟨hx, hp⟩ := exists.intro hx (assume hp', absurd hp' hp)
        end))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (assume ⟨hx, hrp⟩ hr, exists.intro hx (hrp hr))
    (assume h, or.elim (classical.em r)
      (assume hr, match h hr with
        ⟨hx, hp⟩ := exists.intro hx (assume hr, hp)
      end)
      (assume nr, exists.intro a (assume hr, absurd hr nr)))

end ex_5

-- Exercise 6
--
-- Give a calculational proof of the theorem `log_mul` below.
section ex_6

variables log exp : real → real
variable log_exp_eq : ∀ x, log (exp x) = x
variable exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable exp_pos : ∀ x, exp x > 0
variable exp_add : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0) : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc log (x * y) = log (x * exp (log y)) : by rw (exp_log_eq hy)
             ... = log (exp (log x) * exp (log y)) : by rw (exp_log_eq hx)
             ... = log (exp (log x + log y)) : by rw exp_add
             ... = log x + log y : by rw log_exp_eq

end ex_6

-- Exercise 7
--
-- Prove the theorem below, using only the ring properties of ℤ enumerated in
-- Section 4.2 and the theorem `sub_self.`
section ex_7
#check sub_self

example (x : ℤ) : x * 0 = 0 :=
calc x * 0 = x * (x - x) : by rw (sub_self x)
       ... = x * x - x * x : by rw (mul_sub x x x)
       ... = 0 : by rw (sub_self (x * x))

end ex_7
