/-! # Exercises.Avigad.Chapter4

Quantifiers and Equality
-/

/-! #### Exercise 1

Prove these equivalences. You should also try to understand why the reverse
implication is not derivable in the last example.
-/

namespace Exercises.Avigad.Chapter4

namespace ex1

variable (α : Type _)
variable (p q : α → Prop)

theorem forall_and
  : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h => ⟨fun x => And.left (h x), fun x => And.right (h x)⟩)
    (fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩)

theorem forall_imp_distrib
  : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h₁ h₂ x =>
    have px : p x := h₂ x
    h₁ x px

theorem forall_or_distrib
  : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h₁ x => h₁.elim
    (fun h₂ => Or.inl (h₂ x))
    (fun h₂ => Or.inr (h₂ x))

-- The implication in the above example cannot be proven in the other direction
-- because it may be the case predicate `p x` holds for certain values of `x`
-- but not others that `q x` may hold for (and vice versa).

end ex1

/-! #### Exercise 2

It is often possible to bring a component of a formula outside a universal
quantifier, when it does not depend on the quantified variable. Try proving
these (one direction of the second of these requires classical logic).
-/

namespace ex2

variable (α : Type _)
variable (p q : α → Prop)
variable (r : Prop)

theorem self_imp_forall : α → ((∀ _ : α, r) ↔ r) :=
  fun a => Iff.intro (fun h => h a) (fun hr _ => hr)

section

open Classical

theorem forall_or_right : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h₁ => (em r).elim
      Or.inr
      (fun nr => Or.inl (fun x => (h₁ x).elim id (absurd · nr))))
    (fun h₁ => h₁.elim
      (fun h₂ x => Or.inl (h₂ x))
      (fun hr _ => Or.inr hr))

end

theorem forall_swap : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h hr hx => h hx hr)
    (fun h hx hr => h hr hx)

end ex2

/-! #### Exercise 3

Consider the "barber paradox," that is, the claim that in a certain town there
is a (male) barber that shaves all and only the men who do not shave themselves.
Prove that this is a contradiction.
-/

namespace ex3

open Classical

variable (men : Type _)
variable (barber : men)
variable (shaves : men → men → Prop)

theorem barber_paradox (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False :=
  have b : shaves barber barber ↔ ¬shaves barber barber := h barber
  (em (shaves barber barber)).elim
    (fun b' => absurd b' (Iff.mp b b'))
    (fun b' => absurd (Iff.mpr b b') b')

end ex3

/-! #### Exercise 4

Remember that, without any parameters, an expression of type `Prop` is just an
assertion. Fill in the definitions of `prime` and `Fermat_prime` below, and
construct each of the given assertions. For example, you can say that there are
infinitely many primes by asserting that for every natural number `n`, there is
a prime number greater than `n.` Goldbach’s weak conjecture states that every
odd number greater than `5` is the sum of three primes. Look up the definition
of a Fermat prime or any of the other statements, if necessary.
-/

namespace ex4

def even (a : Nat) := ∃ b, a = 2 * b

def odd (a : Nat) := ¬even a

def prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ (m : Nat), (1 < m ∧ m < n) → n % m ≠ 0

def infinitelyManyPrimes : Prop :=
  ∀ (n : Nat), (∃ (m : Nat), m > n ∧ prime m)

def FermatPrime (n : Nat) : Prop :=
  ∃ (m : Nat), n = 2^(2^m) + 1

def infinitelyManyFermatPrimes : Prop :=
  ∀ (n : Nat), (∃ (m : Nat), m > n ∧ FermatPrime m)

def GoldbachConjecture : Prop :=
  ∀ (n : Nat), even n ∧ n > 2 →
    ∃ (x y : Nat), prime x ∧ prime y ∧ x + y = n

def Goldbach'sWeakConjecture : Prop :=
  ∀ (n : Nat), odd n ∧ n > 5 →
    ∃ (x y z : Nat), prime x ∧ prime y ∧ prime z ∧ x + y + z = n

def Fermat'sLastTheorem : Prop :=
  ∀ (n : Nat), n > 2 → (∀ (a b c : Nat), a^n + b^n ≠ c^n)

end ex4

/-! #### Exercise 5

Prove as many of the identities listed in Section 4.4 as you can.
-/

namespace ex5

open Classical

variable (α : Type _)
variable (p q : α → Prop)
variable (r s : Prop)

theorem exists_imp : (∃ _ : α, r) → r :=
  fun ⟨_, hr⟩ => hr

theorem exists_intro (a : α) : r → (∃ _ : α, r) :=
  fun hr => ⟨a, hr⟩

theorem exists_and_right : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨hx, ⟨hp, hr⟩⟩ => ⟨⟨hx, hp⟩, hr⟩)
    (fun ⟨⟨hx, hp⟩, hr⟩ => ⟨hx, ⟨hp, hr⟩⟩)

theorem exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨hx, hpq⟩ => hpq.elim
      (fun hp => Or.inl ⟨hx, hp⟩)
      (fun hq => Or.inr ⟨hx, hq⟩))
    (fun h => h.elim
      (fun ⟨hx, hp⟩ => ⟨hx, Or.inl hp⟩)
      (fun ⟨hx, hq⟩ => ⟨hx, Or.inr hq⟩))

theorem forall_iff_not_exists : (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
  Iff.intro
    (fun h ⟨hx, np⟩ => np (h hx))
    (fun h hx => byContradiction
      fun np => h ⟨hx, np⟩)

theorem exists_iff_not_forall : (∃ x, p x) ↔ ¬(∀ x, ¬p x) :=
  Iff.intro
    (fun ⟨hx, hp⟩ h => absurd hp (h hx))
    (fun h => byContradiction
      fun h' => h (fun (x : α) hp => h' ⟨x, hp⟩))

theorem not_exists : (¬∃ x, p x) ↔ (∀ x, ¬p x) :=
  Iff.intro
    (fun h hx hp => h ⟨hx, hp⟩)
    (fun h ⟨hx, hp⟩ => absurd hp (h hx))

theorem forall_negation : (¬∀ x, p x) ↔ (∃ x, ¬p x) :=
  Iff.intro
    (fun h => byContradiction
      fun h' => h (fun (x : α) => byContradiction
        fun np => h' ⟨x, np⟩))
    (fun ⟨hx, np⟩ h => absurd (h hx) np)

theorem not_forall : (¬∀ x, p x) ↔ (∃ x, ¬p x) :=
  forall_negation α p

theorem forall_iff_exists_imp : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h ⟨hx, hp⟩ => h hx hp)
    (fun h hx hp => h ⟨hx, hp⟩)

theorem exists_iff_forall_imp (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨hx, hp⟩ h => hp (h hx))
    (fun h₁ => (em (∀ x, p x)).elim
      (fun h₂ => ⟨a, fun _ => h₁ h₂⟩)
      (fun h₂ =>
        have h₃ : (∃ x, ¬p x) := Iff.mp (forall_negation α p) h₂
        match h₃ with
        | ⟨hx, hp⟩ => ⟨hx, fun hp' => absurd hp' hp⟩))

theorem exists_self_iff_self_exists (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨hx, hrp⟩ hr => ⟨hx, hrp hr⟩)
    (fun h => (em r).elim
      (fun hr => match h hr with
                 | ⟨hx, hp⟩ => ⟨hx, fun _ => hp⟩)
      (fun nr => ⟨a, fun hr => absurd hr nr⟩))

end ex5

/-! #### Exercise 6

Give a calculational proof of the theorem `log_mul` below.
-/

namespace ex6

variable (log exp : Float → Float)
variable (log_exp_eq : ∀ x, log (exp x) = x)
variable (exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x)
variable (exp_pos : ∀ x, exp x > 0)
variable (exp_add : ∀ x y, exp (x + y) = exp x * exp y)

theorem exp_add_mul_exp (x y z : Float)
  : exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

theorem exp_log_eq_self (y : Float) (h : y > 0)
  : exp (log y) = y := exp_log_eq h

theorem log_mul {x y : Float} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
  calc log (x * y)
    _ = log (x * exp (log y)) := by rw [exp_log_eq hy]
    _ = log (exp (log x) * exp (log y)) := by rw [exp_log_eq hx]
    _ = log (exp (log x + log y)) := by rw [exp_add]
    _ = log x + log y := by rw [log_exp_eq]

end ex6

end Exercises.Avigad.Chapter4