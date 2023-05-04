/-
Chapter 8

Induction and Recursion
-/

-- ========================================
-- Exercise 1
--
-- Open a namespace `Hidden` to avoid naming conflicts, and use the equation
-- compiler to define addition, multiplication, and exponentiation on the
-- natural numbers. Then use the equation compiler to derive some of their basic
-- properties.
-- ========================================

namespace ex1

def add : Nat → Nat → Nat
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul : Nat → Nat → Nat
  | _, Nat.zero => 0
  | m, Nat.succ n => add m (mul m n)

def exp : Nat → Nat → Nat
  | _, Nat.zero => 1
  | m, Nat.succ n => mul m (exp m n)

end ex1

-- ========================================
-- Exercise 2
--
-- Similarly, use the equation compiler to define some basic operations on lists
-- (like the reverse function) and prove theorems about lists by induction (such
-- as the fact that `reverse (reverse xs) = xs` for any list `xs`).
-- ========================================

namespace ex2

variable {α : Type _}

def reverse : List α → List α
  | [] => []
  | (head :: tail) => reverse tail ++ [head]

-- Proof of `reverse (reverse xs) = xs` shown in previous exercise.

end ex2

-- ========================================
-- Exercise 3
--
-- Define your own function to carry out course-of-value recursion on the
-- natural numbers. Similarly, see if you can figure out how to define
-- `WellFounded.fix` on your own.
-- ========================================

namespace ex3

def below {motive : Nat → Sort u} (t : Nat) : Sort (max 1 u) :=
  Nat.recOn t
    (zero := PUnit)
    (succ := fun n ih => PProd (PProd (motive n) ih) (PUnit : Sort (max 1 u)))

/--
A copied implementation of `Nat.brecOn` with the `motive` properly supplied.
Notice the `noncomputable` tag; the code generator does not support the `recOn`
recursor yet, for reasons I haven't fully understood yet. This thread touches on
the topic:

https://leanprover-community.github.io/archive/stream/270676-lean4/topic/code.20generator.20does.20not.20support.20recursor.html
-/
noncomputable def brecOn {motive : Nat → Sort u}
  (t : Nat) (F : (t : Nat) → @below motive t → motive t) : motive t :=
  (Nat.recOn t
    (motive := fun n => PProd
      (motive n)
      (Nat.recOn n PUnit fun n ih => PProd (PProd (motive n) ih) PUnit))
    (zero := { fst := F Nat.zero PUnit.unit, snd := PUnit.unit })
    (succ := fun n ih => {
      fst := F (Nat.succ n) { fst := ih, snd := PUnit.unit },
      snd := { fst := ih, snd := PUnit.unit }
    })).1

#check WellFounded.fix

end ex3

-- ========================================
-- Exercise 4
--
-- Following the examples in Section Dependent Pattern Matching, define a
-- function that will append two vectors. This is tricky; you will have to
-- define an auxiliary function.
-- ========================================

namespace ex4

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

namespace Vector

/--
As long we flip the indices in our type signature in the resulting summation,
there is no need for an auxiliary function.
-/
def append : Vector α m → Vector α n → Vector α (n + m)
  | nil, bs => bs
  | cons a as, bs => cons a (append as bs)

end Vector

end ex4

-- ========================================
-- Exercise 5
--
-- Consider the following type of arithmetic expressions. The ideSure, looks like RDS w
-- ========================================

namespace ex5

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

-- Here `sampleExpr` represents `(v₀ * 7) + (2 * v₁)`. Write a function that
-- evaluates such an expression, evaluating each `var n` to `v n`.

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

-- ----------------------------------------
-- Implement "constant fusion," a procedure that simplifies subterms like
-- `5 + 7` to `12`. Using the auxiliary function `simpConst`, define a function
-- "fuse": to simplify a plus or a times, first simplify the arguments
-- recursively, and then apply `simpConst` to try to simplify the result.
-- ----------------------------------------

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus e₁ e₂  => simpConst $ plus (fuse e₁) (fuse e₂)
  | times e₁ e₂ => simpConst $ times (fuse e₁) (fuse e₂)
  | e           => e

theorem simpConst_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  unfold simpConst
  repeat { unfold eval }
  match h : e with
  | const n
  | var n
  | plus  (const   _) (const _)
  | plus  (var     _) _
  | plus  (plus  _ _) _
  | plus  (times _ _) _
  | times (const   _) (const _)
  | times (var     _) _
  | times (plus  _ _) _
  | times (times _ _) _ => rfl
  | plus  _ (var     _)
  | plus  _ (plus  _ _)
  | plus  _ (times _ _)
  | times _ (var     _)
  | times _ (plus  _ _)
  | times _ (times _ _) => simp only
  

theorem fuse_eq (v : Nat → Nat)
  : ∀ e : Expr, eval v (fuse e) = eval v e := by
  intro e
  induction e with
  | const n | var n => unfold fuse; rfl
  | plus e₁ e₂ he₁ he₂ | times e₁ e₂ he₁ he₂ =>
    unfold fuse
    rw [simpConst_eq]
    unfold eval
    rw [he₁, he₂]

-- The last two theorems show that the definitions preserve the value.

end ex5
