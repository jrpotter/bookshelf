/- Exercises 7.10
 -
 - Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/
import data.nat.basic

-- Exercise 1
--
-- Try defining other operations on the natural numbers, such as multiplication,
-- the predecessor function (with `pred 0 = 0`), truncated subtraction (with
-- `n - m = 0` when `m` is greater than or equal to `n`), and exponentiation.
-- Then try proving some of their basic properties, building on the theorems we
-- have already proved.
--
-- Since many of these are already defined in Lean’s core library, you should
-- work within a namespace named hide, or something like that, in order to avoid
-- name clashes.
namespace ex_1

-- As defined in the book.
inductive nat : Type
| zero : nat
| succ : nat → nat

def add (m n : nat) : nat :=
nat.rec_on n m (λ k ak, nat.succ ak)

theorem add_zero (m : nat) : add m nat.zero = m := rfl
theorem add_succ (m n : nat) : add m n.succ = (add m n).succ := rfl

theorem zero_add (n : nat) : add nat.zero n = n :=
nat.rec_on n
  (add_zero nat.zero)
  (assume n ih,
    show add nat.zero (nat.succ n) = nat.succ n, from calc
      add nat.zero (nat.succ n) = nat.succ (add nat.zero n) : add_succ nat.zero n
                            ... = nat.succ n : by rw ih)

-- Additional definitions.
def mul (m n : nat) : nat :=
nat.rec_on n nat.zero (λ k ak, add m ak)

def pred (n : nat) : nat :=
nat.cases_on n nat.zero id

def sub (m n : nat) : nat :=
nat.rec_on n m (λ k ak, pred ak)

def exp (m n : nat) : nat :=
nat.rec_on n (nat.zero.succ) (λ k ak, mul m ak)

end ex_1

-- Exercise 2
--
-- Define some operations on lists, like a `length` function or the `reverse`
-- function. Prove some properties, such as the following:
--
-- a. `length (s ++ t) = length s + length t`
-- b. `length (reverse t) = length t`
-- c. `reverse (reverse t) = t`
section ex_2

open list

variable {α : Type*}

-- Additional theorems.
theorem length_sum (s t : list α) : length (s ++ t) = length s + length t :=
list.rec_on s
  (by rw [nil_append, length, zero_add])
  (assume hd tl ih, by rw [
    length,
    cons_append,
    length,
    ih,
    add_assoc,
    add_comm t.length,
    add_assoc
  ])

lemma cons_reverse (hd : α) (tl : list α)
  : reverse (hd :: tl) = reverse tl ++ [hd] :=
sorry

theorem length_reverse (t : list α) : length (reverse t) = length t :=
list.rec_on t
  (by unfold reverse reverse_core)
  (assume hd tl ih, begin
    unfold length,
    rw cons_reverse,
    rw length_sum,
    unfold length,
    rw zero_add,
    rw ih,
  end)

theorem reverse_reverse (t : list α) : reverse (reverse t) = t :=
list.rec_on t rfl (assume hd tl ih, sorry)

end ex_2

-- Exercise 3
--
-- Define an inductive data type consisting of terms built up from the following
-- constructors:
--
-- • `const n`, a constant denoting the natural number `n`
-- • `var n`, a variable, numbered `n`
-- • `plus s t`, denoting the sum of `s` and `t`
-- • `times s t`, denoting the product of `s` and `t`
--
-- Recursively define a function that evaluates any such term with respect to an
-- assignment of values to the variables.
namespace ex_3

inductive foo : Type*
| const : ℕ → foo
| var : ℕ → foo
| plus : foo → foo → foo
| times : foo → foo → foo

def value_at : ℕ → list ℕ → ℕ
| 0       vs := list.head vs
| i       [] := default
| (i + 1) vs := value_at i (list.tail vs)

-- The provided "variables" are supplied in a 0-indexed list.
def eval_foo : foo → list ℕ → ℕ
| (foo.const n) vs := n
| (foo.var n) vs := value_at n vs
| (foo.plus m n) vs := eval_foo m vs + eval_foo n vs
| (foo.times m n) vs := eval_foo m vs * eval_foo n vs

end ex_3

-- Exercise 4
--
-- Similarly, define the type of propositional formulas, as well as functions on
-- the type of such formulas: an evaluation function, functions that measure the
-- complexity of a formula, and a function that substitutes another formula for
-- a given variable.
namespace ex_4

inductive foo : Type*
| tt : foo
| ff : foo
| and : foo → foo → foo
| or : foo → foo → foo

def eval_foo : foo → bool
| foo.tt := true
| foo.ff := false
| (foo.and lhs rhs) := eval_foo lhs ∧ eval_foo rhs
| (foo.or lhs rhs) := eval_foo lhs ∨ eval_foo rhs

def complexity_foo : foo → ℕ
| foo.tt := 1
| foo.ff := 1
| (foo.and lhs rhs) := 1 + complexity_foo lhs + complexity_foo rhs
| (foo.or lhs rhs) := 1 + complexity_foo lhs + complexity_foo rhs

def substitute : foo → foo := sorry

end ex_4

-- Exercise 5
--
-- Simulate the mutual inductive definition of `even` and `odd` described in
-- Section 7.9 with an ordinary inductive type, using an index to encode the
-- choice between them in the target type.
section ex_5

end ex_5
