/-! # Avigad.Chapter7

Inductive Types
-/

namespace Avigad.Chapter7

/-! ### Exercise 1

Try defining other operations on the natural numbers, such as multiplication,
the predecessor function (with `pred 0 = 0`), truncated subtraction (with
`n - m = 0` when `m` is greater than or equal to `n`), and exponentiation. Then
try proving some of their basic properties, building on the theorems we have
already proved.

Since many of these are already defined in Lean’s core library, you should work
within a namespace named hide, or something like that, in order to avoid name
clashes.
-/

namespace ex1

-- As defined in the book.
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + Nat.zero = m :=
  rfl

theorem add_succ (m n : Nat) : m + n.succ = (m + n).succ :=
  rfl

theorem zero_add (n : Nat) : Nat.zero + n = n :=
Nat.recOn (motive := fun x => Nat.zero + x = x)
  n
  (show Nat.zero + Nat.zero = Nat.zero from rfl)
  (fun (n : Nat) (ih : Nat.zero + n = n) =>
    show Nat.zero + n.succ = n.succ from
    calc
      Nat.zero + n.succ
        = (Nat.zero + n).succ := add_succ Nat.zero n
      _ = n.succ := by rw [ih])

-- Additional definitions.
def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n => m + mul m n

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n => n

def sub (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => sub (pred m) n

def exp (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero.succ
  | Nat.succ n => mul m (exp m n)

end Nat

end ex1

/-! ### Exercise 2

Define some operations on lists, like a `length` function or the `reverse`
function. Prove some properties, such as the following:

a. `length (s ++ t) = length s + length t`

b. `length (reverse t) = length t`

c. `reverse (reverse t) = t`
-/

namespace ex2

variable {α : Type _}

theorem length_sum (s t : List α)
        : List.length (s ++ t) = List.length s + List.length t :=
  List.recOn s
    (by rw [List.nil_append, List.length, Nat.zero_add])
    (fun hd tl ih => by rw [
      List.length,
      List.cons_append,
      List.length,
      ih,
      Nat.add_assoc,
      Nat.add_comm t.length,
      Nat.add_assoc
    ])

theorem length_inject_anywhere (x : α) (as bs : List α)
        : List.length (as ++ [x] ++ bs) = List.length as + List.length bs + 1 := by
  induction as with
  | nil => simp
  | cons head tail ih => calc
      List.length (head :: tail ++ [x] ++ bs)
        = List.length (tail ++ [x] ++ bs) + 1 := rfl
      _ = List.length tail + List.length bs + 1 + 1 := by rw [ih]
      _ = List.length tail + (List.length bs + 1) + 1 := by rw [Nat.add_assoc (List.length tail)]
      _ = List.length tail + (1 + List.length bs) + 1 := by rw [Nat.add_comm (List.length bs)]
      _ = List.length tail + 1 + List.length bs + 1 := by rw [Nat.add_assoc (List.length tail) 1]
      _ = List.length (head :: tail) + List.length bs + 1 := rfl

theorem list_reverse_aux_append (as bs : List α)
        : List.reverseAux as bs = List.reverse as ++ bs := by
  induction as generalizing bs with
  | nil => rw [List.reverseAux, List.reverse, List.reverseAux, List.nil_append]
  | cons head tail ih => calc
      List.reverseAux (head :: tail) bs
        = List.reverseAux tail (head :: bs) := rfl
      _ = List.reverse tail ++ (head :: bs) := by rw [ih]
      _ = List.reverse tail ++ ([head] ++ bs) := rfl
      _ = List.reverse tail ++ [head] ++ bs := by rw [List.append_assoc]
      _ = List.reverseAux tail [head] ++ bs := by rw [ih]
      _ = List.reverseAux (head :: tail) [] ++ bs := rfl

theorem length_reverse (t : List α)
        : List.length (List.reverse t) = List.length t := by
  induction t with
  | nil => simp
  | cons head tail ih => calc
      List.length (List.reverse (head :: tail))
        = List.length (List.reverseAux tail [head]) := rfl
      _ = List.length (List.reverse tail ++ [head]) := by rw [list_reverse_aux_append]
      _ = List.length (List.reverse tail) + List.length [head] := by simp
      _ = List.length tail + List.length [head] := by rw [ih]
      _ = List.length tail + 1 := rfl
      _ = List.length [] + List.length tail + 1 := by simp
      _ = List.length ([] ++ [head] ++ tail) := by rw [length_inject_anywhere]
      _ = List.length (head :: tail) := rfl

theorem reverse_reverse_aux (as bs : List α)
        : List.reverse (as ++ bs) = List.reverse bs ++ List.reverse as := by
  induction as generalizing bs with
  | nil => simp
  | cons head tail ih => calc
      List.reverse (head :: tail ++ bs)
        = List.reverseAux (head :: tail ++ bs) [] := rfl
      _ = List.reverseAux (tail ++ bs) [head] := rfl
      _ = List.reverse (tail ++ bs) ++ [head] := by rw [list_reverse_aux_append]
      _ = List.reverse bs ++ List.reverse tail ++ [head] := by rw [ih]
      _ = List.reverse bs ++ (List.reverse tail ++ [head]) := by rw [List.append_assoc]
      _ = List.reverse bs ++ (List.reverseAux tail [head]) := by rw [list_reverse_aux_append]
      _ = List.reverse bs ++ (List.reverseAux (head :: tail) []) := rfl
      _ = List.reverse bs ++ List.reverse (head :: tail) := rfl

theorem reverse_reverse (t : List α)
        : List.reverse (List.reverse t) = t := by
  induction t with
  | nil => simp
  | cons head tail ih => calc
      List.reverse (List.reverse (head :: tail))
        = List.reverse (List.reverseAux tail [head]) := rfl
      _ = List.reverse (List.reverse tail ++ [head]) := by rw [list_reverse_aux_append]
      _ = List.reverse [head] ++ List.reverse (List.reverse tail) := by rw [reverse_reverse_aux]
      _ = List.reverse [head] ++ tail := by rw [ih]
      _ = [head] ++ tail := by simp
      _ = head :: tail := rfl

end ex2

/-! ### Exercise 3

Define an inductive data type consisting of terms built up from the following
constructors:

• `const n`, a constant denoting the natural number `n`

• `var n`, a variable, numbered `n`

• `plus s t`, denoting the sum of `s` and `t`

• `times s t`, denoting the product of `s` and `t`

Recursively define a function that evaluates any such term with respect to an
assignment of values to the variables.
-/

namespace ex3

inductive Foo : Type _
  | const : Nat → Foo
  | var : Nat → Foo
  | plus : Foo → Foo → Foo
  | times : Foo → Foo → Foo

def value_at : Nat → List Nat → Nat
| _,       [] => default
| 0,       vs => List.head! vs
| (i + 1), vs => value_at i (List.tail! vs)

-- The provided "variables" are supplied in a 0-indexed list.
def eval_foo : Foo → List Nat → Nat
  | (Foo.const n)  , _  => n
  | (Foo.var n)    , vs => value_at n vs
  | (Foo.plus m n) , vs => eval_foo m vs + eval_foo n vs
  | (Foo.times m n), vs => eval_foo m vs * eval_foo n vs

end ex3

end Avigad.Chapter7
