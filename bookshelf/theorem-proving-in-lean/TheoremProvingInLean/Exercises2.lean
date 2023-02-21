/-
# References

1. Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/

-- Exercise 1
--
-- Define the function `Do_Twice`, as described in Section 2.4.
namespace ex1

def double (x : Nat) := x + x
def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def doTwiceTwice (f : (Nat → Nat) → (Nat → Nat)) (x : Nat → Nat) := f (f x)

#reduce doTwiceTwice doTwice double 2

end ex1

-- Exercise 2
--
-- Define the functions `curry` and `uncurry`, as described in Section 2.4.
namespace ex2

def curry (f : α × β → γ) : (α → β → γ) :=
  fun α β => f (α, β)

def uncurry (f : α → β → γ) : (α × β → γ) :=
  fun x => f x.1 x.2

end ex2

-- Exercise 3
--
-- Above, we used the example `vec α n` for vectors of elements of type `α` of
-- length `n`. Declare a constant `vec_add` that could represent a function that
-- adds two vectors of natural numbers of the same length, and a constant
-- `vec_reverse` that can represent a function that reverses its argument. Use
-- implicit arguments for parameters that can be inferred. Declare some
-- variables and check some expressions involving the constants that you have
-- declared.
namespace ex3

universe u
axiom vec : Type u → Nat → Type u

namespace vec

axiom empty : ∀ (α : Type u), vec α 0
axiom cons : ∀ (α : Type u) (n : Nat), α → vec α n → vec α (n + 1)
axiom append : ∀ (α : Type u) (n m : Nat), vec α m → vec α n → vec α (n + m)
axiom add : ∀ {α : Type u} {n : Nat}, vec α n → vec α n → vec α n
axiom reverse : ∀ {α : Type u} {n : Nat}, vec α n → vec α n

end vec

-- Check results.
variable (a b : vec Prop 1)
variable (c d : vec Prop 2)

#check vec.add a b
-- #check vec.add a c
#check vec.reverse a

end ex3

-- Exercise 4
--
-- Similarly, declare a constant `matrix` so that `matrix α m n` could represent
-- the type of `m` by `n` matrices. Declare some constants to represent
-- functions on this type, such as matrix addition and multiplication, and
-- (using vec) multiplication of a matrix by a vector. Once again, declare some
-- variables and check some expressions involving the constants that you have
-- declared.
namespace ex4

universe u
axiom matrix : Type u → Nat → Nat → Type u

namespace matrix

axiom add : ∀ {α : Type u} {m n : Nat},
  matrix α m n → matrix α m n → matrix α m n
axiom mul : ∀ {α : Type u} {m n p : Nat},
  matrix α m n → matrix α n p → matrix α m p
axiom app : ∀ {α : Type u} {m n : Nat},
  matrix α m n → ex3.vec α n → ex3.vec α m

end matrix

variable (a b : matrix Prop 5 7)
variable (c : matrix Prop 7 3)
variable (d : ex3.vec Prop 3)

#check matrix.add a b
-- #check matrix.add a c
#check matrix.mul a c
#check matrix.app c d

end ex4
