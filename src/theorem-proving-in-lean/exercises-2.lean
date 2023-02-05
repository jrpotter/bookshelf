/- Exercises 2.10
 -
 - Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
-/

-- Borrowed from the book.
def double (x : ℕ) : ℕ := x + x
def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

-- Exercise 1
--
-- Define the function `Do_Twice`, as described in Section 2.4.
section ex_1
def Do_Twice (f : (ℕ → ℕ) → (ℕ → ℕ)) (x : ℕ → ℕ)
  : (ℕ → ℕ) :=
f (f x)
end ex_1

-- Exercise 2
--
-- Define the functions `curry` and `uncurry`, as described in Section 2.4.
section ex_2
def curry (α β γ : Type*) (f : α × β → γ)
  : α → β → γ :=
λ α β, f (α, β)

def uncurry (α β γ : Type*) (f : α → β → γ)
  : α × β → γ :=
λ x, f x.1 x.2
end ex_2

-- Borrowed from the book.
universe u
constant vec : Type u → ℕ → Type u

namespace vec
constant empty : Π (α : Type u), vec α 0
constant cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
constant append : Π (α : Type u) (n m : ℕ), vec α m → vec α n → vec α (n + m)
end vec

-- Exercise 3
--
-- Above, we used the example `vec α n` for vectors of elements of type `α` of
-- length `n`. Declare a constant `vec_add` that could represent a function that
-- adds two vectors of natural numbers of the same length, and a constant
-- `vec_reverse` that can represent a function that reverses its argument. Use
-- implicit arguments for parameters that can be inferred. Declare some
-- variables and check some expressions involving the constants that you have
-- declared.
section ex_3

namespace vec
constant add :
  Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n
constant reverse :
  Π {α : Type u} {n : ℕ}, vec α n → vec α n
end vec

-- Check results.
variables a b : vec Prop 1
variables c d : vec Prop 2
#check vec.add a b
-- #check vec.add a c
#check vec.reverse a

end ex_3

-- Exercise 4
--
-- Similarly, declare a constant `matrix` so that `matrix α m n` could represent
-- the type of `m` by `n` matrices. Declare some constants to represent
-- functions on this type, such as matrix addition and multiplication, and
-- (using vec) multiplication of a matrix by a vector. Once again, declare some
-- variables and check some expressions involving the constants that you have
-- declared.
constant matrix : Type u → ℕ → ℕ → Type u

section ex_4

namespace matrix
constant add : Π {α : Type u} {m n : ℕ}, matrix α m n → matrix α m n → matrix α m n
constant mul : Π {α : Type u} {m n p : ℕ}, matrix α m n → matrix α n p → matrix α m p
constant app : Π {α : Type u} {m n : ℕ}, matrix α m n → vec α n → vec α m
end matrix

variables a b : matrix Prop 5 7
variable c : matrix Prop 7 3
variable d : vec Prop 3

#check matrix.add a b
-- #check matrix.add a c
#check matrix.mul a c
#check matrix.app c d

end ex_4
