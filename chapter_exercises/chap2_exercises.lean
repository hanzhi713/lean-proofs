-- Exercise 1
-- Define the function Do_Twice, as described in Section 2.4.
def double_ (a: ℕ ) : ℕ := a + a
def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x

def times2plus1 : ℕ → ℕ := λ x, x * 2 + 1

def do_twice_ (f: ℕ → ℕ ) (x: ℕ ) : ℕ := f (f x)
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
def do_third_times : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f (f x))

#check do_twice
#reduce do_third_times square 2 -- 256
#reduce do_twice square 2 -- 16

def quadruple : ℕ → ℕ := λ x, do_twice double x

#reduce quadruple 2 -- 8

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → ℕ → ℕ := λ f g x, f g (f g x)

/- Equivalent forms -/
def Do_Twice_ (f: (ℕ → ℕ) → (ℕ → ℕ)) : (ℕ → ℕ) → ℕ → ℕ := λ g x, f g (f g x)
def Do_Twice' (f: (ℕ → ℕ) → (ℕ → ℕ)) (x: ℕ → ℕ) : ℕ → ℕ := f (f x)
def Do_Twice'' : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → ℕ → ℕ := λ f g, f (f g)

#reduce Do_Twice do_twice double 2
#reduce Do_Twice do_twice times2plus1 2 
#reduce Do_Twice do_third_times times2plus1 2
#eval Do_Twice_ do_twice square 2

#reduce do_third_times square 2
#eval Do_Twice do_third_times square 2
#eval Do_Twice do_twice square 2


-- Exercise 2
-- Define the functions curry and uncurry, as described in Section 2.4.
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def curry (α β γ : Type): (α × β → γ) → α → β → γ := λ f a b, f (a, b)

def uncurry (α β γ : Type): (α → β → γ) → α × β → γ := λ f ⟨a, b⟩, f a b


-- Exercise 3
-- Above, we used the example vec α n for vectors of elements 
-- of type α of length n. Declare a constant vec_add that could 
-- represent a function that adds two vectors of natural numbers 
-- of the same length, and a constant vec_reverse that can represent 
-- a function that reverses its argument. 
-- Use implicit arguments for parameters that can be inferred. 
-- Declare some variables and check some expressions involving 
-- the constants that you have declared.

universe u
constant vec : Type u → ℕ → Type u

namespace vec
    constant empty : Π α : Type u, vec α 0
    constant cons :
        Π {α : Type u} {n : ℕ}, α → vec α n → vec α (n + 1)
    constant append :
        Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
end vec

constant vec_add :
    Π {m : ℕ},  vec ℕ m → vec ℕ m → vec ℕ m

constant vec_reverse :
    Π {α : Type u} {m : ℕ}, vec α m → vec α m

variable vecA : vec ℕ 4
variable vecB : vec ℕ 4
variable vecC : vec ℕ 5
#check vec_add vecA vecB
#check vec_reverse vecA
#check vec_add (vec.cons 1 vecA) vecC


-- Exercise 4
-- Similarly, declare a constant matrix so that matrix α m n could 
-- represent the type of m by n matrices. Declare some constants 
-- to represent functions on this type, such as matrix addition and 
-- multiplication, and (using vec) multiplication of a matrix by a vector. 
-- Once again, declare some variables and check some expressions involving 
-- the constants that you have declared.

constant matrix : Type u → ℕ → ℕ → Type u

namespace matrix
    constant empty : Π α : Type u, matrix α 0 0
    constant add : 
        Π {α : Type u} {m n : ℕ}, 
            matrix α m n → matrix α m n → matrix α m n
    constant multiply : 
        Π {α : Type u} {m n p: ℕ}, 
            matrix α m n → matrix α n p → matrix α m p
    constant multiply_by_vec :
        Π {α : Type u} {m n: ℕ}, 
            matrix α m n → vec α n → vec α m
end matrix

variable matA : matrix ℕ 5 4
variable matB : matrix ℕ 4 3
variable matC : matrix ℕ 4 3

#check matrix.add matB matC
#check matrix.multiply matA matB
#check matrix.multiply_by_vec matA vecA
