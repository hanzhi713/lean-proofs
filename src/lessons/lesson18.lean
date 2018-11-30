def fn1 (n : ℕ) := n + 1

def fn1' : set ℕ := {n : ℕ | ∃ x, n = x + 1}
def fn1'' : set (ℕ×ℕ) := {tuple | tuple.1 = tuple.2 + 1}

def fn2 (n : ℕ) (m : ℕ) := n / m
def fn2' : set (ℕ × ℕ × ℕ) := {tuple | tuple.1 / tuple.2.1 = tuple.2.2}

def fn3 (n : ℕ) (m : {a : ℕ // a ≠ 0}) := n / m
-- def fn3' : set (ℕ × ℕ × ℕ) := 

def c : Type := {a : ℕ // a ≠ 0}

example : c := 
begin
    split,
    show ℕ, from 1,
    assume h,
    show false, from nat.no_confusion h
end

namespace function_set_exercise2

  variable fn1: ℕ → ℕ
    def set1 : set (ℕ × ℕ) :=
        {tuple | tuple.2 = fn1 tuple.1}

  variable fn2: ℕ → ℕ → ℕ
    def set2 : set (ℕ × ℕ × ℕ) :=
        {tuple | tuple.2.2 = fn2 tuple.1 tuple.2.1}

  variable fn3: ℕ → ℕ → (ℕ × ℕ)
    def set3 : set (ℕ × ℕ × (ℕ × ℕ)) :=
        {tuple | tuple.2.2 = fn3 tuple.1 tuple.2.1}

end function_set_exercise2


def tupe3 : ℕ × ℕ × ℕ := (1,3,4)