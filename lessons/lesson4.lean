def is_even (x: ℕ) : bool := x % 2 = 0
def positive (n: ℕ) : bool := n > 0
def uint32 (n: ℕ) : bool := n >= 0 ∧ n < 2^32

def positive' : ℕ → bool := λ n, n > 0 
#check positive'
#check λ n : ℕ, n > 0 
#reduce is_even 1
#reduce positive 0

theorem ttt {a b : ℕ}: a=b→ b=a := λ f, eq.symm f
