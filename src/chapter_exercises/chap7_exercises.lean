import data.nat.sqrt

namespace hidden

/-
Try defining other operations on the natural numbers, 
such as multiplication, the predecessor function (with pred 0 = 0), 
truncated subtraction (with n - m = 0 when m is greater than or equal to n), 
and exponentiation. Then try proving some of their basic properties, 
building on the theorems we have already proved.

Since many of these are already defined in Lean’s core library, 
you should work within a namespace named hide, or something like that, in order to avoid name clashes.
-/

def add : ℕ → ℕ → ℕ
| nat.zero m := m
| (nat.succ n) m := nat.succ (add n m) 

#reduce add 3 5

def pred : ℕ → ℕ
| nat.zero := 0
| (nat.succ n) := n

def sub : ℕ → ℕ → ℕ 
| nat.zero m := 0
| (nat.succ n) m := sub n (pred m)

def mul : ℕ → ℕ → ℕ 
| nat.zero m := 0
| (nat.succ n) m := add m (mul n m)

def exp : ℕ → ℕ → ℕ
| m nat.zero := 1
| m (nat.succ n) := mul m (exp m n)

lemma add_zero : ∀ a, add a 0 = a :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw add,
    rw hk,
end

lemma zero_add : ∀ a, add 0 a = a :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw add,
end

lemma one_add : ∀ a, nat.succ a = add a 1 :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw add,
    rw hk,
end

lemma add_one : ∀ a, nat.succ a = add 1 a :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw add,
    rw hk,
    rw zero_add,
end

lemma pred_succ : ∀ a, pred (nat.succ a) = a :=
begin
    assume a,
    induction a with k hk,
    trivial,
    rw pred,
end

lemma add_n_succ_m : ∀ n m, 
    add n (nat.succ m) = nat.succ (add n m) :=
begin
    assume n m,
    induction n with k hk,
    trivial,

    rw add,
    rw add,
    rw hk,
end

lemma add_comm : ∀ a b, add a b = add b a :=
begin
    assume a b,
    induction a with ak hk,
    rw add_zero,
    trivial,

    rw add_n_succ_m,
    rw ←hk,
    rw add,
end

lemma add_assoc : ∀ a b c, 
    add a (add b c) = add (add a b) c :=
begin
    assume a b c,
    induction a with ak ah,
    trivial,

    rw add,
    rw add,
    rw add,
    rw ah,
end

lemma zero_mul : ∀ a, mul a 0 = 0 :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw mul,
    rw hk,
    trivial,
end

lemma mul_zero : ∀ a, mul 0 a = 0 :=
begin
    assume a,
    trivial,
end

lemma one_mul : ∀ a, mul 1 a = a :=
begin
    assume a,
    induction a with k hk,
    trivial,

    rw mul,
    rw add,
    rw mul_zero,
    rw add_zero,
end

#reduce exp 0 0

lemma exp_nonzero : ∀ a, exp 0 (nat.succ a) = 0 :=
begin
    assume a,
    rw exp,
    trivial,
end

lemma mul_n_succ_m : ∀ a b, 
    mul a (nat.succ b) = add a (mul a b) :=
begin
    assume a b,
    induction a with ak ah,
    trivial,

    simp [mul, add_comm, ah, add, add_assoc],
    -- rw mul,
    -- rw mul,
    -- rw add_comm,
    -- rw ah,
    -- rw add,
    -- rw add_n_succ_m,
    -- rw add_comm,
    -- rw add_assoc,
    -- rw add_assoc,
    -- rw (add_comm ak b),
end

lemma mul_comm : ∀ a b , mul a b = mul b a :=
begin
    assume a b,
    induction a with ak ah,
    rw zero_mul,
    rw mul_zero,

    simp [mul, mul_n_succ_m, add_comm, ah],
end

-- example : ∀ a b c, 
--     mul (exp a b) (exp a c) = exp a (add b c) :=
-- begin
--     assume a b c,
--     induction a,
--     induction b,
--     induction c,
--     trivial,


--     simp [exp, mul, add, exp_nonzero],
--     simp [exp, mul, add, exp_nonzero],
    
--     simp [exp, mul, add, exp_nonzero, add_comm, add_assoc],

-- end
#reduce mul 3 5
#reduce exp 2 6

end hidden
