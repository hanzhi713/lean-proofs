-- Exercise 1
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
begin
    apply iff.intro,
        assume forward,
        apply and.intro,
            assume x,
            show p x, from (forward x).1,

            assume x,
            show q x, from (forward x).2,
        
        assume backward,
        assume x,
        apply and.intro,
            show p x, from backward.1 x,
            show q x, from backward.2 x
end

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
begin
        assume forward,
        assume backward,
        assume a,
        exact forward a (backward a),
end

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
    assume forward,
    assume x,
    cases forward with px qx,
        show p x ∨ q x, from or.inl (px x),
        show p x ∨ q x, from or.inr (qx x)
end

-- Exercise 2
-- It is often possible to bring a component of a formula outside
-- a universal quantifier, when it does not depend on the quantified variable. 
-- Try proving these (one direction of the second of these requires classical logic):
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
begin
    assume a,
    apply iff.intro,
        assume ar,
        show r, from ar a,

        assume pfr a,
        show r, from pfr
end

section
    open classical
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    begin
        apply iff.intro,
            assume forward, 
            cases em r with pfr pfnr, -- this direction requires classical resoning
                show (∀ x, p x) ∨ r, from or.inr pfr,

                apply or.inl,
                    assume a,
                    have pa : p a ∨ r := forward a, 
                    cases pa with pfpa pfr,
                        show p a, from pfpa,
                        show p a, from false.elim (pfnr pfr),

            assume backward,
            assume a,
            cases backward with pfpx pfr,
                show p a ∨ r, from or.inl (pfpx a),
                show p a ∨ r, from or.inr pfr
    end
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
    apply iff.intro,
        assume forward,
        assume pfr,
        assume a,
        show p a, from forward a pfr,

        assume backward,
        assume a,
        assume pfr,
        show p a, from backward pfr a,
end

-- Exercise 3
-- Consider the “barber paradox,” that is, the claim that 
-- in a certain town there is a (male) barber that shaves all 
-- and only the men who do not shave themselves. 
-- Prove that this is a contradiction:
variables (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false 
    :=
    begin
        have h1 := h barber,
        -- same as the proof of ¬(p ↔ ¬p) in chap3 exercises
        have forward := iff.elim_left h1,
        have backward := iff.elim_right h1,
        have nf : ¬shaves barber barber := λ a, (forward a) a,
        show false, from nf (backward nf)
    end


--Exercise 4
-- Below, we have put definitions of divides and even in a 
-- special namespace to avoid conflicts with definitions in the library. 
-- The instance declaration make it possible to use the notation 
-- m | n for divides m n. Don’t worry about how it works; 
-- you will learn about that later.
namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
end

-- Remember that, without any parameters, an expression of 
-- type Prop is just an assertion. Fill in the definitions of prime 
-- and Fermat_prime below, and construct the given assertion. 
-- For example, you can say that there are infinitely many primes 
-- by asserting that for every natural number n, there is a prime number 
-- greater than n. Goldbach’s weak conjecture states that 
-- every odd number greater than 5 is the sum of three primes. 
-- Look up the definition of a Fermat prime or any of the other statements, 
-- if necessary.

def prime (n : ℕ) : Prop := n ≥ 2 ∧ ∀ x ∣ n, x = 1 ∨ x = n

def infinitely_many_primes : Prop := ∀ n, prime n → ∃ x, x > n

def Fermat_prime (n : ℕ) : Prop := ∀ n ≥ 0, prime (2 ^ 2 ^ n + 1) 

def infinitely_many_Fermat_primes : Prop := ∀ n, Fermat_prime n → ∃ x, x > n

def goldbach_conjecture : Prop := 
   ∀ n ≥ 2, even n → (∃ x y, prime x → prime y → n = x + y)

def Goldbach's_weak_conjecture : Prop :=
    ∀ n, ¬ (even n) → (∃ x y z, prime x → prime y → prime z → n = x + y + z)

def Fermat's_last_theorem : Prop := 
    ∀ n ≥ 3, ¬ (∃ x y z, x ≥ 1 → y ≥ 1 → z ≥ 1 → x^n + y^n = z^n)

end hidden

-- Exercise 5

open classical
variable a : α -- required in the second one and the last two


example : (∃ x : α, r) → r := 
begin
    assume : ∃ (x : α), r,
    apply exists.elim this,
    intros, assumption
end

section
    include a
    example : r → (∃ x : α, r) := 
    begin
        assume pfr,
        apply exists.intro a,
        assumption
    end
end

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
begin
    apply iff.intro,
        assume h,
        apply and.intro,
            apply exists.elim h,
                intros,
                exact ⟨a, a_1.1⟩,
            apply exists.elim h,
                intros,
                exact a_1.2,
        
        assume h,
        apply exists.elim h.1,
            intros,
            apply exists.intro a,
                apply and.intro,
                    assumption,
                    show r, from h.2
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin
    apply iff.intro,
        assume h,
        apply exists.elim h,
            intros,
            cases a_1,
                apply or.inl,
                    exact ⟨a, a_1⟩,
                apply or.inr,
                    exact ⟨a, a_1⟩,
        
        assume h,
        cases h with epx eqx,
            apply exists.elim epx,
                intros,
                apply exists.intro a,
                    exact or.inl a_1,
            
            apply exists.elim eqx,
                intros,
                apply exists.intro a,
                    exact or.inr a_1,
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
begin
    apply iff.intro,
        assume h,
        assume e,
        show false,
            apply exists.elim e,
                intros,
                have : p a := h a,
                show false, from a_1 this,

        intros h x,
        cases em (p x),
            assumption,

            have : ∃ (x : α), ¬ p x := ⟨x, h_1⟩,
            show p x, from absurd this h
end

theorem e_na_nt : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
begin
    apply iff.intro,
        assume h,
        assume f,
        apply exists.elim h,
            intros,
            have : ¬ p a, from f a,
            show false, from this a_1,
        
        assume h,
            apply by_contradiction, -- requires classical reasoning
                assume notE,
                have : ∀ (x : α), ¬ p x,
                    assume x,
                    assume px,
                    have : ∃ (x : α), p x,
                        from ⟨x, px⟩,
                    show false, from notE this,
                
                show false, from h this
end

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
begin
    apply iff.intro,
        assume h,
        assume a,
        assume pa,
        show false, from h ⟨a, pa⟩,

        assume h,
        assume e,
        apply exists.elim e,
            intros,
            have : ¬ p a, from h a,
            show false, from this a_1
end

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
begin
    apply iff.intro,
        assume h,
        apply by_contradiction,
            intros,
            have : ∀ (x : α), p x,
                assume x,
                apply by_contradiction,
                    assume npx,
                    have : ∃ (x : α), ¬p x, from ⟨x, npx⟩,
                    show false, from a this,
            show false, from h this,
                
        assume h,
        assume f,
        apply exists.elim h,
            intros,
            have : p a, from f a,
            show false, from a_1 this
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
begin
    apply iff.intro,
        assume h,
        assume e,
        apply exists.elim e,
            intros,
            have : p a → r, from h a,
            show r, from this a_1,
        
        assume e : (∃ (x : α), p x) → r,
        assume a,
        assume pa,
        have : (∃ (x : α), p x), from ⟨a, pa⟩,
        show r, from e this
end

-- copied from one of the chapter 3 exercises,
-- used in the proof of ((∀ x, p x) → r) → (∃ x, p x → r) 
theorem npq_pandnq : ∀ {p q : Prop}, ¬(p → q) → p ∧ ¬q :=
begin
    assume p q,
    assume notpq,
    apply and.intro,
        show ¬q,
            assume pfq,
            have pq : p → q := assume pfp, pfq,
            show false, from notpq pq,

        cases em p with pfp pfnp,
            assumption,
            have pq : p → q := 
                assume pfp, false.elim (pfnp pfp),
            show p, from false.elim (notpq pq)
end

include a
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
begin
    apply iff.intro,
        assume e f,
        apply exists.elim e,
            assume x, 
            assume pxr,
            have : p x, from f x,
            show r, from pxr this,

        -- this one is really hard
        assume h : (∀ (x : α), p x) → r,
            apply (e_na_nt α (λ x : α, p x → r)).mpr,
                assume k : ∀ (x : α), ¬(p x → r),
                have xpx: (∀ (x : α), p x),
                    assume x,
                    have : ¬(p x → r), from k x,
                    have : p x ∧ ¬r, from npq_pandnq this,
                    show p x, from this.1,
                have npar: ¬(p a → r), from k a,
                have pfr : r, from h xpx,
                have : p a → r, 
                    assume _, assumption,
                show false, from npar this
end

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
begin
    apply iff.intro,
        assume e,
        assume r,
        apply exists.elim e,
            assume x,
            assume rpx,
            have : p x, from rpx r,
            exact ⟨x, this⟩,
        
        assume re,
        cases em r with pfr pfnr,
            have : (∃ (x : α), p x), from re pfr,
            apply exists.elim this,
                assume x px,
                show ∃ (x : α), r → p x,
                    from ⟨x, assume r, px⟩,
            
            apply exists.intro a,
                assume pfr,
                show p a, from absurd pfr pfnr
end


-- Exercise 6
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
begin
    have z : exp (log (x * y)) = exp (log x + log y) :=
        calc
        exp (log (x * y)) = x * y : by rw exp_log_eq (mul_pos hx hy) 
        ... = exp (log x) * exp (log y) : by rw [exp_log_eq hx, exp_log_eq hy]
        ... = exp (log x + log y) : by rw exp_add,

    have pf : log (exp (log (x * y))) = log (exp (log x + log y)) :=
    congr_arg log z,

    have lhs := calc
        log (exp (log (x * y))) = log (x * y) : by rw log_exp_eq,

    have rhs := calc
        log (exp (log x + log y)) = log x + log y : by rw log_exp_eq,

    show log (x * y) = log x + log y, from calc
        log (x * y) = log x + log y : by rw [eq.symm(lhs), pf, rhs],
end


-- Exercise 7
-- Prove the theorem below, using only the 
-- ring properties of ℤ enumerated in Section 4.2 and the theorem sub_self.
#check sub_self

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = x * (x - x) : by rw sub_self
    ... = x * x - x * x : by rw mul_sub
    ... = 0 : by rw sub_self

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = 0 : by simp