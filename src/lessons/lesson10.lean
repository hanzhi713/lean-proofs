def alwaysTrue : ℕ → Prop := λ n, n ≥ 0

def alwaysFalse : ℕ → Prop := λ n, n < 0

inductive day : Type
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday
| Saturday
| Sunday

#check day.Tuesday

open day -- no longer need to day. prefix

#check Tuesday


-- Answer

def isWeekend : day → Prop :=
    λ d, d = Saturday ∨ d = Sunday

theorem satIsWeekend : isWeekend Saturday :=
begin
    unfold isWeekend,
    apply or.inl,
    apply rfl
end

theorem satIsWeekend' : isWeekend Saturday := or.inl (eq.refl Saturday)

def set01 : ℕ → Prop := λ n, n = 0 ∨ n = 1

def set215 : ℕ → Prop := λ n, 2 ≤ n ∧ n ≤ 15

def setpos : ℕ → Prop := λ n, n > 0

def haha : (ℕ × ℕ) → Prop := λ ⟨a, b⟩, a = b

def isSquare : ℕ → ℕ → Prop := λ a b, a ^2 = b

lemma true39 : isSquare 3 9 := eq.refl 9

def sHasLengthN : string → ℕ → Prop := λ s n, string.length s = n

