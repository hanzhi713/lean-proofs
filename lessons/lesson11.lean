def isEven : ℕ → Prop := λ n, ∃ m : ℕ, m * 2 = n

lemma eightIsEven : isEven 8 :=
begin
    unfold isEven,
    exact ⟨4, dec_trivial⟩,
end

-- def isNonZ : ℕ → Prop := λ n, n ≠ 0

def isnonz : Prop := ∃ n : ℕ, n ≠ 0

lemma isNonZ : isnonz := ⟨1, dec_trivial⟩

lemma isNonZ' : isnonz :=
begin
    apply exists.intro 1,
    assume : 1 = 0,
    show false, from nat.no_confusion this,
end

example : ∀ {P S : ℕ → Prop}, 
    (∃ n : ℕ, P n ∧ S n) → (∃ n : ℕ, S n ∧ P n) :=
begin
    assume P S,
    assume ex,
    apply exists.elim ex,
        assume x,
        assume px_sx,
        apply exists.intro x,
            apply and.comm.mpr,
            assumption,
end

example : ∀ {P S : ℕ → Prop}, 
    (∃ n : ℕ, P n ∧ S n) → (∃ n : ℕ, S n ∧ P n) :=
begin
    assume P S,
    assume ex,
    apply exists.elim ex,
        assume x,
        assume px_sx,
        apply exists.intro x,
            apply and.intro,
                exact px_sx.2,
                exact px_sx.1,
end

def isSquare : ℕ → Prop := λ n, ∃ m : ℕ, n * n = m

example : isSquare 9 := ⟨81, dec_trivial⟩

example : isSquare 9 :=
begin
    apply exists.intro 81,
    apply rfl
end
