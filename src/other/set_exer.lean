import data.set
import data.list
open set
open classical

variable U : Type
variables A B C D : set U

-- 1.
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        split,
        cases h,
            left, assumption,
            right, exact h.1,
        cases h,
            left, assumption,
            right, exact h.2,
        
        assume h,
        have xinAB : x ∈ (A ∪ B) := h.1,
        have xinAC : x ∈ (A ∪ C) := h.2,
        cases xinAB with xinA xinB,
            left, assumption,
            cases xinAC with xinA xinC,
                left, assumption,
                right, exact ⟨xinB, xinC⟩
end

-- 2.
example : -(A \ B) = -A ∪ B :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        cases em (x ∈ B) with xinB xnotinB,
            right, assumption,

            left,
            assume xinA,
            have : x ∈ A \ B := ⟨xinA, xnotinB⟩,
            contradiction,

        assume h,
        assume xinAnotB,
        cases h,
            have : x ∈ A := xinAnotB.1,
            contradiction,

            have : x ∉ B := xinAnotB.2,
            contradiction
end

-- Question 3 see set_exer2.lean

-- 4.
example : (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        split,
            cases h,
                left, exact h.1,
                right, exact h.1,
            
            assume xinAandB,
            cases h,
                exact h.2 xinAandB.2,
                exact h.2 xinAandB.1,
        
        assume h,
        have : ¬ x ∈ (A ∩ B) := h.2,
        cases h.1 with xinA xinB,
            left,
            split,
                assumption,
                assume xinB,
                have : x ∈ (A ∩ B) := ⟨xinA, xinB⟩,
                contradiction,

            right,
            split, 
                assumption,
                assume xinA,
                have : x ∈ (A ∩ B) := ⟨xinA, xinB⟩,
                contradiction,
end

-- 5. Part I
example : A \ (B ∪ C) = (A \ B) \ C :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        split,
            split,
                exact h.1,

                assume xinB,
                have : x ∈ (B ∪ C) := or.inl xinB,
                exact h.2 this,

            assume xinC,
            have : x ∈ (B ∪ C) := or.inr xinC,
            exact h.2 this,

        assume h,
        split,
            exact h.1.1,

            assume xinBorC,
            cases xinBorC with xinB xinC,
                exact h.1.2 xinB,
                exact h.2 xinC,
end

-- 5. Part II
example : C \ D = C ∩ -D :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        assumption,

        assume h,
        assumption,
end

-- 6.
example : (A \ B) ∪ (A ∩ B) = A :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        cases h,
            exact h.1,
            exact h.1,
        
        assume xinA,
        cases em (x ∈ B) with xinB xnotinB,
            right, exact ⟨xinA, xinB⟩,
            left, exact ⟨xinA, xnotinB⟩,
end

-- 7. (1)
example : A \ B = A \ (A ∩ B) :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        split,
            exact h.1,

            assume xinAandB,
            have : x ∉ B := h.2,
            exact this xinAandB.2,
        
        assume h,
        split,
            exact h.1,

            assume : x ∈ B,
            have : x ∈ (A ∩ B) := ⟨h.1, this⟩,
            have : x ∉ (A ∩ B) := h.2,
            contradiction,
end

-- 7. (2)
example : A \ B = (A ∪ B) \ B :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        split,
            left, exact h.1,
            exact h.2,
        
        assume h,
        split,
            cases h.1,
                assumption,
                have : x ∉ B := h.2,
                contradiction,
            exact h.2,
end

-- 7. (3)
example : (A ∩ B) \ C = (A \ C) ∩ B :=
begin
    apply ext,
    assume x,
    split,
        repeat {
            assume h,
            cases h,
            cases h_left,
                    repeat {split, repeat {assumption}},
        }    
end

-- 8 & 9. Note: theorems are from set_exer2.lean
section
    variables {I J : Type}

    theorem Inter.intro {I : Type} {A : I → set U} 
    {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
    by simp; assumption

    @[elab_simple]
    theorem Inter.elim {I : Type} {A : I → set U} 
    {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
    by simp at h; apply h

    theorem Union.intro {I : Type} {A : I → set U} 
    {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
    by {simp, existsi i, exact h}

    theorem Union.elim {I : Type} {A : I → set U} {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
    by {simp at h₁, cases h₁ with i h, exact h₂ i h}

    example : ∀ {A : I → J → set U},
    (⋃ i, ⋂ j, A i j) ⊆ (⋂ j, ⋃ i, A i j) :=
    begin
        intros,
        assume x,
        assume h,
        apply Union.elim U h,
            intros i this,
            apply Inter.intro U,
                assume j,
                apply Union.intro U i,
                    apply Inter.elim U this,
    end

    /-
    A counter-example of the reverse statement (⋂ j, ⋃ i, A i j) ⊆ (⋃ i, ⋂ j, A i j):

    let A be a array of array of sets of naturals defined below
    [[{1}, {2}],
     [{2}, {3}]]
    So A : ℕ → ℕ → set ℕ is indexed by I J : list ℕ := [0, 1]
    ⋂ j, ⋃ i, A i j = ({1} ∪ {2}) ∩ ({2} ∪ {3}) = {2}
    ⋃ i, ⋂ j, A i j = ({1} ∩ {2}) ∪ ({2} ∩ {3}) = ∅

    if (⋂ j, ⋃ i, A i j) ⊆ (⋃ i, ⋂ j, A i j), then {2} ⊆ ∅, which is not true.

    I actually don't know the correct way to create an indexed set, 
    so I used a complicated workaround to finish the proof in Lean
    -/

    -- define Aij as a list of list of sets of naturals
    def Aij : list (list (set ℕ)) := [[{1}, {2}],
                                     [{2}, {3}]]

    -- define a function that converts booleans to 0 and 1
    def bool_to_nat : bool → ℕ
    | tt := 1
    | ff := 0

    -- define A'' as a set indexed by two boolean values
    -- in this case, i and j can take only two possible values, namely ff and tt,
    -- corresponding to indices 0 and 1
    def A'' : bool → bool → set ℕ :=
    begin
        assume i j,
        -- How to get the nth element from a list? I actually don't know.
        -- The following way works anyway
        have : list (set ℕ),
            exact option.iget (Aij.nth (bool_to_nat i)),
        exact option.iget (this.nth (bool_to_nat j)),
    end

    -- Now, A'' tt ff is the element at the second row and first column of A'',
    -- which is {2}, or in Lean's notation, λ (b : ℕ), b = 2 ∨ false
    #reduce A'' tt ff

    example : ∃ {I : Type} {J : Type} {U : Type} {A : I → J → set U}, ¬
    ((⋂ j, ⋃ i, A i j) ⊆ (⋃ i, ⋂ j, A i j)) :=
    begin
        apply exists.intro bool,
        apply exists.intro bool,
        apply exists.intro ℕ,
        apply exists.intro A'',
        assume h,
        have : 2 ∈ (⋂ j, ⋃ i, A'' i j),
            assume s,
            assume z,
            apply exists.elim z,
                intros j a_1,
                rw a_1,
                cases j,
                    apply Union.intro ℕ tt,
                        left, trivial,
                    apply Union.intro ℕ ff,
                        left, trivial,

        have : 2 ∈ (⋃ i, ⋂ j, A'' i j),
            from h this,
            
        apply Union.elim ℕ this,    
            assume i,
            assume h2,
            have h3 : 2 ∈ A'' i tt,
                apply Inter.elim ℕ h2,
            have h4 : 2 ∈ A'' i ff,
                apply Inter.elim ℕ h2,
            cases i,
                repeat {cases h4},
                repeat {cases h3},
    end

    example : ∀ {A : I → set U} {B : J → set U},
    (⋃ i, A i) ∩ (⋃ j, B j) = ⋃ i, ⋃ j, (A i ∩ B j) :=
    begin
        intros,
        apply ext,
            assume x,
            split,
                assume h,
                cases h,
                apply Union.elim U h_left,
                    intros i xinAi,
                    apply Union.elim U h_right,
                        intros j xinBj,
                        apply Union.intro U i,
                            apply Union.intro U j,
                                split,
                                    assumption,
                                    assumption,

                assume h,
                apply Union.elim U h,
                    intros i _,
                    apply Union.elim U a,
                        intros j xinAiBj,
                        split,
                            apply Union.intro U i,
                                exact xinAiBj.1,
                        
                            apply Union.intro U j,
                                 exact xinAiBj.2,
    end
end

-- 10.
example : ∀ a b c d e f: Type, ((a, b, c) = (d, e, f)) ↔ a = d ∧ b = e ∧ c = f :=
begin
    intros,
    split,
        assume h,
        cases h,
        repeat {split},
        
        assume h,
        apply prod.ext,
            exact h.1,
            apply prod.ext,
                exact h.2.1,
                exact h.2.2,
end

-- Use set.prod to replace the built-in operator "×", because 
-- the default × does not represent the Cartesian product between two sets
local infix `×` : 50 := set.prod

-- 11.
example : A × (B ∪ C) = (A × B) ∪ (A × C) :=
begin
    apply ext,
    assume x,
    split,
        assume h,
        cases h,
        cases h_right,
            left,
            exact ⟨h_left, h_right⟩,

            right,
            exact ⟨h_left, h_right⟩,
        
        assume h,
        cases h,
            exact ⟨h.1, or.inl h.2⟩,
            exact ⟨h.1, or.inr h.2⟩,
end

-- 12.
example : (A ∩ B) × (C ∩ D) = (A × C) ∩ (B × D) :=
begin
    apply ext,
    assume x,
        split,
            assume h,
            split,
                cases h,
                exact ⟨h_left.1, h_right.1⟩,

                cases h,
                exact ⟨h_left.2, h_right.2⟩,
            
            assume h,
            cases h,
            cases h_left,
            cases h_right,
            repeat {split, 
                    repeat {assumption}},
end

-- 13. See set_exer2

-- some extra ones
example : A = B ↔ (A ∩ -B) = ∅ ∧ (-A ∩ B) = ∅ :=
begin
    split,
        assume aeqb,
        split,
            repeat {            
                apply ext,
                assume x,
                split,
                    assume h,
                    rw aeqb at h,
                    cases h,
                    contradiction,
                
                    assume h,
                    exact false.elim h,
            },

            assume h,
            cases h,
            apply ext,
            assume x,
            split,
                assume xina,
                cases em (x ∈ B) with xinb xninb,
                    assumption,
                    have h2 := ((set.ext_iff (A ∩ -B) ∅).1 h_left x).1,
                    have : x ∈ A ∩ (-B) := ⟨xina, xninb⟩,
                    exact false.elim (h2 this),
                
                assume xinb,
                cases em (x ∈ A) with xina xnina,
                    assumption,
                    have h2 := ((set.ext_iff (-A ∩ B) ∅).1 h_right x).1,
                    have : x ∈ -A ∩ B := ⟨xnina, xinb⟩,
                    exact false.elim (h2 this),
end

#check @set.prod
#check set.ext