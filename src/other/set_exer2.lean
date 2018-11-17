import data.set
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

-- Question 3 see set_exer.lean

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

-- 5. Part II (I used A and B instead of C and D)
example : A \ B = A ∩ -B :=
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
example : (A ∩ B) × (C ∩ D)=(A × C) ∩ (B × D) :=
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

-- 13. See set_exer

#check @set.prod