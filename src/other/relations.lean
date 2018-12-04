import data.set
import data.nat.basic

section question1and2
/-
Suppose < is a strict partial order on a domain A, 
and define a≤b to mean that a<b or a=b.

Show that ≤ is a partial order.
Show that if < is moreover a strict total order, then ≤ is a total order.
-/

parameters {A : Type} {R : A → A → Prop}
parameter (irreflR : irreflexive R)
parameter (transR : transitive R)

local infix < := R

def R' (a b : A) : Prop := R a b ∨ a = b
local infix ≤ := R'

include transR irreflR
theorem partialR : reflexive R' ∧ transitive R' ∧ anti_symmetric R' :=
begin
    split,
        assume a,
        right,
        trivial,

        split,
            assume a b c,
            assume ab,
            assume bc,
            cases ab,
                cases bc,
                    left,
                    exact transR ab bc,

                    left, 
                    rw ←bc,
                    assumption,

                    rw ab,
                    assumption,
            
            assume a b,
            assume h1 h2,
            cases h1,
                cases h2,
                    apply false.elim,
                        apply irreflR,
                            apply transR,
                                exact h1,
                                exact h2,
                            
                    exact eq.symm h2,
                assumption,
end

example : ∀ a b : A, (a < b) ∨ (a = b) ∨ (b < a) → a ≤ b ∨ b ≤ a :=
begin
    assume a b,
    assume h,
    cases h,
        left, left, assumption,
        cases h,
            left, right, assumption,
            right, left, assumption
end

/-
Suppose < is a strict partial order on a domain A. 
(In other words, it is transitive and asymmetric.) 
Suppose that ≤ is defined so that a≤b if and only if a<b or a=b. 
We saw in class that ≤ is a partial order on a domain A, 
i.e.~it is reflexive, transitive, and antisymmetric.

Prove that for every a and b in A, 
we have a<b iff a≤b and a≠b, using the facts above.
-/

example : ∀ a b, a < b ↔ a ≤ b ∧ a ≠ b :=
begin
    have partR := partialR,
    assume a b,
    split,
        assume h,
        split,
            left, assumption,

            assume ne,
            apply irreflR,
                rw ne at h,
                exact h,
        
        assume h,
        cases h.1,
            assumption,
            exact absurd h_1 h.2,
end

end question1and2

section question4
    parameters (T : Type) (R : T → T → Prop)
    parameter (reflR : reflexive R)
    parameter (symmR : symmetric R)
    parameter (transR : transitive R)

    local infix ≡ := R

    def equiv_class : T → set T := λ a, {c | R a c}

    local notation `[`a`]` : 50 := (equiv_class a)

    include reflR symmR transR
    theorem equiv' : ∀ a b, [a] = [b] ↔ a ≡ b :=
    begin
        assume a b,
        split,
            assume h,
            
            have : ∀ x : T, (x ∈ equiv_class a) ↔ (x ∈ equiv_class b),
                apply (set.ext_iff (equiv_class a) (equiv_class b)).1, assumption,

            apply (this b).2,
            apply reflR,
            
            assume h,
            apply set.ext,
                assume x,
                split,
                    assume h1,
                    apply transR,
                    exact symmR h,
                    assumption,

                    assume h1,
                    apply transR,
                    assumption,
                    assumption,
    end

    example : ∀ a b, [a] = [b] ↔ a ≡ b :=
        assume a b : T,
        iff.intro 
            (
                assume h : [a] = [b],
                have this : ∀ x : T, (x ∈ [a]) ↔ (x ∈ [b]), from
                    (set.ext_iff [a] [b]).1 h,
                show a ≡ b, from (this b).2 (reflR b)
            )
            (
            assume h : a ≡ b,
            show [a] = [b], from set.ext (
                assume x : T,
                iff.intro 
                    (
                        assume h1 : x ∈ [a],
                        show x ∈ [b], from transR (symmR h) h1
                    )
                    (
                        assume h1 : x ∈ [b],
                        show x ∈ [a], from transR h h1
                    )
                )
            )

end question4


section question7

/-
A binary relation ≤ on a domain A is said to be a preorder it is is reflexive and transitive. 
This is weaker than saying it is a partial order; 
we have removed the requirement that the relation is asymmetric. 
An example is the ordering on people currently alive on the planet defined by setting x≤y if and only if x ‘s birth date is earlier than y ‘s. 
Asymmetry fails, because different people can be born on the same day.
 But, prove that the following theorem holds:

Theorem. Let ≤ be a preorder on a domain A. 
Define the relation ≡, where x≡y holds if and only if x≤y and y≤x. 
Then ≡ is an equivalence relation on A.
-/

parameter {A : Type}
parameter {R : A → A → Prop}
parameter (transR : transitive R)
parameter (reflR : reflexive R)
local infix ≤ := R

def R'' (a b : A) : Prop := a ≤ b ∧ b ≤ a

local infix ≡ := R''

include reflR transR
example : reflexive R'' ∧ symmetric R'' ∧ transitive R'' :=
begin
    split,
        assume a,
        split,
            apply reflR,
            apply reflR,
        
        split,
            assume a b,
            assume h,
            cases h with ab ba,
            split,
                assumption,
                assumption,
            
            assume a b c,
            assume ab bc,
            cases ab with ab ba,
            cases bc with bc cb,
            split,
                apply transR,
                    exact ab,
                    assumption,
                apply transR,
                    exact cb,
                    assumption,
end

end question7
