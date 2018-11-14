example : ∃ P Q : Prop, (P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) :=
begin
    apply exists.intro false,
    apply exists.intro true,
    split,
        show false ∨ true, from or.inr true.intro,
        split,
            show ¬false ∨ ¬true,
            apply or.inl,
            assume f, assumption,
            show ¬false ∨ true, from or.inr true.intro,
end

example : ¬ ∃ P Q : Prop, (P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) ∧ (¬Q) :=
begin
    assume h,
    apply exists.elim h,
    intros,
    apply exists.elim a_1,
    intros,
    have na2 : ¬a_2 := a_3.2.2.2,

    cases a_3.1 with pfa pfa_2,
    cases a_3.2.1 with pfna pfna_2,
        exact pfna pfa,
    cases a_3.2.2.1 with pfna pfa_2,
        exact pfna pfa,
        exact na2 pfa_2,
        exact na2 pfa_2,
end

example : ∃ P Q R : Prop,(P ∨ Q ∨ R) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ Q ∨ R) ∧ (¬Q ∨ ¬R)
:= 
begin
    apply exists.intro true,
    apply exists.intro true,
    apply exists.intro false,
    split,
        exact or.inl true.intro,
        split,
            apply or.inr,
            apply or.inr,
            assume f, assumption,

            split,
                apply or.inr,
                apply or.inl,
                exact true.intro,

                apply or.inr,
                assume f, assumption         
end

