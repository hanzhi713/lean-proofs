example : ∀ Q, true ∨ Q := 
    λ Q, 
        or.inl true.intro

#check @or.elim

example : ∀ P, false ∨ P ↔ P :=
begin
    assume P,
    apply iff.intro,
        assume forp,
        cases forp with pff pfp,
            show P, from false.elim pff,
            assumption,
        
        apply or.inr
end
