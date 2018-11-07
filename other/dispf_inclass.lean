theorem all_nne : ∀ (α : Type 1) (p : α → Prop), 
    (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
begin
    assume α p,
        assume h,
        assume e,
        show false,
            apply exists.elim e,
                intros,
                have : p a := h a,
                show false, from a_1 this,
end

example : ¬ (∀ (X : Type), ∀ (p q : X → Prop),
    (∃ x, p x) ∧ (∃ x, q x) → ∃ x, p x ∧ q x) :=
begin
    assume h,
    have ne : ¬ ∃ X : Type, ¬ (∀ (p q : X → Prop),
    (∃ x, p x) ∧ (∃ x, q x) → ∃ x, p x ∧ q x),
        apply all_nne, assumption,
    
    have : ∃ X : Type, ¬ (∀ (p q : X → Prop),
    (∃ x, p x) ∧ (∃ x, q x) → ∃ x, p x ∧ q x),
        apply exists.intro ℕ,
        assume h2,
        have h3 : (∃ x, x = 0) ∧ (∃ x, x = 1) → 
                    (∃ x, x = 0 ∧ x = 1),
            from h2 (λ a, a = 0) (λ b, b = 1),
        have pfx0 : (∃ x, x = 0) := ⟨0, rfl⟩,
        have pfx1 : (∃ x, x = 1) := ⟨1, rfl⟩,
        have : (∃ x, x = 0 ∧ x = 1) := h3 ⟨pfx0, pfx1⟩,
        apply exists.elim this,
            intros x x0x1,
            have l : x = 0 := x0x1.1,
            have r : x = 1 := x0x1.2,
            have : 0 = 1 := eq.subst r (eq.symm l),
            show false, from nat.no_confusion this,
    contradiction,
end