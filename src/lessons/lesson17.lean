#check @reflexive
#check @symmetric
#check @transitive
#check @empty_relation
#check @irreflexive
#check @anti_symmetric
#check @total
#check @reflexive

namespace n
    section
        def ltgt : ℤ → ℤ → Prop := λ x y : ℤ, x < y ∧ y < x
        local infix `<<` : 50 := ltgt

        theorem ltgt_empty : ∀ (a b : ℤ), ¬ (ltgt a b) :=
        begin
            assume a b,
            assume h,
            have : a < a := lt.trans h.1 h.2,
            have : ¬ a < a := lt_irrefl a,
            contradiction
        end

        example : irreflexive ltgt :=
        begin
            assume x xx,
            have : x < x := lt.trans xx.1 xx.2,
            apply lt_irrefl x this,
        end

        example : irreflexive ltgt := λ x h, ltgt_empty x x h

        example : symmetric ltgt :=
        begin
            assume x y h,
            cases h,
            have : x < x := lt.trans h_left h_right,
            have : ¬ x < x := lt_irrefl x,
            contradiction
        end

        example : symmetric ltgt := λ x y h, false.elim (ltgt_empty x y h)

        example : transitive ltgt :=
        begin
            assume x y z xy yz,
            split,
                exact lt.trans xy.1 yz.1,
                exact lt.trans yz.2 xy.2,
        end

        example : transitive ltgt := λ x y z xy yz, false.elim (ltgt_empty x y xy)

        example : anti_symmetric ltgt :=
        begin
            assume x y xy yx,
            have xlty : x < y := xy.1,
            have yltx : y < x := xy.2,
            have xltx : x < x := lt.trans xlty yltx,
            have : ¬ x < x := lt_irrefl x,
            contradiction,
        end

        example : anti_symmetric ltgt := λ x y xy yx, false.elim (ltgt_empty x y xy)

        example : ¬ total ltgt :=
        begin
            assume h,
            have : 1 << 2 ∨ 2 << 1 := h 1 2,
            have t : ¬ (2 : ℤ) < 1 := dec_trivial,
            cases this,
                have : (2 : ℤ) < 1 := this.2,
                contradiction,

                have : (2 : ℤ) < 1 := this.1,
                contradiction
        end

        def connected {α : Type} : (α → α → Prop) → Prop := λ r, ∀ (x y : α), x ≠ y → r x y ∨ r y x
        
        example : ¬ connected ltgt :=
        begin
            assume h,
            have ne : (1 : ℤ) ≠ 2 := dec_trivial,
            have : 1<<2 ∨ 2<<1 := (h 1 2) ne,
            cases this,
                apply ltgt_empty 1 2 this,
                apply ltgt_empty 2 1 this,
        end
    end
end n
