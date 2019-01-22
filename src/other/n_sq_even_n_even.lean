import .odd_and_even_nat

example : ∀ n:ℕ, even (n * n) ↔ even(n) :=
begin
    assume n,
    split,
        assume h,
        apply exists.elim h,
        assume a h1,

        apply classical.by_contradiction,
            assume noteven,
            have oddn := (not_even_odd n).1 noteven,
            apply exists.elim oddn,
            assume b h2,
            
            rw h2 at h1,
            rw add_mul at h1,
            rw mul_add at h1,
            rw one_mul at h1,
            rw mul_one at h1,
            rw ←mul_assoc at h1,
            simp at h1,
            rw (mul_assoc 2 b 2) at h1,
            rw mul_assoc at h1,
            rw ←(mul_add 2 b (b * 2 * b)) at h1,
            rw ←mul_add at h1,
            rw (mul_comm b 2) at h1,
            have o : odd (1 + 2 * (b + (b + 2 * b * b))),
                apply exists.intro ((b + (b + 2 * b * b))),
                    rw add_comm,
                
            rw h1 at o,
            have e : even (2*a) := ⟨a, rfl⟩,
            have := not_both_even_and_odd (2*a),
            have : even (2*a) ∧ odd (2*a) := ⟨e, o⟩,
            contradiction,

        assume h,
        apply exists.elim h,
            assume a h1,
            rw h1,
            apply exists.intro (a * (2 * a)),
                rw mul_assoc,
                -- QED
end

#check eq.to_iff