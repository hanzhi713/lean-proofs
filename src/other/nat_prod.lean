import .odd_and_even_nat


example : ∀ a b, odd a → even b → even (a * b) :=
begin
    assume a b,
    assume odda,
    assume evenb,
    cases odda,
    cases evenb,
        rw odda_h,
        rw evenb_h,

        apply exists.intro ((2 * odda_w + 1) * evenb_w),
            rw ←(mul_assoc 2),
            rw mul_comm 2 (2 * odda_w + 1),
            rw mul_assoc,
end