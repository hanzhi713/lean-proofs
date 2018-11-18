def f : ℕ → ℕ := λ x, x - 1 
theorem zneqo : ¬ 0 = 1 := 
    begin
        assume h : (0 = 1),
        show false,
        from nat.no_confusion h
    end
theorem oneqt : 1 ≠ 2 :=
begin
    assume h: 1 = 2,
    have zeqo : 0 = 1 := congr_arg f h,
    show false, from zneqo zeqo
end

theorem oneqt' : 1 ≠ 2.

theorem oneqt'' : 1 ≠ 2 := dec_trivial

theorem oneqt''' : 1 ≠ 2 :=
begin
    assume h,
    cases h,
end