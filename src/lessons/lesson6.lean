axiom excluded_middle : ∀ P: Prop, P ∨ ¬ P
#check excluded_middle

theorem double_neg_elim: ∀ P: Prop, ¬ ¬ P → P := 
begin
  assume P : Prop,
  assume pfNotNotP : ¬ ¬ P,
  cases excluded_middle P,
    -- case 1: 
    show P, from h,

    have f: false := pfNotNotP h,
    exact false.elim f
end

theorem nat_eq : ∀ (n : nat), ∀ (m : nat), 
    m = n ∨ m ≠ n := 
begin
    assume n m: nat,
    cases excluded_middle (m=n) with h1 h2,
        exact or.inl h1,
        exact or.inr h2
end

open classical
theorem nat_eq' : ∀ (n : nat), ∀ (m : nat), 
    m = n ∨ m ≠ n := 
begin
    assume n m: nat,
    cases em (m=n),
        exact or.inl h,
        exact or.inr h
end


theorem double_neg_elim'': ∀ {P}, (P ∨ ¬P) → ¬¬P → P :=
begin
    assume P: Prop,
    assume h: P ∨ ¬P,
    assume notnotP: ¬¬P,
    cases h with a b,
        show P, from a,
        show P, from false.elim (notnotP b),
end

theorem p_b_c' : ∀ P: Prop, (¬P → false) → P :=
begin
    intro P,
    assume nnp: ¬P → false,
    have a := double_neg_elim P nnp,
    exact a
end

theorem p_b_c'' : ∀ P: Prop, (¬P → false) → P := double_neg_elim