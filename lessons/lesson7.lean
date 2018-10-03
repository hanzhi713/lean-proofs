open classical

theorem double_neg_elim: ∀ { P }, ¬¬P → P := 
begin
  assume P : Prop,
  assume pfNotNotP : ¬¬P,
  cases em P with pfP pfnP,
    show P, from pfP,

    have f: false := pfNotNotP pfnP,
    show P, from false.elim f
end

theorem double_neg_elim': ∀ {P}, (P ∨ ¬P) → ¬¬P → P :=
begin
    assume P: Prop,
    assume h: P ∨ ¬P,
    assume notnotP: ¬¬P,
    cases h with a b,
        show P, from a,
        show P, from false.elim (notnotP b),
end

theorem p_b_c' : ∀ P: Prop, (¬P → false) → P := λ P nnP, double_neg_elim nnP

theorem proof_by_contrapositive: 
    ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    begin
        assume P Q: Prop,
        assume nqnp: (¬ Q → ¬ P),
        assume p : P,
        have nnq : ¬ Q → false :=
            begin 
                assume nq : ¬Q,
                have np : ¬P := nqnp nq,
                show false, from np p
            end,
        show Q, from double_neg_elim nnq
    end

theorem proof_by_contrapositive': 
    ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    begin
        assume P Q: Prop,
        assume nqnp: (¬ Q → ¬ P),
        assume p : P,
        have nnq : ¬ Q → false :=
            λ nq : ¬Q, nqnp nq p,
        show Q, from double_neg_elim nnq
    end

theorem proof_by_contrapositive''''': 
    ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    begin
        assume (P Q: Prop) (nqnp: ¬ Q → ¬ P) (p: P),
        exact double_neg_elim (λ nq : ¬Q, nqnp nq p)
    end

theorem proof_by_contrapositive'''': 
    ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    begin
        assume P Q: Prop,
        assume nqnp: (¬ Q → ¬ P),
        assume p : P,
        exact double_neg_elim (λ nq : ¬Q, nqnp nq p)
    end

theorem proof_by_contrapositive'': ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    λ (P Q : Prop) (nqnp : ¬ Q → ¬ P) (p: P), 
        double_neg_elim (λ nq : ¬ Q, nqnp nq p)

theorem proof_by_contrapositive''': ∀ P Q : Prop, (¬ Q → ¬ P) → (P → Q) :=
    λ P Q nqnp p, double_neg_elim (λ nq, nqnp nq p)

theorem z: ∀ { a }, ¬¬a → a := 
λ a b,
begin
  cases em a with c d,
    exact c,
    exact false.elim (b d)
end

variable k: Prop
#check em k
#check or.by_cases
#check or.cases_on

theorem double_neg_elim'': ∀ {a}, ¬¬a → a := 
λ a b, or.cases_on (em a) (λ a, a) (λ c, false.elim (b c))

example {P: Prop} (a: ¬¬P) : double_neg_elim a = double_neg_elim'' a := rfl

theorem j: ∀ a b : Prop, (¬ b → ¬ a) → (a → b) :=
    λ a b c d, z (λ e, c e d)


variables P Q: Prop
variable q : Q -- proof of Q
example : P → Q := λ p : P, q
example : P → Q := assume p : P, q

-- def prime (p : ℕ) := p ≥ 2 ∧ ∀ n, n | p → n = 1 ∨ n = p