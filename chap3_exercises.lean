variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    begin
        assume npornq,
        assume pandq,
        cases npornq with np nq,
            show false, from np pandq.1,
            show false, from nq pandq.2
    end

example : ¬(p ∧ ¬p) :=
    begin
        assume h,
        show false, from h.2 h.1
    end

example : p ∧ ¬q → ¬(p → q) := 
    begin
        assume pandnotq,
        assume ptoq,
        have q := ptoq pandnotq.1,
        show false, from pandnotq.2 q
    end

example : ¬p → (p → q) := 
    begin
        assume notp,
        assume p,
        show q, from false.elim (notp p)
    end

example : (¬p ∨ q) → (p → q) := 
    begin
        assume notporq,
        assume p,
        cases notporq with notp pfq,
            show q, from false.elim (notp p),
            show q, from pfq
    end

example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : ¬(p ↔ ¬p) := sorry
example : (p → q) → (¬q → ¬p) := 
    begin
        assume pq,
        assume notq,
        assume pfp,
        have pfq : q := pq pfp,
        show false, from notq pfq
    end

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

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
    assume notPandQ,
    cases em p with pfP pfnotP,
    cases em q with pfQ pfnotQ,
    show ¬p ∨ ¬q, from false.elim (notPandQ (and.intro pfP pfQ)),
    show ¬p ∨ ¬q, from or.inr pfnotQ,
    show ¬p ∨ ¬q, from or.inl pfnotP,
end

example : ¬(p → q) → p ∧ ¬q := sorry

example : (p → q) → (¬p ∨ q) := sorry

example : (¬q → ¬p) → (p → q) := sorry
theorem pf_by_contrapositive: (¬q → ¬p) → (p → q) := 
    begin
        assume nqnp: ¬q → ¬p,
        assume pfP,
        have nnq : ¬q → false :=
            begin 
                assume nq : ¬q,
                have np : ¬p := nqnp nq,
                show false, from np pfP
            end,
        show q, from double_neg_elim nnq
    end

#check pf_by_contrapositive

example : p ∨ ¬p := 
    begin
        apply em
    end

example : (((p → q) → p) → p) := 
begin
    assume pqp,
    cases em p with pfp pfnp,
    cases em q with pfq pfnq,
        show p, from pfp,
        show p, from pfp,
        have n: ¬q → ¬p :=
            λ nq, pfnp,
        have pq : p → q := pf_by_contrapositive p q n,
        show p, from pqp pq
end

-- double negation elimination to axiom of excluded middle
theorem DNEtoEM : (∀ P, ¬¬P → P) → (∀ P, P ∨ ¬P) :=
begin
    assume notnotPtoP P,
    have non_contra_em :  P → ¬¬(P ∨ ¬P) :=
        begin
            assume p: P,
            assume np: ¬ (P ∨ ¬ P),
            have f : P ∨ ¬P := or.intro_left (¬P) p,
            show false, from np f
        end,
    have duo_neg_elim_em : ¬¬(P ∨ ¬P) → P ∨ ¬P := notnotPtoP (P ∨ ¬P),
    have notnot_em : ¬¬(P ∨ ¬P) := non_contradictory_em P,
    show P ∨ ¬P, from duo_neg_elim_em notnot_em
end