variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
    apply iff.intro,
        assume pq,
        show q ∧ p, from and.intro pq.2 pq.1,

        assume qp,
        show p ∧ q, from and.intro qp.2 qp.1
end
example : p ∨ q ↔ q ∨ p :=
begin
    apply iff.intro,
        assume pq,
        cases pq with pfp pfq,
            show q ∨ p, from or.inr pfp,
            show q ∨ p, from or.inl pfq,
        
        assume qp,
        cases qp with pfq pfp,
            show p ∨ q, from or.inr pfq,
            show p ∨ q, from or.inl pfp
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
    apply iff.intro,
        assume pqr,
        show p ∧ (q ∧ r), from and.intro pqr.1.1 (and.intro pqr.1.2 pqr.2),

        assume pqr,
        show (p ∧ q) ∧ r, from and.intro (and.intro pqr.1 pqr.2.1) pqr.2.2
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
    apply iff.intro,
        assume pqr,
            cases pqr with pq pfr,
            cases pq with pfp pfq,
                show p ∨ (q ∨ r), from or.inl pfp,
                show p ∨ (q ∨ r), from or.inr (or.inl pfq),
                show p ∨ (q ∨ r), from or.inr (or.inr pfr),

        assume pqr,
            cases pqr with pfp qr,
                show (p ∨ q) ∨ r, from or.inl (or.inl pfp),
            cases qr with pfq pfr,
                show (p ∨ q) ∨ r, from or.inl (or.inr pfq),
                show (p ∨ q) ∨ r, from or.inr pfr
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
    apply iff.intro,
    assume pqr,
        have pfp := pqr.1,
        have qr := pqr.2,
        cases qr with pfq pfr,
            show (p ∧ q) ∨ (p ∧ r), from or.inl (and.intro pfp pfq),
            show (p ∧ q) ∨ (p ∧ r), from or.inr (and.intro pfp pfr),
    
    assume pqpr,
    cases pqpr with pq pr,
        have pfp := pq.1,
        have right := or.inl pq.2,
        show p ∧ (q ∨ r), from and.intro pfp right,

        have pfp := pr.1,
        have right := or.inr pr.2,
        show p ∧ (q ∨ r), from and.intro pfp right
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
    apply iff.intro,
    assume pqr,
        cases pqr with pfp qr,
            show (p ∨ q) ∧ (p ∨ r), from and.intro (or.inl pfp) (or.inl pfp),

            have pfq := qr.1,
            have pfr := qr.2,
            show (p ∨ q) ∧ (p ∨ r), from and.intro (or.inr pfq) (or.inr pfr),
    
    assume pqpr,
        have pq := pqpr.1,
        have pr := pqpr.2,
        cases pq with pfp pfq,
            show p ∨ (q ∧ r), from or.inl pfp,
        cases pr with pfp pfr,
            show p ∨ (q ∧ r), from or.inl pfp,
            show p ∨ (q ∧ r), from or.inr (and.intro pfq pfr)
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
    apply iff.intro,
        assume pqr,
        assume pq,
        show r, from pqr pq.1 pq.2,
    
        assume pqr,
        assume p q,
        show r, from pqr (and.intro p q),
end

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
    apply iff.intro,
        assume pqr,
        apply and.intro,
            assume p,
            show r, from pqr (or.inl p),

            assume q,
            show r, from pqr (or.inr q),
        
        assume pqr,
        have pr := pqr.1,
        have qr := pqr.2,
        assume pq,
        cases pq with pfp pfq,
            show r, from pr pfp,
            show r, from qr pfq
end

-- First Demorgan's law
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
    apply iff.intro,
        assume npq,
        apply and.intro,
            assume p,
            show false, from npq (or.inl p),

            assume q,
            show false, from npq (or.inr q),

        assume npnq,
        assume porq,
        cases porq with pfp pfq,
            show false, from npnq.1 pfp,
            show false, from npnq.2 pfq
end

-- Second Demorgan's law
-- This direction does not require classical reasoning
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

example : p ∨ false ↔ p :=
begin
    apply iff.intro,
        assume pfalse,
        cases pfalse with pfp pff,
            show p, from pfp,
            show p, from false.elim pff,
        
        assume pfp,
            show p ∨ false, from or.inl pfp
end

example : p ∧ false ↔ false :=
begin
    apply iff.intro,
        assume pf,
        show false, from pf.2,

        assume f,
        show p ∧ false, from and.intro (false.elim f) f
end

example : ¬(p ↔ ¬p) :=
begin
    assume h,
    have forward := iff.elim_left h,
    have backward := iff.elim_right h,

    have np : ¬p := assume p, (forward p) p,
    show false, from np (backward np)
end

theorem modus_tollens : (p → q) → (¬q → ¬p) := 
    begin
        assume pq,
        assume notq,
        assume pfp,
            have pfq : q := pq pfp,
            show false, from notq pfq
    end

-- an alternative proof to ¬(p ↔ ¬p)
theorem piffnpf : ¬(p ↔ ¬p) :=
begin
    apply iff.elim,
        assume pnp,
        assume npp,

        apply modus_tollens,
            exact npp,

            assume p, 
            show false, from (pnp p) p,

            assume p,
            show false, from (pnp p) p
end

-- these require classical reasoning
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

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
    assume prs,
    cases em p with pfp pfnp,
        have rs := prs pfp,
        cases rs with pfr pfs,
            apply or.inl,
                show p → r, from assume pfp, pfr,

            apply or.inr,
                show p → s, from assume pfp, pfs,

        apply or.inl,
            assume p,
            show r, from false.elim (pfnp p)
end

-- Second Demorgan's law, 
-- the direction that requires classical reasoning
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
    assume notPandQ,
    cases em p with pfP pfnotP,
    cases em q with pfQ pfnotQ,
        show ¬p ∨ ¬q, from false.elim (notPandQ (and.intro pfP pfQ)),
        show ¬p ∨ ¬q, from or.inr pfnotQ,
        show ¬p ∨ ¬q, from or.inl pfnotP,
end

-- I don't use "example" here because it's used in following proofs
theorem pf_by_contrapositive: (¬q → ¬p) → (p → q) := 
    begin
        assume nqnp : ¬q → ¬p,
        assume pfP : p,
        have nnq : ¬q → false :=
            begin 
                assume nq : ¬q,
                have np : ¬p := nqnp nq,
                show false, from np pfP
            end,
        show q, from double_neg_elim nnq
    end
#check pf_by_contrapositive

example : ¬(p → q) → p ∧ ¬q :=
begin
    assume notpq,
    apply and.intro,
        show ¬q, --note: "show" can be used to switch the order of goals
            assume pfq,
            have pq : p → q := assume pfp, pfq,
            show false, from notpq pq,

        cases em p with pfp pfnp,
            assumption,
            have pq : p → q := 
                assume pfp, false.elim (pfnp pfp),
            show p, from false.elim (notpq pq)
end

-- an alternative proof to the previous one
example : ¬(p → q) → p ∧ ¬q :=
begin
    assume notpq,
    cases em p with pfp pfnp,
    cases em q with pfq pfnq,
        have pq : p → q := assume p, pfq,
        show p ∧ ¬q, from false.elim (notpq pq),

        show p ∧ ¬q, from and.intro pfp pfnq,
        
        have nqnp : ¬q → ¬p := assume nq, pfnp,
        have pq : p → q := pf_by_contrapositive p q nqnp,
        show p ∧ ¬q, from false.elim (notpq pq)
end

-- an alternative proof to the previous one
example : ¬(p → q) → p ∧ ¬q :=
begin
    assume notpq,
    apply and.intro,
        cases em p with pfp pfnp,
        cases em q with pfq pfnq,
            show p, from pfp,
            show p, from pfp,

            have pq : p → q := assume p, false.elim (pfnp p),
            show p, from false.elim (notpq pq),

            assume pfq,
            have pq : p → q := assume p, pfq,
            show false, from notpq pq
end

-- an alternative proof to the previous one
example : ¬(p → q) → p ∧ ¬q :=
begin
    assume notpq,
    apply and.intro,
        cases em p with pfp pfnp,
            show p, from pfp,

            have nqnp : ¬q → ¬p := assume nq, pfnp,
            have pq : p → q := pf_by_contrapositive p q nqnp,
            show p, from false.elim (notpq pq),

            assume pfq,
            have pq : p → q := assume p, pfq,
            show false, from notpq pq
end

example : (p → q) → (¬p ∨ q) :=
begin
    assume pq,
    cases em p with pfp pfnp,
        show ¬p ∨ q, from or.inr (pq pfp),
        show ¬p ∨ q, from or.inl pfnp
end

example : p ∨ ¬p := 
    begin
        apply em
    end

example : (((p → q) → p) → p) := 
begin
    assume pqp,
    cases em p with pfp pfnp,
        show p, from pfp,

        have n: ¬q → ¬p := assume nq, pfnp,
        have pq : p → q := pf_by_contrapositive p q n,
        show p, from pqp pq
end

-- an alternative proof to the previous one
example : (((p → q) → p) → p) := 
begin
    assume pqp,
    cases em p with pfp pfnp,
        show p, from pfp,

        have pq: p → q :=
            assume pfp, false.elim (pfnp pfp),
        show p, from pqp pq
end

-- Proof that double negation elimination implies axiom of excluded middle
-- First prove that ∀ P, ¬¬(P ∨ ¬P). 
-- This proof makes use of the property that ¬(p ∨ q) ↔ ¬p ∧ ¬q
lemma notnotem: ∀ P, ¬¬(P ∨ ¬P) :=
begin
    assume P,   
    assume npornp,
    have np: ¬P := assume p, npornp (or.inl p),
    have nnp: ¬¬P := assume np, npornp (or.inr np),
    show false, from nnp np
end

#check notnotem
#check non_contradictory_em -- notnotem is actually a built-in lemma

theorem DNEtoEM : (∀ P, ¬¬P → P) → (∀ P, P ∨ ¬P) :=
begin
    assume notnotPtoP P,
    have duo_neg_elim_em : ¬¬(P ∨ ¬P) → P ∨ ¬P := notnotPtoP (P ∨ ¬P),
    show P ∨ ¬P, from duo_neg_elim_em (notnotem P)
end
