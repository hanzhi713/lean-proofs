variables P Q : Prop

variable forward: P → Q
variable backward: Q → P

def pqEquiv : P ↔ Q := (iff.intro forward backward)
#check pqEquiv
#check iff.elim_left (pqEquiv P Q forward backward)

theorem ifftrans' {P Q R : Prop} (pq: P ↔ Q)  (qr: Q ↔ R): P ↔ R :=
begin
    apply iff.intro,
        assume p,
            have ptq := iff.elim_left pq,
            have qtr := iff.elim_left qr,
            show R, from qtr (ptq p),

        assume r,
            have qtp := iff.elim_right pq,
            have rtq := iff.elim_right qr,
            show P, from qtp (rtq r),
end

-- cheating here
theorem ifftrans'' {P Q R : Prop} (pq: P ↔ Q) (qr: Q ↔ R) : P ↔ R :=
begin
    exact iff.trans pq qr
end

#check ifftrans'
#check iff.trans

theorem ifftrans : ∀ {P Q R}, (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
    assume P Q R,
    assume pq qr,
        apply iff.intro,
            assume p,
                have ptq := iff.elim_left pq,
                have qtr := iff.elim_left qr,
                show R, from qtr (ptq p),

            assume r,
                have qtp := iff.elim_right pq,
                have rtq := iff.elim_right qr,
                show P, from qtp (rtq r),
end

lemma andcomm : ∀ {P Q}, P ∧ Q ↔ Q ∧ P :=
by {assume p q, apply iff.intro, 
assume pq, split, exact pq.2, exact pq.1, 
assume qp, split, exact qp.2, exact qp.1}

lemma andcomm' : ∀ {P Q}, P ∧ Q ↔ Q ∧ P := λ P Q, and.comm

lemma a_imp_b_imp_c_iff_a_and_b_imp_c:
    ∀ A B C: Prop, (A → B → C) ↔ ((A ∧ B) → C) :=
    λ A B C: Prop,
    begin
        apply iff.intro,
            assume abc,
            assume aandb,
            exact abc aandb.1 aandb.2,

            assume abc,
            assume a,
            assume b,
            exact abc (and.intro a b)
    end

example : 0 = 1 ∨ 0 = 0 :=
begin
    apply or.intro_right,
    apply rfl
end