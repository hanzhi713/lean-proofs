lemma zeqz' : 0 = 0 :=
begin
    apply rfl,
end

#check tt
#check true

#check true.intro

lemma t' : true := true.intro
theorem bad : true := true.intro

lemma f : tt = true := rfl -- ??
lemma f' : tt = tt := rfl
def g_ : true := bool.tt.inj f'
lemma g : tt = true := eq.refl true -- ??

#check false.elim

axiom fff : false
theorem wtf : true = false := false.elim fff
-- theorem wtf_ : 1 = tt := false.elim fff

lemma t1 : 5 = 1 + 4 := eq.refl 5
lemma t2 : "Strike" = "S" ++ "trike" := rfl
theorem t1t2 : 5 = 1 + 4 ∧ "Strike" = "S" ++ "trike" := and.intro t1 t2

theorem alt : 5 = 1 + 4 ∧ "Strike" = "S" ++ "trike" :=
begin
    apply and.intro,
    exact (eq.refl 5),
    exact (eq.refl "Strike"),
end

theorem alt' : 5 = 1 + 4 ∧ "Strike" = "S" ++ "trike" :=
begin
    have X := (eq.refl 5),
    have Y := (eq.refl "Strike"),
    exact and.intro X Y
end

def P : Prop := 0 = 0
def Q : Prop := 1 = 1
lemma pfP : P := eq.refl 0
lemma pfQ : Q := eq.refl 1
theorem pf_PQ : P ∧ Q := and.intro pfP pfQ
theorem pfQ' : Q := and.elim_right pf_PQ

theorem pfQaP : Q ∧ P :=
  and.intro 
    (and.elim_right pf_PQ) 
    (and.elim_left pf_PQ)

theorem pfQaP' : Q ∧ P :=
begin
    have X := (and.elim_right pf_PQ),
    have Y := (and.elim_left pf_PQ),
    apply and.intro X Y,
end

theorem and_com {P Q : Prop} (PQ : P ∧ Q) : Q ∧ P := and.intro 
    (and.elim_right PQ) 
    (and.elim_left PQ)

theorem pfQaP'' : Q ∧ P := and_com pf_PQ

theorem tt11 : 1 = 1 ∧ tt = tt :=
begin
    apply and.intro,
    exact (eq.refl 1),
    exact (eq.refl tt),
end

theorem q11tt : tt = tt ∧ 1 = 1 := and_com tt11


