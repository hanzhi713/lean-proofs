import data.set
open set

section
  variable U : Type
  variables A B C : set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  begin
    assume x,
    assume h,
    left,
    exact h.1,
  end

  example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
  begin
    assume x,
    assume h,
    assume xinA,
    have : x ∈ A ∪ B,
        left, assumption,
    contradiction
  end
end

section
    variable {U : Type}

    /- defining "disjoint" -/

    def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

    example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
    disj A B :=
    assume x,
    assume h1 : x ∈ A,
    assume h2 : x ∈ B,
    have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
    show false, from h x h3

    -- notice that we do not have to mention x when applying
    --   h : disj A B
    example (A B : set U) (h1 : disj A B) (x : U)
        (h2 : x ∈ A) (h3 : x ∈ B) :
    false :=
    h1 h2 h3

    -- the same is true of ⊆
    example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
    x ∈ B :=
    h h1

    example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
        (h3 : D ⊆ B) :
    disj C D :=
    begin
        assume x,
        assume xinC xinD,
        have xinA : x ∈ A := h2 xinC,
        have xinB : x ∈ B := h3 xinD,
        exact h1 xinA xinB,
    end
end


section
    variables {I U : Type}
    variables {A B : I → set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
    by simp; assumption

    @[elab_simple]
    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
    by simp at h; apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
    by {simp, existsi i, exact h}

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
    by {simp at h₁, cases h₁ with i h, exact h₂ i h}


    -- BEGIN
    variables (C : set U)

    example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
    begin
        assume x,
        assume h,
        apply Inter.intro,
            assume i,
            split,
                show x ∈ A i, from Inter.elim h.1 i,
                show x ∈ B i, from Inter.elim h.2 i
    end

    example : C ∩ (⋃ i, A i) ⊆ ⋃ i, C ∩ A i :=
    begin
        assume x,
        assume h,
        -- actually, simp * at * here will do the job
        have xinC := h.1,
        apply Union.elim h.2,
            intros i xinAi,
            apply Union.intro,
                exact ⟨xinC, xinAi⟩,
    end
    -- END
end

section
    -- BEGIN
    variable  {U : Type}
    variables A B C : set U

    -- For this exercise these two facts are useful
    example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
    subset.trans h1 h2

    example : A ⊆ A :=
    subset.refl A

    example (h : A ⊆ B) : powerset A ⊆ powerset B :=
    begin
        assume s : set U,
        assume h2 : s ∈ 𝒫 A, -- s is a subset of A, i.e. s ⊆ A, which is x ∈ s → x ∈ A
        assume x : U,
        assume xinS : x ∈ s,
        exact h (h2 xinS),
    end

    example (h : powerset A ⊆ powerset B) : A ⊆ B :=
    begin
        have : A ∈ 𝒫 A,
            assume _ _, assumption,
        have : A ∈ 𝒫 B := h this,
        assumption, -- note : A ∈ 𝒫 B is equivalent to A ⊆ B
    end
    -- END
end
