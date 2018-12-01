import data.nat.basic
import data.set


def odd : ℕ → Prop := λ n, ∃ m, n = 2 * m + 1
def even : ℕ → Prop := λ n, ∃ m, n = 2 * m

example : ∀ n, (even n ∨ odd n) :=
begin
    assume n,
    apply @nat.rec_on (λ n, even n ∨ odd n),
        left, exact ⟨0, rfl⟩,

        assume k,
        assume h,
        cases h,
            right, 
            apply exists.elim h,
                assume m,
                assume f,
                rw f,
                exact ⟨m, rfl⟩,
            
            left,
            apply exists.elim h,
                assume m,
                assume f,
                rw f,
                exact ⟨m + 1, rfl⟩,
end

theorem not_both_even_and_odd : ∀ n, ¬ (even n ∧ odd n) :=
begin
    assume n,
    apply @nat.rec_on (λ n, ¬ (even n ∧ odd n)),
        assume h,
        apply exists.elim h.2,
            assume _ f, cases f,

        assume k,
        assume h,
        assume h1,
        have : even k ∧ odd k,
            let f : ℕ → ℕ := λ n, n - 1,
            split,
                apply exists.elim h1.2,
                    assume m,
                    assume h2,
                    exact ⟨m, congr_arg f h2⟩,
                    
                apply exists.elim h1.1,
                    assume m,
                    assume h2,
                    apply exists.intro (m - 1),
                        have : k = 2 * m - 1 := congr_arg f h2,
                        rw this,
                            cases m,
                                trivial,

                                simp,
                                calc
                                    2 * nat.succ m - 1 = 2 * (m + 1) - 1 : by trivial
                                    ... = 2 * m + 2 * 1 - 1 : by rw mul_add
                                    ... = 2 * m + (2 * 1 - 1) : by rw (@nat.add_sub_assoc (2*1) 1 dec_trivial)
                                    ... = 1 + 2 * m : by simp,
        contradiction

end

def tilda : ℕ → ℕ → Prop := λ m n, ((even m) ∧ (n = m + 1)) ∨ ((odd m) ∧ n = m - 1) ∨ (m = n)

def equiv_tilda : ℕ → set ℕ := λ a, {b | tilda a b}

example : equiv_tilda 5 = {4, 5} :=
begin
    apply set.ext,
    assume x,
    split,
        assume h,
        cases h,
        have : odd 5 := ⟨2, rfl⟩,
        have : even 5 ∧ odd 5 := ⟨h.1, this⟩,
        have : false := not_both_even_and_odd 5 this,
        contradiction,

        cases h,
            cases h,
            rw h_right,
            simp,

            rw ←h,
            simp,

        assume h,
        cases h,
            right, right, 
            apply eq.symm h,

            cases h,
                right, left,
                split, 
                    exact ⟨2, rfl⟩,
                    rw h,

                cases h,
end

def set_nat : set ℕ := {n | true}

theorem Union.intro {U : Type} {I : Type} {A : I → set U} 
    {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
    by {simp, existsi i, exact h}

theorem Union.elim {U : Type} {I : Type} {A : I → set U} {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
    by {simp at h₁, cases h₁ with i h, exact h₂ i h}

example : (⋃ i, equiv_tilda i) = set_nat :=
begin
    apply set.ext,
        assume x,
        split,
            assume h,
            trivial,

            assume h,
            apply @nat.rec_on (λ k, k ∈ ⋃ i, equiv_tilda i),
                apply Union.intro 0,
                right, right, trivial,

                assume k hk,
                apply Union.elim hk,
                    assume i hi,
                    let f : ℕ → ℕ := λ n, n + 1,
                    cases hi,
                        apply Union.intro (i+2),
                            right, right, 
                            rw hi.2,

                        cases hi,
                        apply Union.intro (i),
                            right, right,
                            rw hi.2,
                            rw ←nat.add_one,
                            rw nat.sub_add_cancel,
                            apply exists.elim hi.1,
                                assume a ha,
                                rw ha,
                                have : 2 * a + 1 ≥ 1 := dec_trivial,
                                assumption,
                        
                        apply Union.intro (i+1),
                            right, right, 
                            rw hi,
end