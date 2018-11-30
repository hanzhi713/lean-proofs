import data.set
import data.int.basic

def odd : ℤ → Prop := λ n, ∃ m, n = 2 * m + 1
def even : ℤ → Prop := λ n, ∃ m, n = 2 * m

theorem even_or_odd : ∀ n, (even n ∨ odd n) :=
begin
    assume n,
    apply @int.induction_on (λ n, even n ∨ odd n),
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
                apply exists.intro (m + 1),
                    calc 
                        2 * m + 1 + 1 = 2 * m + (1 + 1) : by simp 
                        ... = 2 * m + 2 * 1 : by trivial
                        ... = 2 * (m + 1) : by rw mul_add,
        
        assume k h,
        cases h,
            right, 
            apply exists.elim h,
                assume m,
                assume f,
                rw f,
                apply exists.intro (m - 1),
                    apply eq.symm,
                    calc
                        2 * (m - 1) + 1 = 2 * m - 2 * 1 + 1 : by rw mul_sub
                        ... = 2 * m - (2 * 1 - 1) : by simp,
            left,
            apply exists.elim h,
                assume m,
                assume f,
                rw f,
                apply exists.intro m,
                    calc 
                        2 * m + 1 - 1 = 2 * m + (1 - 1) : by rw add_sub_assoc 
                        ... = 2 * m : by simp,
end

example : ∀ n, ¬ (even n ∧ odd n) :=
begin
    assume n,
    apply @int.induction_on (λ n, ¬ (even n ∧ odd n)),
        assume h,
        cases h.2 with _ pf,
        cases w,
            repeat {cases pf},

        assume k h,
        assume h1,
        cases h1 with evenk oddk,
        have : even k ∧ odd k,
        split,
            apply exists.elim oddk,
                assume m eq1,
                let := congr_arg (λ n: ℤ, n - 1) eq1,
                simp at this,
                apply exists.intro m,
                    rw this,
                    simp [add_comm (2*m) (-1), add_assoc],
                
            apply exists.elim evenk,
                assume m,
                assume eq1,
                apply exists.intro (m - 1),
                    let := congr_arg (λ n: ℤ, n - 1) eq1,
                    simp at this,
                    rw this,
                    apply eq.symm,
                    calc
                        2 * (m - 1) + 1 = 2 * m - 2 * 1 + 1 : by rw mul_sub
                        ... = -(2-1) + 2 * m : by simp,
        contradiction,
                  
        assume k h,
        assume h1,
        cases h1,
        have : even k ∧ odd k,
            split,
                apply exists.elim h1_right,
                    assume m eq1,
                    let := congr_arg (λ n: ℤ, n + 1) eq1,
                    simp at this,
                    apply exists.intro (m + 1),
                        rw this,
                        calc
                            1 + (1 + 2 * m) = 1 + 1 + 2 * m : by rw add_assoc
                            ... = 2 + 2 * m : by trivial
                            ... = 2 * m + 2 * 1 : by simp
                            ... = 2 * (m + 1) : by rw mul_add,
            
                apply exists.elim h1_left,
                    assume m eq1,
                    let := congr_arg (λ n: ℤ, n + 1) eq1,
                    simp at this,
                    have eq2 : 1 + 2 * m = 2 * m + 1 := by simp,
                    exact ⟨m, eq.trans this eq2⟩,
        contradiction,
end