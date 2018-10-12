-- this is a proof that ∀ vectors a, b ∈ ℤ^3, 
-- (a × b) ⬝ a = 0 ∧ (a × b) ⬝ b = 0

def dot: ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℤ := λ ⟨a, b, c⟩ ⟨d, e, f⟩, a*d + b*e + c*f
def cross: ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := λ ⟨a, b, c⟩ ⟨d, e, f⟩, ⟨b*f - c*e, c*d - a*f, a*e - b*d⟩

variables m n p j k l : ℤ
#eval cross (124, 1294, 123) (156, 949, 29238499)
#reduce dot (cross (8, 1, 5) (2, 8, 9)) (2, 8, 9)
#reduce dot (cross (m, n, p) (j, k, l)) (j, k, l)

theorem cross' (a b c d e f: ℤ) : cross (a, b, c) (d, e, f) = (b*f - c*e, c*d - a*f, a*e - b*d) := rfl
theorem dot' (a b c d e f: ℤ) : dot (a, b, c) (d, e, f) = a*d + b*e + c*f := rfl

local attribute [simp] mul_comm mul_assoc mul_right_comm

theorem proof1 : ∀ {a b c d e f: ℤ}, dot (cross (a, b, c) (d, e, f)) (a, b, c) = 0 :=
assume a b c d e f,
calc
    dot (cross (a, b, c) (d, e, f)) (a, b, c) = dot (b*f - c*e, c*d - a*f, a*e - b*d) (a, b, c) : by rw cross'
    ... = (b*f - c*e)*a + (c*d - a*f)*b + (a*e - b*d)*c : by rw dot'
    ... = b*f*a - c*e*a + (c*d*b - a*f*b) + (a*e*c - b*d*c) : by repeat {rw sub_mul}
    ... = 0 : by simp
#check proof1

theorem proof2 : ∀ {a b c d e f: ℤ}, dot (cross (a, b, c) (d, e, f)) (d, e, f) = 0 :=
assume a b c d e f,
calc
    dot (cross (a, b, c) (d, e, f)) (d, e, f) = dot (b*f - c*e, c*d - a*f, a*e - b*d) (d, e, f) : by rw cross'
    ... = (b*f - c*e)*d + (c*d - a*f)*e + (a*e - b*d)*f : by rw dot'
    ... = b*f*d - c*e*d + (c*d*e - a*f*e) + (a*e*f - b*d*f) : by repeat {rw sub_mul}
    ... = a * (e * f) + (c * (d * e) + (-(a * (e * f)) + -(c * (d * e)))) : by simp
    ... = a * (e * f) + (c * (d * e) + -(a * (e * f)) + -(c * (d * e))) : by rw add_assoc
    ... = 0 : by simp

#check proof2

example (a b c d e f: ℤ) : 
     dot (cross (a, b, c) (d, e, f)) (a, b, c) = 0 ∧ dot (cross (a, b, c) (d, e, f)) (d, e, f) = 0 :=
    and.intro proof1 proof2