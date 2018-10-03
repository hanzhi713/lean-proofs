-- theorem add_assoc' (a b c : ℤ) : a+b+c = a+(b+c) := add_assoc a b c
-- theorem add_comm' (a b : ℤ) : a + b = b + a := add_comm a b
-- theorem mul_assoc' (a b c : ℤ) : a*b*c = a*(b*c) := mul_assoc a b c
-- theorem mul_comm' (a b:ℤ) : a*b=b*a := mul_comm a b
-- theorem add_mul' (a b c : ℤ) : (a+b)*c = a*c+b*c := add_mul a b c
-- theorem zero_add' (a:ℤ) : 0 + a = a := zero_add a
-- theorem sub_eq_add_neg' (a b : ℤ) : a - b = a + -b := sub_eq_add_neg a b
-- theorem sub_neg_eq_add' (a b :ℤ) : a - -b = a + b := sub_neg_eq_add a b
-- theorem sub_self' (a: ℤ) : a - a = 0 := sub_self a
-- theorem neg_eq_neg_one_mul' (a:ℤ): -a = -1 * a := neg_eq_neg_one_mul a

-- this is a proof that ∀ vectors a, b ∈ ℝ^3, (a × b) ⬝ a = 0

axiom add_assoc' : ∀ a b c : ℤ, a + b + c = a + (b + c)
axiom add_comm' : ∀ a b : ℤ, a + b = b + a
axiom zero_add' : ∀ a : ℤ, 0 + a = a
axiom sub_self' : ∀ a : ℤ, a - a = 0
axiom sub_eq_add_neg': ∀ a b : ℤ, a - b = a + -b
axiom sub_neg_eq_add': ∀ a b : ℤ, a - -b = a + b
axiom mul_assoc' : ∀ a b c: ℤ, a * b *c = a * (b * c)
axiom mul_comm' : ∀ a b : ℤ, a * b = b * a 
axiom add_mul' : ∀ a b c : ℤ, (a + b) * c = a * c + b * c
axiom neg_eq_neg_one_mul' : ∀ a : ℤ, -a = -1 * a

theorem zero_sub' (a : ℤ) : 0 - a = -a :=
calc
    0 - a = 0 + -a : by rw sub_eq_add_neg'
    ... = -a : by rw zero_add'

theorem neg_mul_eq_mul_neg' (a b : ℤ) : -(a * b) = a * -b :=
calc
    -(a * b) = -1 * (a * b) : by rw neg_eq_neg_one_mul'
    ... = -1 * a * b : by rw mul_assoc'
    ... = a * -1 * b : by rw mul_comm' a
    ... = a * (-1 * b) : by rw mul_assoc'
    ... = a * -b : by rw neg_eq_neg_one_mul' b

theorem neg_mul_eq_neg_mul_symm' (a b : ℤ) : -a * b = -(a * b) :=
calc
    -a * b = -1 * a * b : by rw neg_eq_neg_one_mul'
    ... = -1 * (a * b) : by rw mul_assoc'
    ... = -(a * b) : by rw neg_eq_neg_one_mul' (a * b)

theorem times_one : ∀ {a : ℤ}, a = 1 * a :=
assume a,
calc
    a = 0 + a : by rw zero_add'
    ... = 0 - -a : by rw sub_neg_eq_add'
    ... = 0 - -1 * a : by rw neg_eq_neg_one_mul'
    ... = 0 - -(1 * a) : by rw neg_mul_eq_neg_mul_symm'
    ... = 0 + 1 * a : by rw sub_neg_eq_add'
    ... = 1 * a : by rw zero_add'

theorem add_sub_assoc' {a b c : ℤ} : a + b - c = a + (b - c) :=
calc
    a + b - c = a + b + -c : by rw sub_eq_add_neg'
    ... = a + (b + -c) : by rw add_assoc'
    ... = a + (b - c) : by rw sub_eq_add_neg'

theorem sub_add_eq_sub_sub' {a b c : ℤ} : a - (b + c) = a - b - c :=
calc
    a - (b + c) = a + -(b + c) : by rw sub_eq_add_neg'
    ... = a + (-1)* (b + c) : by rw neg_eq_neg_one_mul'
    ... = a + (b + c) * -1 : by rw mul_comm'
    ... = a + (b * -1 + c * -1) : by rw add_mul'
    ... = a + b * -1 + c * -1 : by rw add_assoc'
    ... = a + -1*b + c * -1 : by rw mul_comm'
    ... = a + -1*b + -1*c : by rw mul_comm' c
    ... = a + -b + -1*c : by rw neg_eq_neg_one_mul' b
    ... = (a + -b) + -c : by rw neg_eq_neg_one_mul' c
    ... = a - b + -c : by rw sub_eq_add_neg'
    ... = a - b - c : by rw sub_eq_add_neg' (a-b) c

theorem neg_mul_comm' (a b: ℤ) : -a * b = a * -b :=
calc
    -a * b = -(a * b) : by rw neg_mul_eq_neg_mul_symm'
    ... = a * -b : by rw neg_mul_eq_mul_neg'

theorem sub_mul' (a b c: ℤ) : (a - b) * c = a * c - b * c :=
calc
    (a - b) * c = (a + (-b)) * c : by rw sub_eq_add_neg'
    ... = a * c + -b * c : by rw add_mul'
    ... = a * c + b * -c : by rw neg_mul_comm'
    ... = a * c + - (b * c) : by rw neg_mul_eq_mul_neg'
    ... = a * c - b * c : by rw sub_eq_add_neg'

theorem sub_add_symm' {a b c : ℤ} : a - (b - c) = a - b + c :=
calc 
    a - (b - c) = a + -(b - c) : by rw sub_eq_add_neg'
    ... = a + -1* (b - c) : by rw neg_eq_neg_one_mul'
    ... = a + (b - c) * -1 : by rw mul_comm'
    ... = a + (b*-1 - c * -1) : by rw sub_mul'
    ... = a + (-1*b - c*-1) : by rw mul_comm'
    ... = a + (-1*b - -1*c) : by rw mul_comm' c
    ... = a + -1*b - -1*c : by rw add_sub_assoc'
    ... = a + -b - -1*c : by rw neg_eq_neg_one_mul' b
    ... = a + -b - -c : by rw neg_eq_neg_one_mul' c
    ... = a - b - -c : by rw sub_eq_add_neg' a
    ... = a - b + c :  by rw sub_neg_eq_add'

theorem sub_add' {a b c : ℤ} :  a - b + c = a - (b - c):=
begin
    apply eq.symm,
    exact sub_add_symm'
end

theorem mul_right_comm' {a b c : ℤ} : a * b * c = a * c * b :=
calc
    a * b * c = a * (b * c): by rw mul_assoc'
    ... = a * (c * b) : by rw mul_comm' b
    ... = a * c * b : by rw mul_assoc'

theorem add_right_comm' {a b c : ℤ} : a + b + c = a + c + b :=
calc
    a + b + c = a + (b + c) : by rw add_assoc'
    ... = a + (c + b) : by rw add_comm' c
    ... = a + c + b : by rw add_assoc'

def dot: ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℤ := λ ⟨a, b, c⟩ ⟨d, e, f⟩, a*d + b*e + c*f
def cross: ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := λ ⟨a, b, c⟩ ⟨d, e, f⟩, ⟨b*f - c*e, c*d - a*f, a*e - b*d⟩

variables m n p j k l : ℤ
#eval cross (124, 1294, 123) (156, 949, 29238499)
#reduce dot (cross (8, 1, 5) (2, 8, 9)) (2, 8, 9)
#reduce dot (cross (m, n, p) (j, k, l)) (j, k, l)

theorem cross' (a b c d e f: ℤ) : cross (a, b, c) (d, e, f) = (b*f - c*e, c*d - a*f, a*e - b*d) := rfl
theorem dot' (a b c d e f: ℤ) : dot (a, b, c) (d, e, f) = a*d + b*e + c*f := rfl
theorem add_sub_swap1' (a b c d: ℤ): a - b + c - d = a - d - b + c :=
calc
    a - b + c - d = a - b + c + -d : by rw sub_eq_add_neg'
    ... = a - b + (c + -d) : by rw add_assoc'
    ... = a - b + (-d + c) : by rw add_comm' c
    ... = a - b + -d + c : by rw add_assoc'
    ... = a - (b - -d) + c : by rw sub_add'
    ... = a - (b + d) + c : by rw sub_neg_eq_add'
    ... = a - (d + b) + c : by rw add_comm' b
    ... = a - d - b + c : by rw sub_add_eq_sub_sub'

theorem add_sub_swap2' (a b c d: ℤ) : -a + b + (c - d) = c - a + (b - d) :=
calc
    -a + b + (c - d) = -a + b + c - d : by rw add_sub_assoc'
    ... = -a + c + b - d : by rw add_right_comm'
    ... = c + -a + b - d : by rw add_comm' c
    ... = c - a + b - d : by rw sub_eq_add_neg' c
    ... = c - a + (b - d) : by rw add_sub_assoc'

theorem mul_swap' (a b c: ℤ) : a * b * c = c * b *a :=
calc
    a * b * c = a * c * b : by rw mul_right_comm'
    ... = a * (c * b) : by rw mul_assoc'
    ... = (c * b) * a : by rw mul_comm'

theorem proof (a b c d e f: ℤ) : dot (cross (a, b, c) (d, e, f)) (a, b, c) = 0 :=
calc
    dot (cross (a, b, c) (d, e, f)) (a, b, c) = dot (b*f - c*e, c*d - a*f, a*e - b*d) (a, b, c) : by rw cross'
    ... = (b*f - c*e)*a + (c*d - a*f)*b + (a*e - b*d)*c : by rw dot'
    ... = b*f*a - c*e*a + (c*d - a*f)*b + (a*e - b*d)*c : by rw sub_mul'
    ... = b*f*a - c*e*a + (c*d*b - a*f*b) + (a*e - b*d)*c : by rw sub_mul'
    ... = b*f*a - c*e*a + (c*d*b - a*f*b) + (a*e*c - b*d*c) : by rw sub_mul'
    ... = b*f*a - c*e*a + c*d*b - a*f*b + (a*e*c - b*d*c) : by rw add_sub_assoc'
    ... = b*f*a - a*f*b - c*e*a + c*d*b + (a*e*c - b*d*c) : by rw add_sub_swap1'
    ... = a*f*b - a*f*b - c*e*a + c*d*b + (a*e*c - b*d*c) : by rw mul_swap'
    ... = 0 - c*e*a + c*d*b + (a*e*c - b*d*c) : by rw sub_self'
    ... = -(c*e*a) + c*d*b + (a*e*c - b*d*c) : by rw zero_sub'
    ... = a*e*c - c*e*a + (c*d*b - b*d*c) : by rw add_sub_swap2'
    ... = c*e*a - c*e*a + (c*d*b - b*d*c) : by rw mul_swap'
    ... = 0 + (c*d*b - b*d*c) : by rw sub_self'
    ... = (c*d*b - b*d*c) : by rw zero_add'
    ... = b*d*c - b*d*c : by rw mul_swap'
    ... = 0 : by rw sub_self'
