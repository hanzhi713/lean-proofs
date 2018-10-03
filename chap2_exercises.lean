def double_ (a: ℕ ) : ℕ := a + a
def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x

def times2plus1 : ℕ → ℕ := λ x, x * 2 + 1

def do_twice_ (f: ℕ → ℕ ) (x: ℕ ) : ℕ := f (f x)
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
def do_third_times : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f (f x))

#check do_twice
#reduce do_third_times square 2 -- 256
#reduce do_twice square 2 -- 16

def quadruple : ℕ → ℕ := λ x, do_twice double x

#reduce quadruple 2 -- 8

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → ℕ → ℕ := λ f g x, f g (f g x)

/- Equivalent forms -/
def Do_Twice_ (f: (ℕ → ℕ) → (ℕ → ℕ)) : (ℕ → ℕ) → ℕ → ℕ := λ g x, f g (f g x)
def Do_Twice' (f: (ℕ → ℕ) → (ℕ → ℕ)) (x: ℕ → ℕ) : ℕ → ℕ := f (f x)
def Do_Twice'' : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → ℕ → ℕ := λ f g, f (f g)

#reduce Do_Twice do_twice double 2
#reduce Do_Twice do_twice times2plus1 2 
#reduce Do_Twice do_third_times times2plus1 2
#eval Do_Twice_ do_twice square 2

#reduce do_third_times square 2
#eval Do_Twice do_third_times square 2
#eval Do_Twice do_twice square 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

def curry (α β γ : Type): (α × β → γ) → α → β → γ := λ f a b, f (a, b)

def uncurry (α β γ : Type): (α → β → γ) → α × β → γ := λ f ⟨a, b⟩, f a b

