def n: ℕ := 1

lemma p: 0 = 0 := eq.refl 0
lemma s: "Hello Lean!" = "Hello Lean!" := eq.refl "Hello Lean!"

lemma s1: tt = tt := eq.refl tt

/-def p' : 0 = 0 := eq.refl 1-/

theorem s' : 0 = 0 := eq.refl 0

lemma oeqo : 1 = 1 := eq.refl 1

lemma teqt: 2 = 1 + 1 := eq.refl (1+1)

lemma h : "Hello" = "He" ++ "llo" := rfl
lemma pp : 3*3 + 4*4 = 5*5 := rfl
lemma tthof : 2 + 3 = 1 + 4 := rfl
lemma hpleqhl : "Hello " ++ "Lean!" = "Hello Lean!" := rfl

#check "Hello" = "Hello"