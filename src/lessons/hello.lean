/-theorem interesting: 1 = 1 := rfl. -/
#check ¬ (1 = 0)
#check ∀ T: Type, ∀ t: T, t = t
lemma zeqz: 0 = 0 := rfl
lemma oeqo: 1 = 1 := rfl

theorem helloTheorem: "hello" = "hello" := rfl
theorem twooneone: 2 = 1 + 1 := rfl

theorem tthof: 2 + 3 = 1 + 4 := rfl
theorem holeqhl: "Hello " ++ "Logic!" = "Hello Logic!" := rfl

theorem zeqz_and_oeqo: 0 = 0 ∧ 1 = 1 := and.intro zeqz oeqo
theorem haha: 0 = 0 ∧ 1 = 1 := and.intro rfl rfl

theorem negation: tt = ¬ ff := rfl
variable a: bool
#check ¬ (a = ¬ a)

lemma ft: 5 = 1 + 4 := rfl
lemma st: "S" ++ "trike" = "Strike" := rfl

theorem ftst: 5 = 1 + 4 ∧ "S" ++ "trike" = "Strike" := and.intro ft st

#check rfl

constant T: Type
variable t: T

#check "Heoo"

theorem eee: t = t := rfl

#check (eq.refl tt)
#check (eq.refl "Hello")

constant a: Prop