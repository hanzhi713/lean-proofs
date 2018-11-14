variable g: false
theorem ttt : true → false := false.elim g

theorem zneqo : 0 ≠ 1.

theorem what : "Hello, Lean!" ≠ "Hello Lean!" :=
begin
    assume h : "Hello, Lean!" = "Hello Lean!",
    show false,
    from string.no_confusion,
end

def f : ℕ → ℕ := λ x, x - 1
def v : Prop := 1 = 1
theorem gg : 1 = 1 := rfl

theorem ex2 : 2 ≠ 1.

theorem modus_tollens: 
     ∀ { P Q: Prop }, (P → Q) → ¬ Q → ¬ P :=
        λ P Q pfPQ pfnQ pfP, 
            pfnQ (pfPQ pfP)
 