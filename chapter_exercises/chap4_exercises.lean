-- Exercise 1

variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
begin
    assume first,
    assume second,
    assume a,
    exact first a (second a),
end
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

-- Exercise 2
-- It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

-- Exercise 3
-- It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry