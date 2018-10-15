-- Exercise 1
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can now with tactic proofs, using also rw and simp as appropriate.

-- Actually I'm already using tactics 😁

-- Use tactic combinators to obtain a one line proof of the following:
-- Exercise 2
example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {split, left, assumption, 
    split, right, left, assumption, 
    right, right, assumption}

-- Alternatively,
example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {split, left, assumption, 
    split, repeat {right, {left, assumption} <|> {right, assumption}}}

-- Alternatively,
meta def left_middle_right : tactic unit :=
`[ repeat { {left, assumption} <|> right <|> assumption } ]

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {split, left_middle_right, 
    split, repeat {left_middle_right}}
