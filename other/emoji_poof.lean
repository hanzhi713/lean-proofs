def and_emoji (a b : Prop) := a ∧ b
def or_emoji (a b : Prop) := a ∨ b
def iff_emoji (a b : Prop) := a ↔ b
def impl_emoji (a b : Prop) := a → b

infix `😂` : 55 := and_emoji
infix `😆` : 45 := iff_emoji
infix `😶` : 55 := or_emoji
infix `😉` : 50 := and.intro
infix `😇` : 40 := iff.intro

notation `🤜` a : 50 := or.inl a
notation a `🤛` : 50 := or.inr a
notation a `👈` : 90 := and.elim_right a
notation `👉` a : 90 := and.elim_left a
notation `👍` a `👌` b `👌` c := or.elim a b c

example : ∀ p q r, p 😂 (q 😶 r) 😆 (p 😂 q) 😶 (p 😂 r) := 
λ p q r,
    (λ pqr : p 😂 (q 😶 r), 
        (👍 (pqr👈)
            👌(λ pfq, 🤜 (👉pqr 😉 pfq))
            👌(λ pfr, (👉pqr 😉 pfr) 🤛)
        )
    )
    😇
    (λ pqpr : (p 😂 q) 😶 (p 😂 r), 
        (👍 pqpr 
            👌(λ pq, 👉pq 😉 (🤜 pq👈))
            👌(λ pr, 👉pr 😉 (pr👈 🤛))
        )
    )

example : ∀ P Q, P 😂 Q 😆 Q 😂 P :=
λ P Q, 
        (λ pq, pq👈 😉 👉pq) 
        😇 
        (λ qp, qp👈 😉 👉qp)
