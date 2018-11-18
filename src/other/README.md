# Lean Miscellaneous Proofs

[dispf_inclass.lean](dispf_inclass.lean) is a proof of ```¬ (∀ (X : Type), ∀ (p q : X → Prop), (∃ x, p x) ∧ (∃ x, q x) → ∃ x, p x ∧ q x)```, which is a disproof of one of the proposition in the fifth in-class exercise.

[emoji_proof.lean](emoji_proof.lean) is a proof of ```∀ p q r, p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``` using user-defined emoji notation: ```∀ p q r, p 😂 (q 😶 r) 😆 (p 😂 q) 😶 (p 😂 r) :=```

[int_vector3d_cross_full.lean](int_vector3d_cross_full.lean) is a proof of ```∀ vectors a, b ∈ ℤ³, (a × b) ⬝ a = 0``` without using the ```simp``` tactic. [int_vector3d_cross.lean](int_vector3d_cross.lean) is the same proof with the ```simp``` tactic. [real_vector3d_cross.lean](real_vector3d_cross.lean) is the same proof extended to real numbers ```ℝ³```.

[pf_1_not_eq_2.lean](pf_1_not_eq_2.lean) contains multiple equivalent proofs of the proposition ```1 ≠ 2```.

[set_exer.lean](set_exer.lean) and [set_exer2.lean](set_exer2.lean) contains the answers to the [chapter 11](https://leanprover.github.io/logic_and_proof/sets.html#exercises) and [chapter 12](https://leanprover.github.io/logic_and_proof/sets_in_lean.html#exercises) exercises  of the book [Logic and Proof](https://leanprover.github.io/logic_and_proof) respectively.