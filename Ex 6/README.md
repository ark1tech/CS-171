# Logic
### Write Coq code for any of the following. You may want to write definitions or prior theorems / lemmas for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the Logic module.
- `Lemma proj2 : ∀ P Q : Prop, P ∧ Q → Q.`
- `Theorem and_assoc : ∀ P Q R : Prop, P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.`
- `Lemma mult_is_O : ∀ n m, n × m = 0 → n = 0 ∨ m = 0.`
- `Theorem or_commut : ∀ P Q : Prop,  P ∨ Q → Q ∨ P.`
- `Theorem not_both_true_and_false : ∀ P : Prop,  ¬ (P ∧ ¬P).`
- `Theorem or_distributes_over_and : ∀ P Q R : Prop,  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).`