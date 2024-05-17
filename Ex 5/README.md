# Tactics
### Write Coq code for any of the following. You may want to write definitions or prior theorems / lemmas for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the Tactics module.

- `Example trans_eq_exercise : ∀ (n m o p : nat), m = (minustwo o) → (n + p) = m → (n + p) = (minustwo o).`
- `Example injection_ex3 : ∀ (X : Type) (x y z : X) (l j : list X), x :: y :: l = z :: j → j = z :: l → x = y.`
- `Example discriminate_ex3 : ∀ (X : Type) (x y z : X) (l j : list X), x :: y :: l = [ ] → x = z.`
- `Theorem plus_n_n_injective : ∀ n m, n + n = m + m →  n = m.`
- `Theorem nth_error_after_last: ∀ (n : nat) (X : Type) (l : list X), length l = n → nth_error l n = None.`
- `Theorem eqb_true : forall n m, n =? m = true -> n = m.`