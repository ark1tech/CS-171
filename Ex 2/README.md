# Basics and Introduction

### Write Coq code for any of the following. You may want to write definitions for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the Basics / Induction modules (particularly for #2).  Numbers 1 to 4 are taken from Basics, while 5 to 8 are taken from Induction.

- `Theorem plus_id_exercise : ∀ n m o : nat, n = m → m = o → n + m = m + o.`
- `Theorem mult_n_1 : ∀ p : nat, p × 1 = p.`
- `Theorem identity_fn_applied_twice : ∀ (f : bool → bool), (∀ (x : bool), f x = x) → ∀ (b : bool), f (f b) = b.`
- `Theorem andb_eq_orb : ∀ (b c : bool), (andb b c = orb b c) → b = c.`
- `Theorem mul_0_r : ∀ n:nat, n × 0 = 0.`
- `Theorem add_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p.`
- `Theorem eqb_refl : ∀ n : nat, (n =? n) = true.`
- `Theorem even_S : ∀ n : nat, even (S n) = negb (even n).`