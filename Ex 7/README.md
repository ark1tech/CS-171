# Inductively Defined Propositions

### Write Coq code for any of the following. You may want to write definitions or prior theorems / lemmas for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the IndProp module.

- `Theorem SSSSev__even : ∀ n,  ev (S (S (S (S n)))) → ev n.`
- `Theorem ev5_nonsense :  ev 5 → 2 + 2 = 9.`
- `Theorem ev_sum : ∀ n m, ev n → ev m → ev (n + m).`
- `Theorem ev_ev__ev : ∀ n m, ev (n+m) → ev n → ev m.`
- `Theorem ev_plus_plus : ∀ n m p,  ev (n+m) → ev (n+p) → ev (m+p). (this can be hard btw)`
- `Theorem total_relation_is_total : ∀ n m, total_relation n m. (check IndProp module for more context on this one)`
