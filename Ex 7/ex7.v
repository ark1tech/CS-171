(* --------------- PREFACE --------------- *)

Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* --------------- ANSWERS --------------- *)

Theorem SSSSev__even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros.
    induction n.
    - apply ev_0.
    - 

(* Theorem ev5_nonsense :
    ev 5 -> 2 + 2 = 9.
Admitted. *)

(* Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Admitted. *)

(* Theorem ev_ev__ev : forall n m,
    ev (n+m) -> ev n -> ev m.
Admitted. *)

(* Theorem ev_plus_plus : forall n m p,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Admitted. *)

(* Theorem total_relation_is_total : forall n m,
    total_relation n m.
Admitted. *)
