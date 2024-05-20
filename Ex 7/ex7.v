(* --------------- PREFACE --------------- *)

Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
    | total_rel (n m : nat) : total_relation n m.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
    intros n H. inversion H. apply H1.
Qed.

(* --------------- ANSWERS --------------- *)

Theorem SSSSev__even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros.
    inversion H.
    inversion H1.
    apply H3.
Qed.

Theorem ev5_nonsense :
    ev 5 -> 2 + 2 = 9.
Proof.
    intros.
    simpl.
    inversion H.
    inversion H1.
    inversion H3.
Qed.

Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
    intros n m HA HB.
    induction HA.
    - simpl. apply HB.
    - simpl. apply ev_SS in IHHA. apply IHHA.
Qed.

Theorem ev_ev__ev : forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
    intros.
    induction H0.
    - simpl in H. apply H.
    - simpl in H. apply IHev. apply evSS_ev in H. apply H.
Qed.

Theorem ev_plus_plus : forall n m p,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
    intros.
    inversion H 
Admitted.

Theorem total_relation_is_total : forall n m,
    total_relation n m.
Proof.
    intros.
    apply (total_rel n m).
Qed.