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

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Lemma plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.
  
Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
    intros.
    induction n as [| n'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros.
    induction n.
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite -> IHn. rewrite plus_n_Sm. reflexivity.
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
    intros.
    induction H.
    - simpl. apply H0.
    - apply ev_SS. apply IHev.
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
    apply ev_ev__ev with (n := (n+m)).
    - rewrite <- add_comm. rewrite add_comm with (n:=m). apply ev_sum.

Theorem total_relation_is_total : forall n m,
    total_relation n m.
Proof.
    intros.
    apply (total_rel n m).
Qed.