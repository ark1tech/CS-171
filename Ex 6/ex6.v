(* --------------- PREFACE --------------- *)

Theorem mul_0_r : forall (n : nat), n * 0 = 0.
Proof.
    intros.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Inductive list (X:Type) : Type :=
    | nil
    | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

Notation "x :: l" := (cons x l)
    (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* --------------- ANSWERS --------------- *)
Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
    intros.
    apply H.
Qed.

Theorem and_assoc : forall  P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros.
    split.
    - split. apply H. apply H.
    - apply H.
Qed. 

Lemma mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
    intros.
    destruct n.
    - left. reflexivity.
    - destruct m.
     + right. reflexivity.
     + left. inversion H.
Qed. 

Theorem or_commut : forall P Q : Prop,  P \/ Q -> Q \/ P.
Proof.
    intros.
    inversion H.
    right. apply H0.
    left. apply H0.
Qed.
    
Theorem not_both_true_and_false : forall P : Prop,  ~(P /\ ~P).
Proof.
    unfold not.
    intros.
    destruct H.
    apply H0.
    apply H.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,  P \/  (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros.
    split.
    - split. 
        + destruct H. left. apply H. destruct H. right. apply H.
        + destruct H. left. apply H. destruct H. right. apply H0.
    - intros H. inversion H as [[x | y]]. left. apply x. inversion H0. left. apply H1. right. split. apply y. apply H1.
Qed.