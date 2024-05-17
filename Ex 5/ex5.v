(* --------------- PREFACE --------------- *)

Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

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

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o)
    -> (n + p) = m
    -> (n + p) = (minustwo o).
Proof.
    intros n m o p eq1 eq2.
    rewrite eq2.
    apply eq1.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j
    -> j = z :: l
    -> x = y.
Proof.
    intros X x y z l j eq1 eq2.
    injection eq1 as eq3 eq4.
    rewrite eq3.
    rewrite <- eq4 in eq2.
    symmetry.
    injection eq2 as eq5.
    apply eq5.
Qed.

Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [ ] -> x = z.
Proof.
    intros.
    discriminate H.
Qed.


(* BONUS : needed for plus_n_n_injective *)
Lemma plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
    intros n. 
    induction n.
    - destruct m.
        + reflexivity.
        + discriminate.
    - destruct m.
        + symmetry. discriminate.
        + simpl. symmetry. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. injection H as eq1. apply IHn in eq1. f_equal. symmetry. apply eq1.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X), length l = n -> nth_error l n = None.
Proof.
    intros.

(* Theorem eqb_true : forall n m, n =? m = true -> n = m. *)