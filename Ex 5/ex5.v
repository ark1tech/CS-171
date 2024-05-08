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
    subst.
    symmetry.
    
    

(* Example discriminate_ex3 : ∀ (X : Type) (x y z : X) (l j : list X), x :: y :: l = [ ] → x = z. *)

(* Theorem plus_n_n_injective : ∀ n m, n + n = m + m →  n = m. *)

(* Theorem nth_error_after_last: ∀ (n : nat) (X : Type) (l : list X), length l = n → nth_error l n = None. *)

(* Theorem eqb_true : forall n m, n =? m = true -> n = m. *)