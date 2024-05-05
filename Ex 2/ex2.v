Definition orb (b1: bool) (b2: bool) : bool :=
    match b1 with 
    |true => true
    |false => b2
    end.

Definition andb (b1: bool) (b2: bool) : bool :=
    match b1 with
    |false => false
    |true => b2
    end. 

Fixpoint eqb (n m : nat) : bool :=
    match n, m with
    |O , O => true
    |O , S _ => false
    |S _ , O => false
    |S n', S m' => eqb n' m'
    end.

Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Fixpoint minus (n m : nat) : nat := 
    match n, m with 
    | O , _ => O
    | S _ , O => n
    | S n' , S m' => minus n' m'
    end.

Fixpoint mult (n : nat) (m : nat) : nat :=
    match n with
    |O => O
    |S n' => plus m (mult n' m)
    end. 

(* ---------- Answers ---------- *)

Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
    intros.
    rewrite -> H.
    rewrite -> H0.
    reflexivity.
Qed.

Search ( mult ).

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
    intros.
    destruct p.
    - reflexivity.
    - rewrite <- mult_n_Sm. simpl. 
    rewrite <- mult_n_O. reflexivity.
Qed.

Theorem identity_fn_applied_twice : forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
    intros.
    rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
    intros.
    destruct b.
    - destruct c.
        + reflexivity.
        + inversion H.
    - destruct c.
        + inversion H.
        + reflexivity.
Qed.

Theorem mul_0_r : forall (n : nat), mult n 0 = 0.
Proof.
    intros.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
    intros.
    induction n as [| n'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat, (eqb n n) = true.
Proof.
    intros.
    induction n as [| n'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.
    
Search (even).

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
    intros.
    induction n as [| n'].
    - simpl. reflexivity.
    - rewrite IHn'. simpl. destruct (even n').
        + reflexivity.
        + reflexivity.
Qed.
    