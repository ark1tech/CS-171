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

(* Answers *)

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

    (* destruct b.
    intros.
    destruct c.
    reflexivity.
    inversion H. *)

Qed.

Theorem mul_0_r : ∀ n:nat, n × 0 = 0.
Theorem add_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p.
Theorem eqb_refl : ∀ n : nat, (n =? n) = true.
Theorem even_S : ∀ n : nat, even (S n) = negb (even n).