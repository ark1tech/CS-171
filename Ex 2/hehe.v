Fixpoint plus (n m: nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end. 

Compute(plus (S O) (S O)).
Compute(plus 2 2).

(* Using data type for nat, comment out your definition of nat *)
(* Allowed for the exercises *)

(* Tricks: 
    - Module search coq
    - Search ( *expression* ) => returns all native theorems in coq
*)

(* Simplification Proofs:
    - The way you define it is everything... 
        - if addition is defined as 0 + n = n, it may not know n + 0 = n. (No definition of commutativity)
*)

(* \forall n \in N, 0 + n = n *)
Theorem my_first_theorem : forall n : nat, 0 + n = n.
Proof.
    intros n. (* This means yung assumption, n \in N *)
    simpl. (* Evaluates the equation (using the defined operation ONLY!) *)
    reflexivity. 
Qed.

(* Proof by rewriting *)
Theorem myth : forall a b c : nat, a = b -> b = c -> a = c.
Proof.
    intros a b c h1 h2.
    rewrite <- h2. (* rewrites/subs using hypothesis *)
    rewrite -> h1.
    reflexivity.
Qed.

Theorem plus_id : forall n m : nat, n = m -> n + n = m + m.
Proof.
    intros n m h.
    rewrite <- h.
    reflexivity.
Qed.


Fixpoint eqb (n m : nat) : bool :=
    match n, m with
    |O , O => true
    |O , S _ => false
    |S _ , O => false
    |S n' , S m' => eqb n' m'
    end.

(* Proof by cases *)
(* nat has two cases: O or S n' *)
Theorem plus_1_neq_0 : forall n : nat, eqb (n + 1) 0 = false.
Proof.
    intros.
    (* destruct n. *)
    (* Rename to avoid confusion sa n': destruct n as [ | n'] *)
    destruct n as [ | n'].
    - (* Case 1 *)
    simpl.
    reflexivity.
    -
    simpl.
    reflexivity.
Qed. 

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof. 
    intros.
    destruct b.
    - 
    simpl.
    reflexivity.
    - 
    simpl.
    reflexivity.
Qed.

(* Proof by induction *)
Theorem fix_for_first : forall n : nat, n + 0 = n.
Proof.
    intros n.
    induction n as [ | n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.

(* Using native theoremn *)
Theorem try : forall n : nat, n + 0 = n.
Proof.
    intros n.
    rewrite -> plus_n_O.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [ | n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.


(* Any defined theorems can be used as a hypothesis anywhere! *)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
    intros n m. 
    induction n as [ | n' IH].
    - simpl. rewrite -> try. reflexivity.
    - simpl. rewrite -> IH. rewrite -> plus_n_Sm. reflexivity.
Qed.
