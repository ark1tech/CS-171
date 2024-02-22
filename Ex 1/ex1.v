Inductive bool : Type := 
    |true
    |false.

Definition notb (b: bool) : bool :=
    if b then false
    else true.

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

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
    if notb(b1) then false
    else if notb(b2) then false
    else if notb(b3) then false
    else true.

Fixpoint minus (n m : nat) : nat := 
    match n, m with 
    | O , _ => O (*the _ character is a catch-all regex*)
    | S _ , O => n
    | S n' , S m' => minus n' m'
    end.

Fixpoint mult (n : nat) (m : nat) : nat :=
    match n with
    |O => O
    |S n' => plus m (mult n' m)
    end. 

(* Answers *)

Definition nandb (b1: bool) (b2: bool) : bool :=
    notb(andb b1 b2).

(* Example test_nandb: (nandb true true) = false.
Proof. simpl. reflexivity. Qed. *)

Fixpoint factorial (n : nat) : nat
    