From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(*------------------HELPERS------------------*)
Fixpoint lebnat (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => lebnat n' m'
        end
    end.

Fixpoint grbnat (n m : nat) : bool :=
    match n with
    | O => false
    | S n' =>
        match m with
        | O => true
        | S m' => grbnat n' m'
        end
    end.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).
Notation "x <= y" := (lebnat x y).
Notation "x > y" := (grbnat x y).

(*------------------USE CASE FOR PACEMAKER ------------------

    A sick client wants you to make an app that maintains his heart
    rate to a normal BPM (40 to 120 BPM).

    App constraints:

    1) The heart's BPM should stay in between 40 and 120 (normal heart rate).
    2) Any time the heart rate goes above or below this limit, a weak electrical signal is produced to create an artificial heart beat.
    3) If there is no natural heartbeat detected within the last 60 seconds, a strong electrical signal is produced to restart the heart.

*)


(*------------------DEFINITIONS------------------*)

Definition bpm_lower_limit : nat := 40.
Definition bpm_upper_limit : nat := 120.

Inductive beat_type : Type :=
    | artificial
    | natural.

Inductive beat_type_bpm : Type :=
    | I (b : beat_type) (n : nat).

(* Definition that differentiates weak from strong electrical signal *)


(*------------------HEART FUNCTIONS------------------*)

(* Definition that returns actual BPM from natural + artificial *)


(*------------------HEART AXIOMS------------------*)

(* If beat type is not natural, it is artificial *)

(* Vice versa*)

(* If BPM is not normal, it is abnormal *)

(* Vice versa *)


(*------------------HEART PROPERTIES------------------*)


(*------------------PACEMAKER FUNCTIONS------------------*)

(* Function that returns TRUE if actual BPM is <40 or >120 -- meaning abnormal *)

(* Function that returns TRUE if natural BPM is 0 -- meaning needs restarting *)




(*------------------PACEMAKER AXIOMS------------------*)

(* Function that adds 1 to artificial BPM if abnormal BPM *)
