From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(*------------------HELPERS------------------*)


Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(*------------------USE CASE FOR PACEMAKER ------------------
    A client...

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

(* Definition that calculates actual BPM from natural + artificial *)

(* Definition that states 1 if BPM is normal, 0 if BPM is abnormal *)

(* Definition that differentiates weak from strong electrical signal *)


(*------------------PREPARATION FUNCTIONS------------------*)

(* Function that returns TRUE if actual BPM is <40 or >120 *)

(* Function that returns TRUE if natural BPM is 0 *)

(* Function that adds 1 to artificial BPM if weak signal is true *)


(*------------------PREPARATION AXIOMS------------------*)

(* If beat type is not natural, it is artificial *)

(* Vice versa*)

(* If *)


(*------------------PREPARATION PROPERTIES------------------*)


(*------------------PACEMAKER FUNCTIONS------------------*)


(*------------------PACEMAKER AXIOMS------------------*)

