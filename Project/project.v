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
    A sick client wants you to make an app that maintains a normal heart rate.
    The normal heart rate is 60 to 100 BPM.

    App constraints:

    1) The heart's BPM should stay in between a certain threshold, which we define as 60 and 100 (normal heart rate).
    2) Any time the heart rate goes below this limit, a weak electrical signal is produced to create an artificial heart beat to compensate.
    3) If the heart rate goes above this limit, a strong electrical signal is produced to restart the heart's rhythm.
    4) If there is no natural heartbeat detected within the last 60 seconds, a strong electrical signal is produced to restart the heart's rhythm.
*)

(*------------------DEFINITIONS------------------*)

Definition bpm_lower_limit : nat := 60.
Definition bpm_upper_limit : nat := 100.
Definition bpm_default : nat := 70.

Inductive beat_type : Type :=
    | artificial
    | natural.

Inductive beat : Type :=
    | I (b : beat_type) (n : nat).

(* Return TRUE if opposing beat types -- meaning actual BPM can be solved *)
Definition valid_beat_pair (b1 b2 : beat) : bool :=
    match b1, b2 with
    | I artificial n1, I natural n2 => true
    | I natural n1, I artificial n2 => true
    | I _ n1, I _ n2 => false
    end.

(* actual_bpm : returns actual BPM from natural + artificial, only if different_beat_type is true *)
Definition actual_bpm (b1 b2 : beat) : nat :=
    if valid_beat_pair b1 b2 then
        match b1, b2 with
        | I _ n1, I _ n2 => n1 + n2
        end
    else
        0.
(* ---> MIGHT BE FAULTY *)

(*------------------HEART FUNCTIONS------------------*)

(* axiom to ensure actual BPM is only solved using natural BPM + artificial BPM *)


(* need_pace : Function that returns TRUE if actual BPM is below limit -- meaning abnormal *)
Definition need_pace (b1 b2 : beat) : bool :=
    (actual_bpm b1 b2) <= bpm_lower_limit.

(* need_restart : Function that returns TRUE if actual BPM is above limit or natural BPM is 0 -- meaning needs restarting *)
Definition need_restart (b1 b2 : beat) : bool :=
    let bpm1 :=
        match b1 with
        | I natural n1 => n1
        | I artificial _ => 1
        end in
    let bpm2 :=
        match b2 with
        | I natural n2 => n2
        | I artificial _ => 1
        end in
    (actual_bpm b1 b2 > bpm_upper_limit) || (bpm1 =? 0) || (bpm2 =? 0).

(*------------------HEART AXIOMS------------------*)

(* If beat type is not natural, it is artificial *)
Axiom ax_natural_artificial : forall b : beat,
    match b with
    | I bt _ => bt <> natural
        -> bt = artificial
    end.

(* Vice versa*)
Axiom ax_artificial_natural : forall b : beat,
    match b with
    | I bt _ => bt <> artificial
        -> bt = natural
    end.


(*------------------PACEMAKER FUNCTIONS------------------*)

(* signal_weak : Function that adds 1 to artificial BPM if abnormal BPM *)

(* signal_strong : Function that restarts the heart, i.e. reset to default BPM *)



(*------------------PACEMAKER AXIOMS------------------*)


(*------------------PACEMAKER PROPERTIES------------------*)

(* If artificial BPM is 40, then need_restart is TRUE *)

(* If natural BPM is 0, then both need_pace and need_restart is TRUE *)

(* If BPM is not normal, then need_pace is TRUE or need_restart is TRUE *)
Theorem abnormal_bpm : forall b1 b2,
    match actual_bpm b1 b2 with
    | 
    end.

(* If BPM is normal, then need_pace and need_restart is FALSE *)
Theorem normal_bpm : forall b,
    .