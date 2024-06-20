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

Definition ltb (n m : nat) : bool := 
    match eqb n m with
    | true => false
    | false => leb n m
    end.

Definition geqnat (m n : nat) : bool := (ltb m n) || (m =? n).


Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).
Notation "x <= y" := (lebnat x y).
Notation "x >= y" := (geqnat x y).
Notation "x > y" := (grbnat x y).
Notation "x < y" := (ltb x y).

(*------------------DEFINITIONS------------------*)

Definition bpm_lower_limit : nat := 40.
Definition bpm_upper_limit : nat := 200.
Definition bpm_default : nat := 70.

(* !!!~~~ COMMENTED OUT == OBSOLETE ~~~!!! *)
(* Inductive beat_type : Type :=
    | artificial
    | natural.

Inductive beat : Type :=
    | I (b : beat_type) (n : nat).

Definition is_artificial (b : beat) : bool :=
    match b with
    | I artificial _ => true
    | _ => false
    end.

Definition is_natural (b : beat) : bool :=
    match b with
    | I natural _ => true
    | _ => false
    end. *)

(* Return TRUE if opposing beat types -- meaning actual BPM can be solved *)
(* Definition valid_beat_pair (b1 b2 : beat) : bool :=
    match b1, b2 with
    | I artificial n1, I natural n2 => true
    | I natural n1, I artificial n2 => true
    | I _ n1, I _ n2 => false
    end. *)

(* actual_bpm : returns actual BPM from natural + artificial, only if valid_beat_pair is true ---> MIGHT BE FAULTY *)
Definition actual_bpm (b1 b2 : beat) : nat :=
    if valid_beat_pair b1 b2 then
        match b1, b2 with
        | I _ n1, I _ n2 => n1 + n2
        end
    else
        0.

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

Definition is_normal (b1 b2 : beat) : bool :=
    if actual_bpm b1 b2 >= bpm_lower_limit  
        then if actual_bpm b1 b2 <= bpm_lower_limit  
            then true
        else false 
    else 
        false.

(*------------------HEART AXIOMS------------------*)

(* If beat type is not natural, it is artificial
Axiom ax_natural_artificial : forall b : beat,
    match b with
    | I bt _ => bt <> natural
        -> bt = artificial
    end. *)

(* Vice versa*)
(* Axiom ax_artificial_natural : forall b : beat,
    match b with
    | I bt _ => bt <> artificial
        -> bt = natural
    end. *)

(* If BPM is not normal, then need_pace is TRUE or need_restart is TRUE *)
Axiom bpm_abnormal : forall b1 b2,
    is_normal b1 b2 = false
    -> need_pace b1 b2 = true \/ need_restart b1 b2 = true.

(* If BPM is normal, then need_pace and need_restart is FALSE *)
Axiom bpm_normal : forall b1 b2 : beat,
    (actual_bpm b1 b2 >= bpm_lower_limit) && (actual_bpm b1 b2 < bpm_upper_limit) = true
    -> need_pace b1 b2 = false /\ need_restart b1 b2 = false.

(*------------------HEART PROPERTIES ------------------*)


(*------------------PACEMAKER FUNCTIONS------------------*)

(* signal_weak : Function that adds 1 to artificial BPM if need_pace is TRUE *)
Definition signal_weak (b1 b2 : beat) : bool :=
    if valid_beat_pair b1 b2 && need_pace b1 b2
        then true
    else false.


(* signal_strong : Function that restarts the heart, i.e. reset to default BPM *)
Definition signal_strong (b1 b2 : beat) : bool :=
    if valid_beat_pair b1 b2 && need_restart b1 b2
        then true
    else false.


(*------------------PACEMAKER AXIOMS------------------*)

(* If artificial BPM is greater than or equal to lower limit, then need_restart is TRUE *)
Axiom artificial_lowerlimit_restart : forall n1 n2 : nat,
    n2 >= bpm_lower_limit = true
    -> need_restart (I natural n1) (I artificial n2) = true.

(* If natural BPM is 0, then both need_pace and need_restart is TRUE *)
Axiom natural_zero_pace_restart : forall n1 n2 : nat,
    n1 =? 0 = true
    -> need_restart (I natural n1) (I artificial n2) = true
        /\ need_pace (I natural n1) (I artificial n2) = true.

Axiom asdfasdf : forall b1 b2: beat, 
    need_restart b1 b2 = true /\ (actual_bpm b1 b2 =? 0) = false -> is_normal (I natural 0) (I artificial 1) = false. 


(*------------------PACEMAKER PROPERTIES------------------*)

(* If need_pace, then BPM-1 still needs pace *)
(* Theorem bpm_S_restart : forall b1 b2 : beat,
    . *)

(* If need_restart and BPM != 0, then BPM+1 is still abnormal *)
Theorem bpm_P_pace : forall b1 b2 : beat,
    (need_restart b1 b2 = true) /\ (actual_bpm b1 b2 =? 0 = false)
    -> (actual_bpm b1 b2 + 1) >= bpm_upper_limit = true.
Admitted.
(* Proof.
    intros.
    apply asdfasdf in H. 
Qed. *)

(* If BPM 0, then BPM+1 does not need restart *)
Theorem bpm_0_restart : forall b1 b2 : beat,
    actual_bpm b1 b2 =? 0 = true
    -> need_restart b1 b2 = true
    -> need_restart b1 b2 = false.
Admitted.

(* -> match b1, b2 with
    | I t1 n1, I t2 n2
        => need_restart (I t1 n1) (I t2 (n2+1)) = false
    end. *)

(* BPM 0 still needs pace *)
Theorem zero_pace : forall n1 n2 : nat,
    n1 =? 0 = true
    -> need_pace (I natural n1) (I artificial n2) = true.
Proof.
    intros.
    apply natural_zero_pace_restart.
    apply H.
Qed.
