From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

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

Definition l_lower : nat := 40.
Definition l_upper : nat := 200.

Inductive heartrate : Type := pair (ba bn : nat).
Notation "( x , y )" := (pair x y).

(*------------------FUNCTIONS------------------*)
Definition B_nat (p : heartrate) : nat :=
  match p with
  | (bn,ba) => bn
  end.

Definition B_art (p : heartrate) : nat :=
  match p with
  | (bn,ba) => ba
  end.

Definition B_total (p : heartrate) : nat :=
  (B_nat p) + (B_art p).
