From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Notation "x <= y" := (Nat.leb x y).
Notation "x >= y" := (Nat.leb y x).
Notation "x > y" := (Nat.ltb y x).
Notation "x < y" := (Nat.ltb x y).

(*------------------DEFINITIONS------------------*)

Definition l_lower : nat := 40.
Definition l_upper : nat := 200.

Inductive heartrate : Type := pair (ba bn : nat).

Notation "( bn , ba )" := (pair bn ba).

(*------------------FUNCTIONS------------------*)
Definition B_nat (p : heartrate) : nat :=
  match p with | (bn,ba) => bn end.

Definition B_art (p : heartrate) : nat :=
  match p with | (bn,ba) => ba end.

Definition B_total (p : heartrate) : nat :=
  (B_nat p) + (B_art p).

Definition is_normal (p : heartrate) : bool :=
  (B_total p >= l_lower) && (B_total p <= l_upper).

Definition need_pace (p : heartrate) : bool :=
  (B_total p) < l_lower.

Definition need_restart (p : heartrate) : bool :=
  (B_total p =? 0) || (B_total p > l_upper).

Definition signal_weak (p : heartrate) : bool :=
  (B_nat p) < l_lower.

Definition signal_strong (p : heartrate) : bool :=
  need_restart p.

(*------------------AXIOMS------------------*)
Axiom axiom1 : forall p : heartrate,
  is_normal p = false
  -> (need_pace p = true) \/ (need_restart p = true).

Axiom axiom2 : forall p : heartrate,
  is_normal p = true
  -> (need_pace p = false) /\ (need_restart p = false).

Axiom axiom3 : forall p : heartrate,
  (B_total p =? 0) = true
  -> (need_pace p = true) /\ (need_restart p = true).

Axiom axiom4 : forall p : heartrate,
  (B_art p >= 60) = true -> (B_nat p =? 0) = true.

(*------------------THEOREMS------------------*)
