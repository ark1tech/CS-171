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
  is_normal p = false -> (need_pace p = true) \/ (need_restart p = true).

Axiom axiom2 : forall p : heartrate,
  is_normal p = true -> (need_pace p = false) /\ (need_restart p = false).

Axiom axiom3 : forall p : heartrate,
  B_total p = 0 -> (need_pace p = true) /\ (need_restart p = true).

Axiom axiom4 : forall p : heartrate,
  B_art p = 60 -> (B_nat p =? 0) = true.

Axiom axiom5 : forall p : heartrate,
  B_art p = 0 /\ B_nat p = 0 -> B_total p = 0.

(*------------------THEOREMS------------------*)
Theorem theorem1 : forall p : heartrate,
  need_pace p = true
  -> signal_weak p = true.
Proof.
  intros p H.
  unfold need_pace in H.
  unfold signal_weak.
  unfold B_total in H.
  unfold B_nat in H.
  unfold B_art in H.
  apply Nat.ltb_lt in H.
  destruct p as [bn ba].
  simpl in H.
  simpl.
  apply Nat.ltb_lt.
  lia.
Qed.

Theorem theorem2 : forall p : heartrate,
  (B_art p >= 60) = true
  -> signal_strong p = true.
Proof.
  intros p H.
  unfold signal_strong, need_restart, B_total.

  (* Prove that B_total p =? 0 = true or l_upper <? B_total p = true *)
  assert (H1: ((B_art p =? 60) || (B_art p > 60) = true)).
  {
    apply Nat.leb_le in H.
    destruct (B_art p) eqn:E.
    - rewrite Nat.eqb_eq in H.
      contradiction.
    - destruct n.
      + left. apply Nat.leb_le. auto.
      + right. apply Nat.ltb_lt. simpl. auto.
  }

  destruct H1 as [H_eq | H_gt].
  - (* Case 1: B_art p = 60 *)
    apply Nat.eqb_eq in H_eq.
    apply axiom4 in H_eq.
    apply Nat.eqb_eq in H_eq.
    rewrite H_eq, H_eq.
    simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.eqb_refl.
    reflexivity.

  - (* Case 2: B_art p > 60 *)
    unfold B_total.
    apply Nat.ltb_lt in H_gt.
    rewrite Nat.eqb_neq in H_gt.
    rewrite H_gt.
    simpl.
    apply orb_true_r.
Qed.