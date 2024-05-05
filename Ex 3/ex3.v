Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Inductive natprod : Type :=
    | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
    match p with
    | (x,y) => x
    end.

Definition snd (p : natprod) : nat :=
    match p with
    | (x,y) => y
    end.

Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
    (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y)
    (right associativity, at level 60).

Theorem app_associative: forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros.
    induction l1.
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1. reflexivity.
Qed.

Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

(* ---------- ANSWERS ---------- *)

Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
    intros.
    destruct p.
    simpl.
    reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
Proof.
    intros.
    destruct p.
    simpl.
    reflexivity.
Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
        match h with
        | O => nonzeros t
        | S h' => h :: (nonzeros t)
        end
    end.
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
        match (even h) with
        | true => oddmembers t
        | false => h :: (oddmembers t)
        end
    end.
Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Theorem app_nil_r : forall l : natlist,  l ++ [ ] = l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros.
    induction l1.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHl1. apply app_associative.
Qed.