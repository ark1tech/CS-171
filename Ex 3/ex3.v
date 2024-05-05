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
    | cons (n : nat) (l : natlist). (*here, n is the head, while l is the tail*)

(* ANSWERS *)

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
    

(* Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
Theorem app_nil_r : ∀ l : natlist,  l ++ [ ] = l.
Theorem rev_app_distr: ∀ l1 l2 : natlist,  rev (l1 ++ l2) = rev l2 ++ rev l1. *)