(* --------------- PREFACE --------------- *)

Inductive list (X:Type) : Type :=
    | nil
    | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
    match count with
    | 0 => nil X
    | S count'
    => cons X x (repeat X x count')
    end.

Notation "x :: l" := (cons x l)
    (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

Fixpoint rev {X:Type} (l:list X) : list X :=
    match l with
    | nil => nil
    | cons h t => app (rev t) (cons h nil)
    end.

Fixpoint length {X : Type} (l : list X) : nat :=
    match l with
    | nil => 0
    | cons _ l' => S (length l')
    end.

Notation "x ++ y" := (app x y)
    (right associativity, at level 60).

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros A l m n.
    induction l as [ | n' l' IHl' ].
    - simpl. reflexivity.
    - simpl. rewrite IHl'. reflexivity.
Qed.

(* Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
    match l with
    | [] => []
    | h :: t =>
        if test h then h :: (filter test t)
        else filter test t
    end. *)

(* Definition partition {X : Type} (test : X -> bool)
    (l : list X) : list X * list X :=
    ((filter test l),(filter (fun n => negb (test n)) l)). *)

(* Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
    match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
    end. *)

(* --------------- ANSWERS --------------- *)

Theorem app_nil_r : forall (X : Type), forall (l : list X),
    l ++ [ ] = l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.

(* Bonus, necessary for rev_involutive *)
Theorem rev_app_distr: forall (X : Type), forall (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros.
    induction l1.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.
(* ^^ there's a way to integrate this sa rev_involutive proof mismo, haven't figured that out. Will give it a try after I gym *)

Theorem rev_involutive : forall (X : Type), forall (l : list X),
    rev (rev l) = l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity.
Qed.

(* Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8]. *)

(* Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l). *)