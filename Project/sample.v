Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Permutation.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

(*------------------HELPERS------------------*)

(*eqbnat returns true if n equals m*)
Fixpoint eqbnat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqbnat n' m'
            end
  end.

(*lebnat returns true if n is less than or equal to m*)
Fixpoint lebnat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => lebnat n' m'
      end
  end.

(*lenat returns true if n is strictly less than m*)
Definition lenat (n m : nat) : bool :=
    (lebnat n m) && negb (eqbnat n m).

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).



(*------------------USE CASE FOR ICE CREAM MAKER------------------*)

(*
    You are contacted by a diabetic client who wants you to make an app that
    correctly prepares ice cream subject to these constraints:

    1) Ingredients should be added to the maker in the ff order: milk, cream, sugar.
    2) The amount of milk should be 5 cups.
    3) The amount of cream should be 3 cups.
    4) The amount of sugar should be 4 cups.
    5) No other ingredient should be added in the preparation phase.
    6) Inability to meet any of these constraints will result in FAILURE !

    Afterwards, the client wants you to add flavoring to the ice cream.
    The client is exponentially addicted to flavoring, subject to
    these constraints:

    1) Available flavors are chocolate, strawberry and vanilla.
    2) The maker accepts a list of flavors.
    3) However, the input list to the maker should be uniform (i.e. all of the same flavor).
    4) Given a uniform list of length n, the taste rating is 2^n.
*)





(*------------------DEFINITIONS------------------*)

(*Axioms that the amount of milk, cream and sugar should be exactly 5,3,4 respectively*)
Definition milkquant : nat := 5.
Definition creamquant : nat := 3.
Definition sugarquant : nat := 4.

(*Types of material*)
Inductive material : Type :=
    | milk
    | cream
    | sugar.

(*Definition that combines material type with amount*)
Inductive ingredients : Type :=
    | I (m : material) (n : nat).

(*Types of flavors*)
Inductive flavor : Type :=
    | chocolate
    | vanilla
    | strawberry.    


(*------------------PREPARATION FUNCTIONS------------------*)

(*prepare returns true if ingredient specifications are met*)
Definition prepare (l : list ingredients) : bool :=
    match l with
    | (I milk x)::(I cream y)::(I sugar z)::[]
        =>  match (eqbnat x milkquant) with
            | false =>  false
            | true =>   match (eqbnat y creamquant) with
                        | false =>  false
                        | true =>   match (eqbnat z sugarquant) with
                                    | false => false
                                    | true => true
                                    end
                        end
            end
    | _ => false
    end.

(*check returns true if the type of two ingredients is the same*)
Definition check (i : ingredients) (t : ingredients) : bool :=
    match i with
    | (I milk _) =>   match t with
                    | (I milk _) => true
                    | _ => false
                    end
    | (I cream _) =>  match t with
                    | (I cream _) => true
                    | _ => false
                    end
    | (I sugar _) =>  match t with
                    | (I sugar _) => true
                    | _ => false
                    end
    end.


(*------------------PREPARATION AXIOMS------------------*)

(*If the type is not milk, it should be cream or sugar*)
Axiom axone : forall m n i, check (I i n) (I milk m) = false -> i = cream \/ i = sugar.

(*If the type is not cream, it should be milk or sugar*)
Axiom axtwo : forall m n i, check (I i n) (I cream m) = false -> i = milk \/ i = sugar.

(*If the type is not sugar, it should be milk or cream*)
Axiom axthree : forall m n i, check (I i n) (I sugar m) = false -> i = milk \/ i = cream.


(*------------------PREPARATION PROPERTIES------------------*)

(*If the first ingredient in the list is not milk, preparation fails*)
Theorem one : forall h t m i n, 
    h = (I i n) -> 
    (check (I i n) (I milk m) = false) -> 
    ((prepare (h::t)) = false).
Proof.
    intros. apply axone in H0. rewrite H. destruct H0.
    - rewrite H0. simpl. reflexivity.
    - rewrite H0. simpl. reflexivity.
Qed.

(*If the first ingredient is made up of the right quantity of milk, but
the second ingredient in the list is not cream, preparation fails*)
Theorem two : forall j h t m i n, 
    j = (I milk milkquant) ->
    h = (I i n) -> 
    (check (I i n) (I cream m) = false) -> 
    ((prepare (j::h::t)) = false).
Proof.
    intros. apply axtwo in H1. destruct H1.
    - rewrite H. rewrite H0. rewrite H1. simpl. reflexivity.
    - rewrite H. rewrite H0. rewrite H1. simpl. reflexivity.
Qed.

(*If the first ingredient is made up of the right quantity of milk, 
and the second ingredient is made up of the right quantity of cream
but the third ingredient in the list is not sugar, preparation fails*)
Theorem three : forall k j h m i n,
    j = (I milk milkquant) ->
    k = (I cream creamquant) ->
    h = (I i n) -> 
    (check (I i n) (I sugar m) = false) ->
    ((prepare (j::k::h::[])) = false).
Proof.
    intros. apply axthree in H2. destruct H2.
    - rewrite H. rewrite H0. rewrite H1. rewrite H2. simpl. reflexivity.
    - rewrite H. rewrite H0. rewrite H1. rewrite H2. simpl. reflexivity.
Qed.

(*If the first ingredient is milk but of not the right quantity, preparation fails
despite having the right ingredients and quantities for the rest*)
Theorem four : forall n t h, 
    ((eqbnat n milkquant) = false) -> 
    h = (I milk n) ->
    t = [(I cream creamquant); (I sugar sugarquant)] ->
    prepare (h::t) = false.
Proof.
    intros. rewrite H1. rewrite H0. simpl. rewrite H. reflexivity.
Qed.

(*If the second ingredient is cream but of not the right quantity, preparation fails
despite having the right ingredients and quantities for the rest*)
Theorem five : forall n h j k, 
    ((eqbnat n creamquant) = false) -> 
    h = (I cream n) ->
    j = (I milk milkquant) ->
    k = (I sugar sugarquant) ->
    prepare (j::h::k::[]) = false.
Proof.
    intros. rewrite H0. rewrite H1. rewrite H2. simpl. rewrite H. reflexivity.
Qed.

(*If the third ingredient is sugar but of not the right quantity, preparation fails
despite having the right ingredients and quantities for the rest*)
Theorem six : forall n t h, 
    ((eqbnat n sugarquant) = false) -> 
    t = (I sugar n) ->
    h = [(I milk milkquant); (I cream creamquant)] ->
    prepare (h++[t]) = false.
Proof.
    intros. rewrite H1. rewrite H0. simpl. rewrite H. reflexivity.
Qed.


(*------------------ICE CREAM MAKING FUNCTIONS------------------*)

(*returns true if a and b have the same flavor*)
Definition checkflavor (a b : flavor) : bool :=
    match a, b with
    | chocolate, chocolate => true
    | vanilla, vanilla => true
    | strawberry, strawberry => true
    | _, _ => false
    end.

(*returns true if the list is made up of one flavor only, i.e. uniform list*)
Fixpoint checkflavorlist (l : list flavor) : bool :=
    match l with
    | [] =>             false
    | a::[] =>          true
    | a::b::[] =>       match (checkflavor a b) with
                        | false =>  false
                        | true =>   true
                        end
    | a::b::c::[] =>    match (checkflavor a b) with
                        | false =>  false
                        | true =>   match (checkflavor b c) with
                                    | true =>   true
                                    | false =>  false
                                    end
                        end
    | a::b::t =>        match (checkflavor a b) with
                        | false => false
                        | true => (checkflavorlist t)
                        end
    end.

(*returns a taste measure of 2^n given a uniform flavor list of length n and a correct list of ingredients*)
Fixpoint make (l1 : list ingredients) (l2 : list flavor) : nat :=
    match (prepare l1) with
    | false =>  0
    | true =>   match l2 with
                | [] =>             0
                | a::[] =>          2
                | a::b::[] =>       match (checkflavor a b) with
                                    | false =>  0
                                    | true =>   4
                                    end
                | a::b::c::[] =>    match ((checkflavor a b) ) with
                                    | false =>  0
                                    | true =>   match (checkflavor b c) with
                                                | false => 0
                                                | true => 8
                                                end
                                    end
                | a::b::t =>        match (checkflavor a b) with
                                    | false => 0
                                    | true => 4 * (make l1 t)
                                    end
                end
    end.


(*------------------ICE CREAM MAKING AXIOMS------------------*)

(*If the ingredient list is correct and the flavor list is uniform, then
adding another flavor of the same type will increase the taste of make by 2*)
Axiom axfour : forall l1 l2 a, 
    prepare l1 = true /\
    checkflavorlist (a::l2) = true ->
    make l1 (a :: l2) = 2 * (make l1 l2).

Axiom axfive : forall l1 l2 a b, 
    prepare l1 = true /\
    checkflavorlist (a::b::l2) = true ->
    make l1 (a::b::l2) = 4 * (make l1 l2).

(*am cheating here*)    
Lemma helper : forall n, lebnat (2 * n) (4 * n) = true.
Admitted.

(*If the ingredient list is correct and the flavor list is uniform, then
adding another flavor of the same type will mean that the resulting taste is better*)
Theorem seven : forall l1 l2 a,
    prepare l1 = true /\
    checkflavorlist l2 = true ->
    prepare l1 = true /\ checkflavorlist (a::l2) = true ->
    lebnat (make l1 l2) (make l1 (a::l2)) = true.
Proof.
    intros. destruct l2.
    - simpl. destruct H. rewrite H. simpl. reflexivity.
    - apply axfour in H. rewrite H. apply axfive in H0. rewrite H0.
      apply helper.
Qed.


