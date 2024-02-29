(* 
Lists 
    - Inductive keyword
    - Pair keyword to indicate a two-tuple
*)

Inductive nat : Type :=
    | O
    | S (n : nat).

Inductive natprod : Type :=
    | pair (n1  n2 : nat). (* Constructor of the data type *)

Definition frst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end. 
    
Definition scnd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end. 

Theorem surjective_pairing : forall (n m : nat), (n, m) = (frst (n, m), scnd (n, m)).
Proof.
    intros.
    reflexivity.
Qed.

(* Using the two-tuple data type natprod *)
Theorem surjective_pairing' = forall p : natprod, p = (frst p, scnd p).  
Proof. 
    intros.
    simpl.          (* wont work kasi di nya alam pano gagawin *)
    destruct p.     (* malalaman nya na natural numbers pala yung tuple *)
    reflexivity.    (* k na ! *)
Qed.

(*  
methods for lists
    - cons (nat, list)
        - cons (1, [[2, 3, 4]]) -> [1, 2, 3, 4] 
        - appends to the list head
    - nil
*)

Inductive natlist : Type := 
    | nil 
    | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(* 
.. means you are referring inductively   
 (cons 1 (cons 2 (cons 3 (cons 4 []))) => (cons 1 .. cons 4 [])
*)

Fixpoint repeat_list (n count : nat) : natlist :=
    match count with 
    | O => [ ]
    | S count' => n :: (repeat n count')
    end.

Fixpoint len_list (l : natlist) : nat :=
    match l with
    | nil => O 
    | h::t => l + (length t)
    end.

Fixpoint append_list (l1 l2 : natlist) : natlist := 
    match l1 with 
    | nil => l2
    | h::t => h :: (append_list t l2)
    end.

Definition head_list (l : natlist) : nat :=
    match l with
    | nil => O 
    | h::t => h
    end.

Definition tail_list (l : natlist) : nat :=
    match l with
    | nil => O 
    | h::t => t
    end.

Fixpoint count (v : nat) (l : natlist) : nat :=
    match l with
    | nil => O
    | h::t => 
        if (eqb h v) then S (count v t)
        else (count v t).
    end.

(* Avoid if else as much as possible sabi ni sir *)
Fixpoint count2 (v : nat) (l : natlist) : nat :=
    match l with
    | nil => O
    | h::t => 
        match (eqb h v) with
        | true => S (count v t)
        | false => count v t 
        end
    end.

Theorem tl_length_pred : forall l : natlist, pred (len_list l) = len_list (t l).
Proof.
    intros. 
    destruct l as [ | h l'].
    - reflexivity. 
    - reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist, append_list (l1 append_list(l2 l3)) = append_list(append_list(l1 l2) l3).
(* If hindi gumana yung simpl reflexivity, baka induction ang solution and not destruct *)
Proof.
    intros. 
    induction l1 as [ | h l' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.
 
Theorem reverse_list (l : natlist) : natlist := 
    match l with 
    | nil => nil
    | h::t => append_list(t h)
    end.

Theorem app_length : for l1 l2 : natlist, len_list (append_list(l1 l2)) = len_list(l1) + len_list(l2).
Proof. 
    intros.
    induction l1 as [ | h t IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
Qed.    

Theroem rev_length : for l : natlist, len_list(reverse_list l) = len_list l.
Proof. 
    intros.
    induction l as [ | h t IH].
    - reflexivity.
    (* We apply theorems and IH *)
    (* add_comm and add_0_r *)
    - simpl. rewrite -> app_length. rewrite -> IH. rewrite -> (* commutativity theorem *). reflexivity. 
Qed.





