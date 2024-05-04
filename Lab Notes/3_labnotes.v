(* Polymorphism *)

Inductive list (X:Type) : Type := 
    | nil
    | cons (x : X) (l : list X).

(* Always indicate yung type (bc of the constructor) *)
Compute(const nat 2 (cons nat 1 (nil nat))) (* [2, 1]*)

Arguments nil {X}.
Arguments cons {X}.

(* Applications: *)
(* Make your own type *)
Inductive icecream : Type :=
    | ube
    | chocolate
    | strawberry.
    
Inductive permissions : Type :=
    | read
    | write.

(* Make a list of custom objects/classes *)

(* Append method *)
Fixpoint append {X : Type} (l1 l2 : list X) : list X :=
    match l1 with 
    | nil => l2
    | cons h t => cons h(app t l2)
    end.

Compute (append (cons ube (cons ube nil)) (cons chocolate cons (strawberry nil))).

(* Append method *)
Fixpoint reverse {X : Type} (l1 l2 : list X) : list X :=
    match l1 with 
    | nil => l2
    | cons h t => cons h(app t l2)
    end.

    (* kapag axiom no need to prove ! *)

(* assert hypothesis => di na need mag for all => what ever data may be, pwede na sya gamitin..? => additional goal and prove the assert (proving theorem inside a theorem )*) 