Require Import List.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.


Definition my_nth : forall (A : Type) (l : list A) (n : nat), n < length l -> A.
intros A l. induction l.
intros n lt0; elimtype False; apply (lt_n_O n); assumption.
intro n; induction n.
intro; apply a.
intro ltSS; apply (IHl n); apply lt_S_n; assumption.
Defined.

Implicit Arguments my_nth [A].


(***
 *** The universal inductive type
 ***)

Inductive UIndType (A : Set) (ctors : list { B : Set & B -> (list A * A)})
  : A -> Set :=
  | MkUIndType (i : nat) (lt : i < length ctors) (b : projT1 (my_nth ctors i lt))
    (rec_args : UIndType_list A ctors (fst (projT2 (my_nth ctors i lt) b)))
    : UIndType A ctors (snd (projT2 (my_nth ctors i lt) b))
with UIndType_list (A : Set) (ctors : list { B : Set & B -> (list A * A)})
  : list A -> Set :=
  | ITI_Nil : UIndType_list A ctors nil
  | ITI_Cons (a : A) (l : list A) : UIndType A ctors a ->
    UIndType_list A ctors l ->
    UIndType_list A ctors (a :: l)
.
