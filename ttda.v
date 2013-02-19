(* Axiom em : forall (P : Prop), P \/ (not P). *)

Inductive type2prop (A : Type) : Prop :=
  type2prop_intro : A -> type2prop A.

Inductive prop2type (P : Prop) : Type :=
  prop2type_intro : P -> prop2type P.

(*
Theorem ttda_to_em_type :
  (forall (A B : Type) (P : A -> B -> Prop),
    (forall (a : A), exists b, P a b) ->
    (exists f, forall (a : A), P a (f a))) ->
  forall (A : Type), A + (A -> False).
*)

Lemma em_type_to_ttda_informative :
  (forall (A : Type), A + (A -> False)) ->
  (forall (A B : Type) (P : A -> B -> Prop),
    (forall (a : A), exists b, P a b) ->
    (forall (a : A), { b : B | P a b})).
intros em_type A B P f_pf a.
elim (em_type {b : B | P a b}).
 intro; assumption.
 
 intro not_ex; elimtype False.
 elim (f_pf a).
 intros b b_pf; apply not_ex; exists b; assumption.
Qed.

Theorem em_type_to_ttda :
  (forall (A : Type), A + (A -> False)) ->
  (forall (A B : Type) (P : A -> B -> Prop),
    (forall (a : A), exists b, P a b) ->
    (exists f, forall (a : A), P a (f a))).
intros em_type A B P f_pf.
exists
 (fun a => proj1_sig (em_type_to_ttda_informative em_type A B P f_pf a)).
intro; apply (proj2_sig (em_type_to_ttda_informative em_type A B P f_pf a)).
Qed.

Theorem em_type_to_em :
  (forall (A : Type), A + (A -> False)) ->
  (forall (P : Prop), P \/ ~P).
intros em_type P.
elim (em_type (prop2type P)).
 intro p2t; elim p2t; left; assumption.
 
 intro not_p2t; right; intro p; apply not_p2t; apply prop2type_intro;
  assumption.
Qed.
