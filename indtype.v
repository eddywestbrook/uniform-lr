Require Import List.

(***
 The universal inductive type

 Intuitively, inductive datatype a : (x1:A1) -> ... (xn:An) -> s with
 constructors ci : (y1:Bi1) -> ... -> (ym:Bim) -> a Mi1 .. Min is
 represented FIXME

 ***)


Inductive UCtorType (Index : Set) : Type :=
| UCtorType_Cons_Rec (index : Index) (rest : UCtorType Index)
  : UCtorType Index
| UCtorType_Cons_NonRec (A : Set) (rest : A -> UCtorType Index)
  : UCtorType Index
| UCtorType_Nil (index : Index) : UCtorType Index
.

Fixpoint UCT2ParamType (Index : Set) (ctype : UCtorType Index) {struct ctype}
  : Set :=
  match ctype with
    | UCtorType_Cons_Rec index rest => UCT2ParamType Index rest
    | UCtorType_Cons_NonRec A rest => { a : A & UCT2ParamType Index (rest a) }
    | UCtorType_Nil index => unit
  end.

Definition UCTopt2ParamType (Index : Set) (ct_opt : option (UCtorType Index)) :=
  match ct_opt with
    | Some ctype => UCT2ParamType Index ctype
    | None => False
  end.

Fixpoint UCTParams2RecIndices
  (Index : Set) (ctype : UCtorType Index) {struct ctype}
  : UCT2ParamType Index ctype -> list Index
  := match ctype as ctype' return UCT2ParamType Index ctype' -> list Index with
       | UCtorType_Cons_Rec index rest =>
         fun params => index :: UCTParams2RecIndices Index rest params
       | UCtorType_Cons_NonRec A rest =>
         fun params => match params with
                         existT a params' =>
                           UCTParams2RecIndices Index (rest a) params'
                       end
       | UCtorType_Nil index => fun _ => nil
     end.

Definition UCToptParams2RecIndices
  (Index : Set) (ctype_opt : option (UCtorType Index))
  : UCTopt2ParamType Index ctype_opt -> list Index
  := match ctype_opt as c' return UCTopt2ParamType Index c' -> list Index with
       | Some ctype => UCTParams2RecIndices Index ctype
       | None => fun (params : False) => match params with end
     end.

Fixpoint UCTParams2Index
  (Index : Set) (ctype : UCtorType Index) {struct ctype}
  : UCT2ParamType Index ctype -> Index
  := match ctype as ctype' return UCT2ParamType Index ctype' -> Index with
       | UCtorType_Cons_Rec index rest =>
         fun params => UCTParams2Index Index rest params
       | UCtorType_Cons_NonRec A rest =>
         fun params =>
           match params with
             existT a params' => UCTParams2Index Index (rest a) params'
           end
       | UCtorType_Nil index => fun _ => index
     end.

Definition UCToptParams2Index
  (Index : Set) (ctype_opt : option (UCtorType Index))
  : UCTopt2ParamType Index ctype_opt -> Index
  := match ctype_opt as c' return UCTopt2ParamType Index c' -> Index with
       | Some ctype => UCTParams2Index Index ctype
       | None => fun (params : False) => match params with end
     end.


Inductive UIndType (Index : Set) (ctors : nat -> option (UCtorType Index))
  : Index -> Set :=
  | MkUIndType (i : nat) (params : UCTopt2ParamType Index (ctors i))
    (rec_args :
      UIndType_list Index ctors
        (UCToptParams2RecIndices Index (ctors i) params))
    : UIndType Index ctors (UCToptParams2Index Index (ctors i) params)
with UIndType_list (Index : Set) (ctors : nat -> option (UCtorType Index))
  : list Index -> Set :=
  | UIndType_Nil : UIndType_list Index ctors nil
  | UIndType_Cons (index : Index) (l : list Index)
    : UIndType Index ctors index ->
      UIndType_list Index ctors l ->
      UIndType_list Index ctors (index :: l)
.
