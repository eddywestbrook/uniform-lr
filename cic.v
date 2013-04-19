Require Import List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Arith_base.
Load indtype.

(*** terms and helper defs ***)

Definition level := nat.

Inductive Term : Set :=
| Prp : Term
| Tp : level -> Term
| Pi : Term -> Term -> Term
| IndType : IndInfo -> TermList -> Term
| Var : nat -> Term
| App : Term -> Term -> Term
| Lam : Term -> Term -> Term
| CtorApp : IndInfo -> nat -> TermList -> Term
| Elim : ElimInfo -> TermList -> Term -> Term
with IndInfo :=
| MkIndInfo : Term -> (nat -> TermOpt) -> IndInfo
with ElimInfo :=
| MkElimInfo : IndInfo -> nat -> Term -> (nat -> TermOpt) -> ElimInfo
with TermOpt :=
| SomeTerm : Term -> TermOpt
| NoTerm : TermOpt
with TermList :=
| TL_nil : TermList
(* README: TermLists cons to the right *)
| TL_cons : TermList -> Term -> TermList
.

Definition TermMSeq := nat -> TermOpt.

(* Definition Ctx : Set := list Term. *)
(* Definition Ctx : Set := TermList. *)


(***
 *** operations on my fake lists (stupid Coq)
 ***)

Fixpoint TL_len (l : TermList) :=
  match l with
    | TL_nil => 0
    | TL_cons l' _ => S (TL_len l')
  end.

Fixpoint TL_app (l1 l2 : TermList) :=
  match l2 with
    | TL_nil => l1
    | TL_cons l2' M => TL_cons (TL_app l1 l2') M
  end.

Fixpoint TL_nth_or_fail (n : nat) (l : TermList) : Term + { TL_len l <= n } :=
  match n as n', l as l' return Term + { TL_len l' <= n' } with
    | n, TL_nil => inright _ (le_O_n n)
    | 0, TL_cons _ M => inleft _ M
    | (S n'), (TL_cons l' _) =>
      match TL_nth_or_fail n' l' with
        | inleft M => inleft _ M
        | inright pf => inright _ (le_n_S _ _ pf)
      end
  end.

Inductive TL_isNth (T : Term) : nat -> TermList -> Set :=
| isNth_TL_base (l : TermList) : TL_isNth T 0 (TL_cons l T)
| isNth_TL_cons (n : nat) (T' : Term) (l : TermList)
  : TL_isNth T n l -> TL_isNth T (S n) (TL_cons l T').


(***
 *** Helper definitions for manipulating terms
 ***)

Fixpoint apply (M : Term) (l : TermList) {struct l} : Term :=
  match l with
    | TL_nil => M
    | TL_cons l' N => App (apply M l') N
  end.

Definition apply1opt (M : Term) (Nopt : TermOpt) : Term :=
  match Nopt with
    | NoTerm => M
    | SomeTerm N => App M N
  end.

Fixpoint piMulti (As : TermList) (B : Term) : Term :=
  match As with
    | TL_nil => B
    | TL_cons As' An => piMulti As' (Pi An B)
  end.

(* Pattern-match on a term of the form (M N1 .. Nn) and return a pair
   of (M, N1 .. Nn)
 *)
Fixpoint matchApply (M : Term) : Term * TermList :=
  match M with
    | App M1 M2 => (fst (matchApply M1), TL_cons (snd (matchApply M1)) M2)
    | _ => (M, TL_nil)
  end.

(* Match a term of the form (x1:A1) -> .. -> (xn:An) -> M (N1 .. Nm) and
   return (As ++ A1 .. An, M, N1 .. Nm)
 *)
Fixpoint matchPiApplyH (As : TermList) (M : Term)
  : TermList * (Term * TermList) :=
  match M with
    | Pi A B => matchPiApplyH (TL_cons As A) B
    | _ => (As, matchApply M)
  end.

Definition matchPiApply (M : Term) := matchPiApplyH TL_nil M.
Definition matchPiApply_Pis (M : Term) := fst (matchPiApply M).
Definition matchPiApply_head (M : Term) := fst (snd (matchPiApply M)).
Definition matchPiApply_args (M : Term) := snd (snd (matchPiApply M)).



(***
 *** helper definitions for variable occurrences
 ***)

Inductive occurs (n : nat) : Term -> Set :=
(* no occurrences for Sort *)
| OccursPi1 (A B : Term) : occurs n A -> occurs n (Pi A B)
| OccursPi2 (A B : Term) : occurs (S n) B -> occurs n (Pi A B)
| OccursIndType1 (info : IndInfo) (params : TermList)
  : occursInfo n info -> occurs n (IndType info params)
| OccursIndType2 (info : IndInfo) (params : TermList)
  : occursList n params -> occurs n (IndType info params)
| OccursVar : occurs n (Var n)
| OccursApp1 (M N : Term) : occurs n M -> occurs n (App M N)
| OccursApp2 (M N : Term) : occurs n N -> occurs n (App M N)
| OccursLam1 (A M : Term) : occurs n A -> occurs n (Lam A M)
| OccursLam2 (A M : Term) : occurs (S n) M -> occurs n (Lam A M)
| OccursCtorApp1 (info : IndInfo) (i : nat) (params : TermList)
  : occursInfo n info -> occurs n (CtorApp info i params)
| OccursCtorApp2 (info : IndInfo) (i : nat) (params : TermList)
  : occursList n params -> occurs n (CtorApp info i params)
| OccursElim1 (einfo : ElimInfo) (params : TermList) (scrut : Term)
  : occursElimInfo n einfo -> occurs n (Elim einfo params scrut)
| OccursElim2 (einfo : ElimInfo) (params : TermList) (scrut : Term)
  : occursList n params -> occurs n (Elim einfo params scrut)
| OccursElim3 (einfo : ElimInfo) (params : TermList) (scrut : Term)
  : occurs n scrut -> occurs n (Elim einfo params scrut)
with occursMSeq (n : nat) : TermMSeq -> Set :=
| OccursSeq (patts : TermMSeq) (j : nat)
  : occursOpt n (patts j) -> occursMSeq n patts
with occursList (n : nat) : TermList -> Set :=
| OccursListBase (l : TermList) (M : Term)
  : occurs n M -> occursList n (TL_cons l M)
| OccursListCons (l : TermList) (M : Term)
  : occursList n l -> occursList n (TL_cons l M)
with occursOpt (n : nat) : TermOpt -> Set :=
| OccursOpt (M : Term) : occurs n M -> occursOpt n (SomeTerm M)
with occursInfo (n : nat) : IndInfo -> Set :=
| OccursMkIndInfo1 (kind : Term) (ctorTypes : TermMSeq)
  : occurs n kind -> occursInfo n (MkIndInfo kind ctorTypes)
| OccursMkIndInfo2 (kind : Term) (ctorTypes : TermMSeq)
  : occursMSeq n ctorTypes -> occursInfo n (MkIndInfo kind ctorTypes)
with occursElimInfo (n : nat) : ElimInfo -> Set :=
| OccursMkElimInfo1 (info : IndInfo) (i : nat) (P : Term) (patts : TermMSeq)
  : occursInfo n info -> occursElimInfo n (MkElimInfo info i P patts)
| OccursMkElimInfo2 (info : IndInfo) (i : nat) (P : Term) (patts : TermMSeq)
  : occurs n P -> occursElimInfo n (MkElimInfo info i P patts)
| OccursMkElimInfo3 (info : IndInfo) (i : nat) (P : Term) (patts : TermMSeq)
  : occursMSeq n patts -> occursElimInfo n (MkElimInfo info i P patts)
.

Inductive notOccurs (n : nat) : Term -> Set :=
| NotOccursPrp (i : nat) : notOccurs n Prp
| NotOccursTp (i : nat) : notOccurs n (Tp i)
| NotOccursPi (A B : Term)
  : notOccurs n A -> notOccurs (S n) B -> notOccurs n (Pi A B)
| NotOccursIndType (info : IndInfo) (params : TermList)
  : notOccursInfo n info -> notOccursList n params ->
    notOccurs n (IndType info params)
| NotOccursVar (m : nat) : (n <> m) -> notOccurs n (Var m)
| NotOccursApp (M N : Term)
  : notOccurs n M -> notOccurs n N -> notOccurs n (App M N)
| NotOccursLam (A M : Term)
  : notOccurs n A -> notOccurs (S n) M -> notOccurs n (Lam A M)
| NotOccursCtorApp (info : IndInfo) (i : nat) (params : TermList)
  : notOccursInfo n info -> notOccurs n (CtorApp info i params)
| NotOccursElim (einfo : ElimInfo) (params : TermList) (scrut : Term)
  : notOccursElimInfo n einfo -> notOccursList n params -> notOccurs n scrut ->
    notOccurs n (Elim einfo params scrut)
with notOccursList (n : nat) : TermList -> Set :=
| NotOccursNil : notOccursList n TL_nil
| NotOccursCons (l : TermList) (M : Term)
  : notOccursList n l -> notOccurs n M -> notOccursList n (TL_cons l M)
with notOccursTermOpt (n : nat) : TermOpt -> Set :=
| NotOccursNoTerm : notOccursTermOpt n NoTerm
| NotOccursSomeTerm (M : Term) :
  notOccurs n M -> notOccursTermOpt n (SomeTerm M)
with notOccursMSeq (n : nat) : TermMSeq -> Set :=
| NotOccursMSeq (seq : TermMSeq)
  : (forall (i : nat), notOccursTermOpt n (seq i)) -> notOccursMSeq n seq
with notOccursInfo (n : nat) : IndInfo -> Set :=
| NotOccursMkIndInfo (kind : Term) (ctorTypes : TermMSeq)
  : notOccurs n kind -> notOccursMSeq n ctorTypes ->
    notOccursInfo n (MkIndInfo kind ctorTypes)
with notOccursElimInfo (n : nat) : ElimInfo -> Set :=
| NotOccursMkElimInfo (info : IndInfo) (i : nat) (P : Term) (patts : TermMSeq)
  : notOccursInfo n info -> notOccurs n P -> notOccursMSeq n patts ->
    notOccursElimInfo n (MkElimInfo info i P patts)
.


(*** substitution and lifting ***)

(* README: k is the amount we are incrementing the variables, and n is the
 * number of variable bindings under which we have traversed so far *)
Fixpoint lift (n k : nat) (M : Term) {struct M} : Term :=
  match M with
    | Prp => Prp
    | Tp i => Tp i
    | Pi A B => Pi (lift n k A) (lift (S n) k B)
    | IndType info params =>
      IndType (liftIndInfo n k info) (liftList n k params)
    | Var i =>
      match le_lt_dec n i with
        | left _ => Var (i + k) (* case: i >= n *)
        | right _ => Var i (* case: i < n *)
      end
    | App M1 M2 => App (lift n k M1) (lift n k M2)
    | Lam A M1 => Lam (lift n k A) (lift (S n) k M1)
    | CtorApp info i params =>
      CtorApp (liftIndInfo n k info) i (liftList n k params)
    | Elim einfo params scrut =>
      Elim (liftElimInfo n k einfo) (liftList n k params) (lift n k scrut)
  end
with liftList (n k : nat) (l : TermList) {struct l} :=
  match l with
    | TL_nil => TL_nil
    | TL_cons l' M => TL_cons (liftList n k l') (lift n k M)
  end
with liftOpt (n k : nat) (M_opt : TermOpt) {struct M_opt} :=
  match M_opt with
    | SomeTerm M => SomeTerm (lift n k M)
    | NoTerm => NoTerm
  end
with liftIndInfo (n k : nat) (info : IndInfo) {struct info} :=
  match info with
    | MkIndInfo sort ctors =>
      MkIndInfo (lift n k sort) (fun i => liftOpt n k (ctors i))
  end
with liftElimInfo (n k : nat) (einfo : ElimInfo) :=
  match einfo with
    MkElimInfo info i P patts =>
      MkElimInfo (liftIndInfo n k info) i (lift n k P)
      (fun i => liftOpt n k (patts i))
  end
  .

(* Grr, Coq cannot handle liftMSeq in the above mutal definitions... *)
Definition liftMSeq (n k : nat) (seq : TermMSeq) :=
  fun i => liftOpt n k (seq i).


Definition Subst := TermList.

(* README: n is the number of binders we have traversed *)
Fixpoint substH (n : nat) (s : Subst) (M : Term) {struct M} : Term :=
  match M with
    | Prp => Prp
    | Tp i => Tp i
    | Pi A B => Pi (substH n s A) (substH (S n) s B)
    | IndType info params =>
      IndType (substIndInfo n s info) (substList n s params)
    | Var i =>
      match le_lt_dec n i with
        | right _ => Var i (* case: i < n *)
        | left _ => (* case: i >= n *)
          match TL_nth_or_fail (i - n) s with
            | inleft N => lift 0 n N
            | _ => Var (i + n)
          end
      end
    | App M1 M2 => App (substH n s M1) (substH n s M2)
    | Lam A M1 => Lam (substH n s A) (substH (S n) s M1)
    | CtorApp info i params =>
      CtorApp (substIndInfo n s info) i (substList n s params)
    | Elim einfo params scrut =>
      Elim (substElimInfo n s einfo) (substList n s params) (substH n s scrut)
  end
with substList (n : nat) (s : Subst) (l : TermList) :=
  match l with
    | TL_nil => TL_nil
    | TL_cons l' M => TL_cons (substList n s l') (substH n s M)
  end
with substOpt (n : nat) (s : Subst) (M_opt : TermOpt) :=
  match M_opt with
    | SomeTerm M => SomeTerm (substH n s M)
    | NoTerm => NoTerm
  end
with substIndInfo (n : nat) (s : Subst) (info : IndInfo) :=
  match info with
    | MkIndInfo sort ctorTypes =>
      MkIndInfo (substH n s sort) (fun i => substOpt n s (ctorTypes i))
  end
with substElimInfo (n : nat) (s : Subst) (einfo : ElimInfo) :=
  match einfo with
    | MkElimInfo info i P patts =>
      MkElimInfo (substIndInfo n s info) i (substH n s P)
      (fun i => substOpt n s (patts i))
  end
.

Definition substMSeq (n : nat) (s : Subst) (seq : TermMSeq) :=
  (fun i => substOpt n s (seq i)).

Definition subst (s : Subst) (M : Term) := substH 0 s M.
Definition substOne (N M : Term) := substH 0 (TL_cons TL_nil N) M.


(***
 *** helper functions defined in terms of substitution
 ***)

(* Return the result type of the application of a function of type
   (x1:A1) -> .. -> (xn:An) -> B to a list of arguments N1 .. Nn;
   i.e., substitute each Ni for xi in B. Return NoTerm if the function
   type does not have enough Pi's for the given argument list.
 *)
Fixpoint typeApply (funtp : Term) (args : TermList) : TermOpt :=
  match args with
    | TL_nil => SomeTerm funtp
    | TL_cons args' N =>
      match funtp with
        | Pi A B => match typeApply funtp args' with
                      | SomeTerm Bres => SomeTerm (substOne N Bres)
                      | NoTerm => NoTerm
                    end
        | _ => NoTerm
      end
  end.


(***
 *** definitions for inductive types
 ***)

(* Inductive types are given as a pair (kind, ctorTypes) of the kind
   of the inductive type constructor itself and a sequence of the
   types of the constructors. To be well-formed, kind must be of the
   form (x1:A1) -> ... -> (xn:An) -> s such that each Ai has sort si
   and, if s is (Tp j), then each Ai has type (Tp j). Each type in
   ctorTypes must be (x1:B1) -> ... -> (xm:Bm) -> X M1 .. Mn, where: X
   is deBruijn index 0 outside the binding for x1; each Bi has the
   same type (Tp j) as in the kind, or any sort sj for impredicative
   types; and where each M has the corresponding A type in kind.

   Each Bi must also be strictly positive in X, meaning that, if it
   contains X, it has the form (y1:C1) -> ... -> (yp:Cp) -> X N1 .. Nn
   where none of the C's or N's have X free. Note that, as an
   additional technical requirement to simplify the proofs later on,
   we also require that any yi whose type Ci does contain X (in the
   above form) does not occur in any later C's or in any of the N's.
   This should in fact always hold anyway for strictly positive types,
   since there is nothing in scope that has a type which refers to X,
   the return type of yi, and thus any later term containing y would
   have to mention the type of yi, which would contain X, which is
   disallowed by positivity. We do not prove this, however,
 *)


(**
 ** strict positivity
 **)

(* Captures the fact that a term is X M1 .. Mn for some arguments Mi
   that do not contain X free.
 *)
Inductive isXApp (n : nat) : Term -> Set :=
  | isXAppBase : isXApp n (Var n) 
  | isXAppStep (M N : Term) :
    isXApp n M -> notOccurs n N -> isXApp n (App M N)
. 

(* Defines positivity for recursive argument types, meaning that the
   type has the form (y1:C1) -> ... -> (yp:Cp) -> X N1 .. Nn where
   none of the C's have X free.
 *)
Inductive positiveArg (n : nat) : Term -> Set :=
| PosArg (A B : Term)
  : notOccurs n A -> positiveArg (S n) B -> positiveArg n (Pi A B)
| PosArgEnd (M : Term) : isXApp n M -> positiveArg n M
.


(* Defines constructor types that are strictly positive for deBruijn
   index n.
 *)
Inductive positiveN (n : nat) : Term -> Set :=
| Positive_Rec (A B : Term)
  : positiveArg n A -> positiveN (S n) B -> positiveN n (Pi A B)
| Positive_NonRec (A B : Term)
  : notOccurs n A -> positiveN (S n) B -> positiveN n (Pi A B)
| Positive_End (A : Term) : isXApp n A -> positiveN n A
.

Definition positive := positiveN 0.


(**
 ** building the type of an eliminator
 **)

(* Helper function for elimtpCtor: builds the type of the recursive
   calls. See comments for elimtpCtor below. NOTE: This also gives the
   type of the result of buildRecElimCall.
 *)
Fixpoint buildRecCallType (n : nat) (A P xapp : Term) : TermOpt :=
  match A with
    | Pi C Arest =>
      match buildRecCallType (S n) Arest (lift 0 1 P)
        (App (lift 0 1 xapp) (Var 0))
      with
        | NoTerm => NoTerm
        | SomeTerm res => SomeTerm (Pi C res)
      end
    | _ => match fst (matchApply A) with
             | Var i => match eq_nat_dec i n with
                          | left _ =>
                            SomeTerm (App
                              (apply P (snd (matchApply A)))
                              xapp)
                          | right _ => NoTerm
                        end
             | _ => NoTerm
           end
  end.


(* Build the type of the "recursive step" of a constructor of type ctp
   for an inductive hypothesis predicate P. In more detail, ctp should
   have the form (x1:A1) -> .. -> (xn:An) -> X M1 .. Mm, where X is
   the variable corresponding to deBruijn index 0 outside ctp. The
   recursive step should then have type

   (x1:A1) -> (y1:B1)? -> .. (xn:An) -> (yn:Bn)? ->
   P M1 .. Mm (c x1 .. xn)

   where c is the constructor whose recursive step type we are
   building and each Bi is, intuitively, the type of the result of a
   recursive call on xi. To define Bi, we test to see if the type Ai
   has the form (z1:C1) -> .. -> (zn:Cn) -> X N1 .. Nn; if so,
   then Bi is defined as

   (z1:C1) -> .. -> (zn:Cn) -> P N1 .. Nn (xi z1 .. zn)

   Otherwise, the binding (yi:Bi) is omitted.

   To define this recursively, elimtpCtor takes ctp along with: the
   predicate P; the numbers n and m of xi's and yi's, respectively,
   that we have already added outside the current point in the
   computation; and a term capp, which is c applied to all of the xi's
   that have already been seen.

   NOTE: ctp has *not* been lifted into the yi bindings; this is to
   avoid a recursive call on (lift 0 1 ctp') in the first case. Thus,
   any uses of components matched in ctp must be lifted by m.
 *)

Fixpoint elimtpCtor (n m : nat) (ctp P capp : Term) {struct ctp} : Term :=
  match ctp with
    | Pi A ctp' =>
      Pi (lift 0 m A) (
        match buildRecCallType ((S n)+m) (lift 0 (S m) A) (lift 0 1 P) (Var 0)
        with
          | SomeTerm B =>
            Pi B (elimtpCtor (S n) (S m) ctp' (lift 0 2 P)
              (App (lift 0 2 capp) (Var 1)))
          | NoTerm =>
            (elimtpCtor (S n) m ctp' (lift 0 1 P) (App (lift 0 1 capp) (Var 0)))
        end
      )
    | _ => App (apply P (snd (matchApply ctp))) capp
  end.

(**
 ** iota-reduction
 **)

(* The iota-rule is defined like this:

   elim info i P f (M1 .. Mm) (cj N1 .. Nn)
   -->
   (f j) N1 N1'? N2 N2'? ...

   If the type of Nk has the form (x1:A1) .. (xp:Ap) -> a P1 .. Pm,
   then Nk'?  becomes a recursive call to the eliminator, of the form

   \x1 .. xp -> elim info i P f (P1 .. Pm) (Nk x1 .. xp)

   Otherwise, Nk'? is NoTerm, i.e., there is no argument for it.
*)


(* Build \x1 .. xp -> elim info i P f (P1 .. Pm) (Nk x1 .. xp) from
   the type (x1:A1) .. (xp:Ap) -> a P1 .. Pm and the terms Nk and the
   eliminator (elim info i P f)
*)
Fixpoint buildRecElimCall (n : nat) (Ntp N : Term) (einfo : ElimInfo)
  : TermOpt :=
  match Ntp with
    | Pi A B =>
      match buildRecElimCall (S n) B (App (lift 0 1 N) (Var 0))
        (liftElimInfo 0 1 einfo)
      with
        | SomeTerm recResult => SomeTerm (Lam A recResult)
        | NoTerm => NoTerm
      end
    | _ => match fst (matchApply Ntp) with
             | Var i => match eq_nat_dec i n with
                          | left _ =>
                            SomeTerm (Elim einfo (snd (matchApply Ntp)) N)
                          | right _ => NoTerm
                        end
             | _ => NoTerm
           end
  end.


(* Build the term "(f j) N1 N1'? N2 N2'? ...", the result of iota
   reduction, from "elim info i P f (M1 .. Mm) (cj N1 .. Nn)", where M
   = (f j), ctp = the type of cj, cargs = N1 .. Nn, and einfo is the
   ElimInfo containing (info, i, P, f).

   Typing Invariants: M has type Mtp = elimtp P cj ctp, i.e., the type a
   "recursive step" for a constructor of type ctp; and cargs match
   some prefix of the argument types of ctp, i.e., typeApply ctp cargs
   is not NoTerm.

   Typing Result: The resulting term should have the following type:
   elimtpCtor 0 0 (typeApply ctp cargs) P ((\x1 .. xn -> cj x1 .. xn) cargs)
 *)
Fixpoint buildIotaResult (ctp M : Term) (cargs : TermList) (einfo : ElimInfo)
  {struct cargs} : Term :=
  match cargs with
    | TL_nil => M
    | TL_cons cargs' Ni =>
      match typeApply ctp cargs with
        | SomeTerm (Pi A B) =>
          apply1opt (buildIotaResult ctp M cargs' einfo)
          (buildRecElimCall 0 A Ni einfo)
        | _ =>
          (* README: should never happen *)
          (buildIotaResult ctp M cargs' einfo)
      end
  end.

FIXME HERE:


(* README: we assume there is some "ambient" ctx and an argCtx for the
 * non-recursive args in the current constructor; elimF then takes in ctx',
 * some params that are well-typed in (ctx,argCtx,ctx'), and some scrut
 * that is well-typed in (ctx,ctx'), and returns a term well-typed in
 * (ctx,ctx'). *)
Definition elimRecArg (elimF : Ctx -> TermList -> Term -> Term)
  (r : RecTp) (recArg : Term) :=
  match r with
    | MkRecTp ctx indices =>
      makeLam ctx (elimF ctx indices
        (makeAppToVars (lift 0 (ctxLen ctx) recArg) 0 ctx))
  end.

(* README: elimRecArgsH takes each recursive argument recArg supplied
 * to a constructor and returns both recArg and the result of a
 * recursive call (using elimF) on recArg *)
Fixpoint elimRecArgsH (elimF : Ctx -> TermList -> Term -> Term)
  (rs : RecTpList) (recArgs : TermList) : option TermList :=
  match rs, recArgs with
    | RTL_nil, TL_nil => Some TL_nil
    | RTL_cons rs' r, TL_cons recArgs' recArg =>
      match elimRecArgsH elimF rs' recArgs' with
        | None => None
        | Some ret =>
          Some (TL_cons (TL_cons ret recArg) (elimRecArg elimF r recArg))
      end
    | _, _ => None
  end.

Definition elimRecArgs (info : IndInfo) (fs : TermList) (i : nat)
  (args : TermList) (recArgs : TermList) : option TermList :=
  match nthCtorType i info with
    | None => None
    | Some (MkCtorType ctx rs indices) =>
      elimRecArgsH (fun ctx params scrut =>
        Elim (liftIndInfo 0 (ctxLen ctx) info)
        (liftTermList 0 (ctxLen ctx) fs)
        (substTermList (ctxLen ctx) args params)
        scrut)
      rs recArgs
  end.


(*
Definition elimRecArg (info : IndInfo) (fs : TermList) (args : TermList) (r : RecTp) (recArg : Term) :=
  match r with
    | MkRecTp ctx indices =>
      makeLam ctx (
        Elim (liftIndInfo 0 (ctxLen ctx) info)
        (liftTermList 0 (ctxLen ctx) fs)
        (substTermList (ctxLen ctx) args indices)
        (makeAppToVars (lift 0 (ctxLen ctx) recArg) 0 ctx)
      )
  end.

Fixpoint elimRecArgsH (info : IndInfo) (fs : TermList) (args : TermList)
  (rs : RecTpList) (recArgs : TermList) : option TermList :=
  match rs, recArgs with
    | RTL_nil, TL_nil => Some TL_nil
    | RTL_cons rs' r, TL_cons recArgs' recArg =>
      match elimRecArgsH info fs args rs' recArgs' with
        | None => None
        | Some ret => Some (TL_cons ret (elimRecArg info fs args r recArg))
      end
    | _, _ => None
  end.

Definition elimRecArgs (info : IndInfo) (fs : TermList) (i : nat)
  (args : TermList) (recArgs : TermList) : option TermList :=
  match nthCtorType i info with
    | None => None
    | Some (MkCtorType ctx rs indices) =>
      elimRecArgsH info fs args rs recArgs
  end.
*)

Inductive rrto : Term -> Term -> Set :=
| RR_Beta : forall A M N, rrto (App (Lam A M) N) (substOne N M)
| RR_iota : forall info info' fs f params i args recArgs elimArgs,
  nth_or_fail_TL i fs = inleft _ f ->
  elimRecArgs info fs i args recArgs = Some elimArgs ->
  rrto (Elim info fs params (CtorApp info' i args recArgs))
  (makeApp (makeApp f args) elimArgs)
| RR_Pi1 : forall A A' B, rrto A A' -> rrto (Pi A B) (Pi A' B)
| RR_Pi2 : forall A B B', rrto B B' -> rrto (Pi A B) (Pi A B')
| RR_App1 : forall f f' a , rrto f f' -> rrto (App f a) (App f' a)
| RR_App2 : forall f a a', rrto a a' -> rrto (App f a) (App f a')
| RR_Lam1 : forall A A' M, rrto A A' -> rrto (Lam A M) (Lam A' M)
| RR_Lam2 : forall A M M', rrto M M' -> rrto (Lam A M) (Lam A M')
| RR_Elim1 : forall info info' fs params scrut,
  rrtoIndInfo info info' ->
    rrto (Elim info fs params scrut) (Elim info' fs params scrut)
| RR_Elim2 : forall info fs fs' params scrut,
  rrtoTermList fs fs' ->
    rrto (Elim info fs params scrut) (Elim info fs' params scrut)
| RR_Elim3 : forall info fs params params' scrut,
  rrtoTermList params params' ->
    rrto (Elim info fs params scrut) (Elim info fs params' scrut)
| RR_Elim4 : forall info fs params scrut scrut',
  rrto scrut scrut' ->
    rrto (Elim info fs params scrut) (Elim info fs params scrut')
with rrtoTermList : TermList -> TermList -> Set :=
| RR_TL_cons1 : forall M l l',
  rrtoTermList l l' -> rrtoTermList (TL_cons l M) (TL_cons l' M)
| RR_TL_cons2 : forall M M' l,
  rrto M M' -> rrtoTermList (TL_cons l M) (TL_cons l M')
with rrtoCtx : Ctx -> Ctx -> Set :=
| RR_Ctx_cons1 : forall ctx ctx' M,
  rrtoCtx ctx ctx' -> rrtoCtx (Ctx_cons ctx M) (Ctx_cons ctx' M)
| RR_Ctx_cons2 : forall ctx M M',
  rrto M M' -> rrtoCtx (Ctx_cons ctx M) (Ctx_cons ctx M')
with rrtoIndInfo : IndInfo -> IndInfo -> Set :=
| RR_MkIndInfo1 : forall ctx ctx' i ctps,
  rrtoCtx ctx ctx' ->
  rrtoIndInfo (MkIndInfo ctx i ctps) (MkIndInfo ctx' i ctps)
| RR_MkIndInfo2 : forall ctx i ctps ctps',
  rrtoCtorTypeList ctps ctps' ->
  rrtoIndInfo (MkIndInfo ctx i ctps) (MkIndInfo ctx i ctps')
with rrtoCtorTypeList : CtorTypeList -> CtorTypeList -> Set :=
| RR_CTL_cons1 : forall ctp l l',
  rrtoCtorTypeList l l' -> rrtoCtorTypeList (CTL_cons l ctp) (CTL_cons l' ctp)
| RR_CTL_cons2 : forall ctp ctp' l,
  rrtoCtorType ctp ctp' -> rrtoCtorTypeList (CTL_cons l ctp) (CTL_cons l ctp')
with rrtoCtorType : CtorType -> CtorType -> Set :=
| RR_MkCtorType1 : forall ctx ctx' rs indices,
  rrtoCtx ctx ctx' ->
  rrtoCtorType (MkCtorType ctx rs indices) (MkCtorType ctx' rs indices)
| RR_MkCtorType2 : forall ctx rs rs' indices,
  rrtoRecTpList rs rs' ->
  rrtoCtorType (MkCtorType ctx rs indices) (MkCtorType ctx rs' indices)
| RR_MkCtorType3 : forall ctx rs indices indices',
  rrtoTermList indices indices' ->
  rrtoCtorType (MkCtorType ctx rs indices) (MkCtorType ctx rs indices')
with rrtoRecTpList : RecTpList -> RecTpList -> Set :=
| RR_RTL_cons1 : forall r l l',
  rrtoRecTpList l l' -> rrtoRecTpList (RTL_cons l r) (RTL_cons l' r)
| RR_RTL_cons2 : forall r r' l,
  rrtoRecTp r r' -> rrtoRecTpList (RTL_cons l r) (RTL_cons l r')
with rrtoRecTp : RecTp -> RecTp -> Set :=
| RR_MkRecTp1 : forall ctx ctx' indices,
  rrtoCtx ctx ctx' ->
  rrtoRecTp (MkRecTp ctx indices) (MkRecTp ctx' indices)
| RR_MkRecTp2 : forall ctx indices indices',
  rrtoTermList indices indices' ->
  rrtoRecTp (MkRecTp ctx indices) (MkRecTp ctx indices')
.



Inductive conv : Term -> Term -> Set :=
| conv_refl : forall M , conv M M
| conv_stepR : forall M1 M2 M3 , rrto M1 M2 -> conv M2 M3 ->
  conv M1 M3
| conv_stepL : forall M1 M2 M3 , rrto M2 M1 -> conv M2 M3 ->
  conv M1 M3
.


(*** sub-typing ***)

Inductive subtype : Term -> Term -> Set :=
| SubTp_Refl : forall T , subtype T T
| SubTp_Sort : forall i j , i <= j -> subtype (Sort i) (Sort j)
| SubTp_Pi : forall A B B' , subtype B B' -> subtype (Pi A B) (Pi A B')
.


(*** typing ***)

(* translates a RecTp into the type of the eliminator for that RecTp
 *
 * README: we assume an "ambient" ctx, an argCtx that quantifies over
 * the non-recursive args for the current constructor, and an indCtx
 * that quantifies over the index args to the current inductive type,
 * where the latter two must be well-formed relative to ctx; we then
 * assume that r is well-typed w.r.t. (ctx,argCtx) and that B is
 * well-typed w.r.t. (ctx,argCtx,indCtx, --some IndType-- ), and
 * return a term that is well-typed in (ctx,argCtx, 0 : r)
 *)
Definition recTp2ElimType (r : RecTp) B :=
  match r with
    | MkRecTp ctx indices =>
      makePi (liftCtx 0 1 ctx) (substH ((ctxLen ctx) + 1)
        (TL_cons (liftTermList (ctxLen ctx) 1 indices)
          (makeAppToVars (Var (ctxLen ctx)) 0 ctx))
        (lift 0 ((ctxLen ctx) + 1) B))
  end.

(* README: we make the same context assumptions as recTp2ElimType and,
 * in addition, that info is well-typed in the "ambient" ctx. *)
Fixpoint recTps2ElimCtx (info : IndInfo) (argCtx : Ctx) (rs : RecTpList) B :=
  match rs with
    | RTL_nil => Ctx_nil
    | RTL_cons rs' r =>
      Ctx_cons (Ctx_cons (recTps2ElimCtx info argCtx rs' B)
        (lift 0 (ctxLen (recTps2ElimCtx info argCtx rs' B))
          (recTp2Type info argCtx r)))
      (lift 1 (ctxLen (recTps2ElimCtx info argCtx rs' B)) (recTp2ElimType r B))
  end.

(* README: same context assumptions as recTp2sElimCtx, but ctp is
 * well-typed w.r.t. the "ambient" ctx and B is well-typed w.r.t.
 * (ctx,indCtx, --some IndType--); we return a term that is well-typed
 * w.r.t. the ambient ctx *)
Definition ctorElimType (info : IndInfo) (indCtx : Ctx) (i : nat) (ctp : CtorType) B :=
  match ctp with
    | MkCtorType argCtx rs indices =>
      let elimCtx := (recTps2ElimCtx info argCtx rs
        (lift (ctxLen indCtx + 1) (ctxLen argCtx) B)) in
      makePi argCtx (
        makePi elimCtx
        (subst
          (TL_cons (liftTermList 0 (ctxLen elimCtx) indices)
            (CtorApp (liftIndInfo 0 (ctxLen argCtx + ctxLen elimCtx) info)
              i
              (makeVarList (ctxLen elimCtx) argCtx)
              (makeVarListStep2 0 elimCtx)
            ))
          (lift (ctxLen indCtx + 1) (ctxLen argCtx + ctxLen elimCtx) B))
      )
  end.

Fixpoint elimFsTypesH (info : IndInfo) (indCtx : Ctx) (i : nat) (ctps : CtorTypeList) B :=
  match ctps with
    | CTL_nil => TL_nil
    | CTL_cons ctps' ctp =>
      TL_cons (elimFsTypesH info indCtx (S i) ctps' B)
      (ctorElimType info indCtx i ctp B)
  end.

Definition elimFsTypes (info : IndInfo) B :=
  match info with
    | MkIndInfo indCtx _ ctps => elimFsTypesH info indCtx 0 ctps B
  end.


Inductive HasTp (ctx : Ctx) : Term -> Term -> Set :=
| HT_convR : forall M T T' , HasTp ctx M T -> rrto T T' -> HasTp ctx M T'
| HT_convL : forall M T T' , HasTp ctx M T -> rrto T' T -> HasTp ctx M T'
| HT_sub : forall M T T' , HasTp ctx M T -> subtype T T' -> HasTp ctx M T'
(* | HT_Prp : forall i , HasTp ctx Prp (Sort i) *)
| HT_Sort : forall i, HasTp ctx (Sort i) (Sort (S i))
| HT_Pi_P : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (Ctx_cons ctx A) B (Sort i) ->
  HasTp ctx (Pi A B) (Sort i)
| HT_Pi_I : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (Ctx_cons ctx A) B (Sort 0) ->
  HasTp ctx (Pi A B) (Sort 0)
| HT_IndType : forall info indices indCtx i ,
  WfIndInfo ctx info indCtx i ->
  HasTpTermList ctx indices indCtx ->
  HasTp ctx (IndType info indices) (Sort i)
| HT_Var : forall i T, isNth_Ctx T i ctx ->
  HasTp ctx (Var i) T
| HT_App : forall A B M N,
  HasTp ctx M (Pi A B) -> HasTp ctx N A ->
  HasTp ctx (App M N) (substOne N B)
| HT_Lam : forall i A M B,
  HasTp ctx A (Sort i) ->
  HasTp (Ctx_cons ctx A) M B ->
  HasTp ctx (Lam A M) (Pi A B)
| HT_CtorApp : forall info indCtx indI argCtx rs indices i args recArgs,
  WfIndInfo ctx info indCtx indI ->
  nthCtorType i info = Some (MkCtorType argCtx rs indices) ->
  HasTpTermList ctx args argCtx ->
  HasTpTermList_TL ctx recArgs (recTps2Types info argCtx rs) ->
  HasTp ctx (CtorApp info i args recArgs)
  (IndType info (substTermList 0 args indices))
| HT_Elim_P : forall info indCtx indI fs params scrut B Bi,
  WfIndInfo ctx info indCtx (S indI) ->
  (HasTp
    (Ctx_cons (Ctx_app ctx indCtx)
      (IndType (liftIndInfo 0 (ctxLen indCtx) info) (makeVarList 0 indCtx)))
    B (Sort Bi)) ->
  HasTpTermList_TL ctx fs (elimFsTypes info B) ->
  HasTpTermList ctx params indCtx ->
  HasTp ctx scrut (IndType info params) ->
  HasTp ctx (Elim info fs params scrut) (subst (TL_cons params scrut) B)
| HT_Elim_I : forall info indCtx fs params scrut B Bi,
  WfIndInfo ctx info indCtx 0 ->
  (HasTp
    (Ctx_cons (Ctx_app ctx indCtx)
      (IndType (liftIndInfo 0 (ctxLen indCtx) info) (makeVarList 0 indCtx)))
    B (Sort Bi)) ->
  ((Bi = 0) + (numCtors info <= 1)) ->
  HasTpTermList_TL ctx fs (elimFsTypes info B) ->
  HasTpTermList ctx params indCtx ->
  HasTp ctx scrut (IndType info params) ->
  HasTp ctx (Elim info fs params scrut) (subst (TL_cons params scrut) B)
(*
| HT_Elim_I0 : forall indCtx params scrut B,
  WfCtx ctx indCtx 0 ->
  HasTpTermList ctx params indCtx ->
  HasTp ctx scrut (IndType (MkIndInfo indCtx 0 CTL_nil) params) ->
  HasTp ctx (Elim (MkIndInfo indCtx 0 CTL_nil) TL_nil params scrut) (subst (TL_cons params scrut) B)
*)

(* FIXME: impredicative elims *)

with HasTpTermList (ctx : Ctx) : TermList -> Ctx -> Set :=
| HT_TL_nil : HasTpTermList ctx TL_nil Ctx_nil
| HT_TL_cons : forall l lCtx M T,
  HasTpTermList ctx l lCtx -> HasTp ctx M (subst l T) ->
  HasTpTermList ctx (TL_cons l M) (Ctx_cons lCtx T)

(* same as above, but with no substitution, since the types are not a
 * Ctx, and so are not dependent *)
with HasTpTermList_TL (ctx : Ctx) : TermList -> TermList -> Set :=
| HT_TL_nil_TL : HasTpTermList_TL ctx TL_nil TL_nil
| HT_TL_cons_TL : forall l Ts M T,
  HasTpTermList_TL ctx l Ts -> HasTp ctx M T ->
  HasTpTermList_TL ctx (TL_cons l M) (TL_cons Ts T)

(* states that a Ctx is well-formed with max sort i *)
with WfCtx (ctx : Ctx) : Ctx -> nat -> Set :=
| WF_Ctx_nil : forall i, WfCtx ctx Ctx_nil i
| WF_Ctx_cons : forall ctx' A i,
  WfCtx ctx ctx' i -> HasTp ctx A (Sort i) -> WfCtx ctx (Ctx_cons ctx' A) i

with WfIndInfo (ctx : Ctx) : IndInfo -> Ctx -> nat -> Set :=
| WF_MkIndInfo : forall indCtx i ctps,
  WfCtx ctx indCtx i ->
  WfCtorTypeList ctx indCtx ctps i ->
  WfIndInfo ctx (MkIndInfo indCtx i ctps) indCtx i

with WfCtorTypeList (ctx : Ctx) : Ctx -> CtorTypeList -> nat -> Set :=
| WF_CTL_nil : forall indCtx i, WfCtorTypeList ctx indCtx CTL_nil i
| WF_CTL_cons : forall indCtx i ctps ctp,
  WfCtorTypeList ctx indCtx ctps i ->
  WfCtorType ctx indCtx ctp i ->
  WfCtorTypeList ctx indCtx (CTL_cons ctps ctp) i

with WfCtorType (ctx : Ctx) : Ctx -> CtorType -> nat -> Set :=
| WF_MkCtorType : forall indCtx argCtx i r indices,
  WfCtx ctx argCtx i ->
  WfRecTpList ctx indCtx argCtx r i ->
  HasTpTermList (Ctx_app ctx argCtx) indices indCtx ->
  WfCtorType ctx indCtx (MkCtorType argCtx r indices) i

with WfRecTpList (ctx : Ctx) : Ctx -> Ctx -> RecTpList -> nat -> Set :=
| WF_RTL_nil : forall indCtx argCtx i, WfRecTpList ctx indCtx argCtx RTL_nil i
| WF_RTL_cons : forall indCtx argCtx i rs r,
  WfRecTpList ctx indCtx argCtx rs i ->
  WfRecTp ctx indCtx argCtx r i ->
  WfRecTpList ctx indCtx argCtx (RTL_cons rs r) i

with WfRecTp (ctx : Ctx) : Ctx -> Ctx -> RecTp -> nat -> Set :=
| WF_MkRecTp : forall indCtx argCtx i recCtx recIndices,
  WfCtx (Ctx_app ctx argCtx) recCtx i ->
  HasTpTermList (Ctx_app ctx argCtx) recIndices indCtx ->
  WfRecTp ctx indCtx argCtx (MkRecTp recCtx recIndices) i
.
