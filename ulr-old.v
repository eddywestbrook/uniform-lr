Require Import List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Arith_base.

(*** terms and helper defs ***)

Definition level := nat.

Definition IndInfoH (T : Set) :=
  (level * (list ((list T) * (list (list T * list T)))))%type.

Inductive Term : Set :=
| Sort : level -> Term
| Pi : Term -> Term -> Term
| IndType : IndInfo -> TermList -> Term
| Var : nat -> Term
| App : Term -> Term -> Term
| Lam : Term -> Term -> Term
| CtorApp : IndInfo -> nat -> TermList -> TermList -> Term
| Elim : IndInfo -> TermList -> TermList -> Term -> Term
with TermList :=
| TL_nil : TermList
| TL_cons : TermList -> Term -> TermList
with Ctx :=
| Ctx_nil : Ctx
| Ctx_cons : Ctx -> Term -> Ctx
with IndInfo :=
| MkIndInfo : Ctx -> level -> CtorTypeList -> IndInfo
with CtorTypeList :=
| CTL_nil : CtorTypeList
| CTL_cons : CtorTypeList -> CtorType -> CtorTypeList
with CtorType :=
| MkCtorType : Ctx -> RecTpList -> TermList -> CtorType
with RecTpList :=
| RTL_nil : RecTpList
| RTL_cons : RecTpList -> RecTp -> RecTpList
with RecTp :=
| MkRecTp : Ctx -> TermList -> RecTp
.

(* Definition Ctx : Set := list Term. *)
(* Definition Ctx : Set := TermList. *)


(*** operations on my fake lists (stupid Coq) ***)

Fixpoint ctxLen (ctx : Ctx) :=
  match ctx with
    | Ctx_nil => 0
    | Ctx_cons ctx' _ => S (ctxLen ctx')
  end.

Fixpoint Ctx_app (ctx1 ctx2 : Ctx) :=
  match ctx2 with
    | Ctx_nil => ctx1
    | Ctx_cons ctx2' M => Ctx_cons (Ctx_app ctx1 ctx2') M
  end.

Fixpoint TL_Len (l : TermList) :=
  match l with
    | TL_nil => 0
    | TL_cons l' _ => S (TL_Len l')
  end.

Fixpoint TL_app (l1 l2 : TermList) :=
  match l2 with
    | TL_nil => l1
    | TL_cons l2' M => TL_cons (TL_app l1 l2') M
  end.

Fixpoint nth_or_fail_TL (n : nat) (l : TermList) : Term + { TL_Len l <= n } :=
  match n as n', l as l' return Term + { TL_Len l' <= n' } with
    | n, TL_nil => inright _ (le_O_n n)
    | 0, TL_cons _ M => inleft _ M
    | (S n'), (TL_cons l' _) =>
      match nth_or_fail_TL n' l' with
        | inleft M => inleft _ M
        | inright pf => inright _ (le_n_S _ _ pf)
      end
  end.

Fixpoint CTL_Len (l : CtorTypeList) :=
  match l with
    | CTL_nil => 0
    | CTL_cons l' _ => S (CTL_Len l')
  end.

Fixpoint nth_or_fail_CTL (n : nat) (l : CtorTypeList) : CtorType + { CTL_Len l <= n } :=
  match n as n', l as l' return CtorType + { CTL_Len l' <= n' } with
    | n, CTL_nil => inright _ (le_O_n n)
    | 0, CTL_cons _ ctp => inleft _ ctp
    | (S n'), (CTL_cons l' _) =>
      match nth_or_fail_CTL n' l' with
        | inleft ctp => inleft _ ctp
        | inright pf => inright _ (le_n_S _ _ pf)
      end
  end.


Inductive isNth_CTL (T : CtorType) : nat -> CtorTypeList -> Set :=
| isNth_CTL_base (l : CtorTypeList) : isNth_CTL T 0 (CTL_cons l T)
| isNth_CTL_cons (n : nat) (T' : CtorType) (l : CtorTypeList)
  : isNth_CTL T n l -> isNth_CTL T (S n) (CTL_cons l T').

Inductive isNth_TL (T : Term) : nat -> TermList -> Set :=
| isNth_TL_base (l : TermList) : isNth_TL T 0 (TL_cons l T)
| isNth_TL_cons (n : nat) (T' : Term) (l : TermList)
  : isNth_TL T n l -> isNth_TL T (S n) (TL_cons l T').

Inductive isNth_RTL (T : RecTp) : nat -> RecTpList -> Set :=
| isNth_RTL_base (l : RecTpList) : isNth_RTL T 0 (RTL_cons l T)
| isNth_RTL_cons (n : nat) (T' : RecTp) (l : RecTpList)
  : isNth_RTL T n l -> isNth_RTL T (S n) (RTL_cons l T').

Inductive isNth_Ctx (T : Term) : nat -> Ctx -> Set :=
| isNth_Ctx_base (ctx : Ctx) : isNth_Ctx T 0 (Ctx_cons ctx T)
| isNth_Ctx_cons (n : nat) (ctx : Ctx) (T' : Term)
  : isNth_Ctx T n ctx -> isNth_Ctx T (S n) (Ctx_cons ctx T').


(*** simple term maipulation ***)

Fixpoint makeLam (ctx : Ctx) (body : Term) {struct ctx} : Term :=
  match ctx with
    | Ctx_nil => body
    | Ctx_cons ctx' tp => makeLam ctx' (Lam tp body)
  end.
Fixpoint makePi (ctx : Ctx) (body : Term) {struct ctx} : Term :=
  match ctx with
    | Ctx_nil => body
    | Ctx_cons ctx' tp => makePi ctx' (Pi tp body)
  end.
Fixpoint makeApp (f : Term) (args : TermList) : Term :=
  match args with
    | TL_nil => f
    | TL_cons args' arg => App (makeApp f args') arg
  end.
Fixpoint makeVarList (n : nat) (ctx : Ctx) : TermList :=
  match ctx with
    | Ctx_nil => TL_nil
    | Ctx_cons ctx' tp => TL_cons (makeVarList (S n) ctx') (Var n)
  end.
Definition makeAppToVars (f : Term) (n : nat) (ctx : Ctx) : Term :=
  makeApp f (makeVarList n ctx).
(*
Fixpoint makeAppToVars (f : Term) (n : nat) (ctx : Ctx) : Term :=
  match ctx with
    | Ctx_nil => f
    | Ctx_cons ctx' tp => App (makeAppToVars f (S n) ctx') (Var n)
  end.
*)
Fixpoint makeVarListStep2 (n : nat) (ctx : Ctx) : TermList :=
  match ctx with
    | Ctx_cons (Ctx_cons ctx' tp1) tp2 =>
      TL_cons (makeVarListStep2 (S (S n)) ctx') (Var n)
    | _ => TL_nil
  end.

(* Definition dummyCtorType : CtorType := MkCtorType Ctx_nil RTL_nil TL_nil. *)

Definition ctorRecTps (ctp : CtorType) : RecTpList :=
  match ctp with
    MkCtorType ctx recTps indices => recTps
  end.

Definition numCtors (info : IndInfo) :=
  match info with
    MkIndInfo ctx l ctps => CTL_Len ctps
  end.


Definition nthCtorType (n : nat) (info : IndInfo) : option CtorType :=
  match info with
    MkIndInfo ctx l ctps =>
    match nth_or_fail_CTL n ctps with
      | inleft ctp => Some ctp
      | inright _ => None
(* | inright _ => dummyCtorType *)
    end
  end.


(*** proofs of the maximum sort + 1 in a term ***)
(* README: this (not entirely finished) is not closed under conv!
Inductive MaxSort (i : nat) : Term -> Set :=
| MS_Sort j : j < i -> MaxSort i (Sort j)
| MS_Pi A B i : MaxSort i A -> MaxSort i B -> MaxSort i (Pi A B) 
| MS_IndType info args i :
  MaxSortIndInfo i info -> MaxSortTermList i args ->
  MaxSort i (IndType info args)
| MS_Var j i : MaxSort i (Var j)
| MS_App M N i : MaxSort i M -> MaxSort i N -> MaxSort i (App M N)
| MS_Lam A M i : MaxSort i A -> MaxSort i M -> MaxSort i (Lam A M)
| MS_CtorApp info j args recArgs i :
  MaxSortIndInfo i info -> MaxSortTermList i args ->
  MaxSortRecTpList i recArgs -> MaxSort i (CtorApp info j args recArgs)
| MS_Elim info fs params scrut i :
  MaxSortIndInfo i info -> MaxSortTermList i fs ->
  MaxSortTermList i params -> MaxSort i scrut ->
  MaxSort i (info fs params scrut)
with MaxSortTermList (i : nat) : TermList -> Set :=
| MS_TL_nil : MaxSortTermList i TL_nil
| MS_TL_cons l M : MaxSortTermList i l -> MaxSort i M ->
  MaxSortTermList i (TL_cons l M)
with MaxSortCtx (i : nat) : MaxSortCtx -> Set :=
| MS_Ctx_nil : MaxSortCtx i Ctx_nil
| MS_Ctx_cons l M : MaxSortCtx i l -> MaxSort i M ->
  MaxSortCtx i (Ctx_cons l M)
with MaxSortIndInfo (i : nat) : MaxSortIndInfo -> Set :=
| MS_MkIndInfo ctx j ctps :
  MaxSortCtx i ctx -> j <= i -> MaxSort
with MaxSortCtorTypeList (i : nat) : MaxSortCtorTypeList -> Set :=
| MS_CTL_nil : MaxSortCtorTypeList i CTL_nil
| MS_CTL_cons l M : MaxSortCtorTypeList i l -> MaxSort i M ->
  MaxSortCtorTypeList i (CTL_cons l M)
with MaxSortCtorType (i : nat) : MaxSortCtorType -> Set :=
| MS_MkCtorType : Ctx -> RecTpList -> TermList -> CtorType
with MaxSortRecTpList (i : nat) : MaxSortRecTpList -> Set :=
| MS_RTL_nil : MaxSortRecTpList i RTL_nil
| MS_RTL_cons l M : MaxSortRecTpList i l -> MaxSort i M ->
  MaxSortRecTpList i (RTL_cons l M)
with MaxSortRecTp (i : nat) : MaxSortRecTp -> Set :=
| MS_MkRecTp : Ctx -> TermList -> RecTp
.
*)

(*** substitution and lifting ***)

(* README: k is the amount we are incrementing the variables, and n is the
 * number of variable bindings under which we have traversed so far *)
Fixpoint lift (n k : nat) (M : Term) {struct M} : Term :=
  match M with
    | Sort i => Sort i
    | Pi A B => Pi (lift n k A) (lift (S n) k B)
    | IndType info indices =>
      IndType (liftIndInfo n k info) (liftTermList n k indices)
    | Var i =>
      match le_lt_dec n i with
        | left _ => Var (i + k) (* case: i >= n *)
        | right _ => Var i (* case: i < n *)
      end
    | App M1 M2 => App (lift n k M1) (lift n k M2)
    | Lam A M1 => Lam (lift n k A) (lift (S n) k M1)
    | CtorApp info i args recArgs =>
      CtorApp (liftIndInfo n k info) i (liftTermList n k args) (liftTermList n k recArgs)
    | Elim info fs params scrut =>
      Elim (liftIndInfo n k info) (liftTermList n k params)
      (liftTermList n k fs) (lift n k scrut)
  end
with liftTermList (n k : nat) (l : TermList) :=
  match l with
    | TL_nil => TL_nil
    | TL_cons l' M => TL_cons (liftTermList n k l') (lift n k M)
  end
with liftCtx (n k : nat) (ctx : Ctx) :=
  match ctx with
    | Ctx_nil => Ctx_nil
    | Ctx_cons ctx' M => Ctx_cons (liftCtx n k ctx') (lift (n + (ctxLen ctx')) k M)
  end
with liftIndInfo (n k : nat) (info : IndInfo) :=
  match info with
    | MkIndInfo ctx i ctorTypes => MkIndInfo (liftCtx n k ctx) i (liftCtorTypeList n k ctorTypes)
  end
with liftCtorTypeList (n k : nat) (l : CtorTypeList) :=
  match l with
    | CTL_nil => CTL_nil
    | CTL_cons l' ctp =>
      CTL_cons (liftCtorTypeList n k l') (liftCtorType n k ctp)
  end
with liftCtorType (n k : nat) (ctp : CtorType) :=
  match ctp with
    | MkCtorType ctx recCtx indices =>
      (MkCtorType (liftCtx n k ctx)
        (liftRecTpList (n + (ctxLen ctx)) k recCtx)
        (liftTermList (n + (ctxLen ctx)) k indices))
  end
with liftRecTpList (n k : nat) (l : RecTpList) :=
  match l with
    | RTL_nil => RTL_nil
    | RTL_cons l' r => RTL_cons (liftRecTpList n k l') (liftRecTp n k r)
  end
with liftRecTp (n k : nat) (r : RecTp) :=
  match r with
    | MkRecTp ctx indices =>
      MkRecTp (liftCtx n k ctx) (liftTermList (n + (ctxLen ctx)) k indices)
  end
  .


Fixpoint substH (n : nat) (s : TermList) (M : Term) {struct M} : Term :=
  match M with
    | Sort i => Sort i
    | Pi A B => Pi (substH n s A) (substH (S n) s B)
    | IndType info indices =>
      IndType (substIndInfo n s info) (substTermList n s indices)
    | Var i =>
      match le_lt_dec n i with
        | right _ => Var i (* case: i < n *)
        | left _ => (* case: i >= n *)
          match nth_or_fail_TL (i - n) s with
            | inleft N => lift 0 n N
            | _ => Var (i + n)
          end
      end
    | App M1 M2 => App (substH n s M1) (substH n s M2)
    | Lam A M1 => Lam (substH n s A) (substH (S n) s M1)
    | CtorApp info i args recArgs =>
      CtorApp (substIndInfo n s info) i (substTermList n s args) (substTermList n s recArgs)
    | Elim info fs params scrut =>
      Elim (substIndInfo n s info) (substTermList n s params)
      (substTermList n s fs) (substH n s scrut)
  end
with substTermList (n : nat) (s : TermList) (l : TermList) :=
  match l with
    | TL_nil => TL_nil
    | TL_cons l' M => TL_cons (substTermList n s l') (substH n s M)
  end
with substCtx (n : nat) (s : TermList) (ctx : Ctx) :=
  match ctx with
    | Ctx_nil => Ctx_nil
    | Ctx_cons ctx' M =>
      Ctx_cons (substCtx n s ctx') (substH (plus n (ctxLen ctx')) s M)
  end
with substIndInfo (n : nat) (s : TermList) (info : IndInfo) :=
  match info with
    | MkIndInfo ctx l ctorTypes =>
      MkIndInfo (substCtx n s ctx) l (substCtorTypeList n s ctorTypes)
  end
with substCtorTypeList (n : nat) (s : TermList) (l : CtorTypeList) :=
  match l with
    | CTL_nil => CTL_nil
    | CTL_cons l' ctp =>
      CTL_cons (substCtorTypeList n s l') (substCtorType n s ctp)
  end
with substCtorType (n : nat) (s : TermList) (ctp : CtorType) :=
  match ctp with
    | MkCtorType ctx recCtx indices =>
      (MkCtorType (substCtx n s ctx)
        (substRecTpList (plus n (ctxLen ctx)) s recCtx)
        (substTermList (plus n (ctxLen ctx)) s indices))
  end
with substRecTpList (n : nat) (s : TermList) (l : RecTpList) :=
  match l with
    | RTL_nil => RTL_nil
    | RTL_cons l' r => RTL_cons (substRecTpList n s l') (substRecTp n s r)
  end
with substRecTp (n : nat) (s : TermList) (r : RecTp) :=
  match r with
    | MkRecTp ctx indices =>
      MkRecTp (substCtx n s ctx) (substTermList (plus n (ctxLen ctx)) s indices)
  end
  .

Definition subst (s : TermList) (M : Term) := substH 0 s M.
Definition substOne (N M : Term) := substH 0 (TL_cons TL_nil N) M.


(*** auxiliary defs dependent on substitution ***)

Fixpoint termList2Ctx (l : TermList) : Ctx :=
  match l with
    | TL_nil => Ctx_nil
    | TL_cons l' A => Ctx_cons (termList2Ctx l') (lift 0 (TL_Len l') A)
  end.

(*** operations on inductive types: most of these require lifting ***)

Definition indLevel (info : IndInfo) :=
  match info with
    | MkIndInfo _ l _ => l
  end.

(* README: we assume info is well-typed in the "ambient" ctx, that
 * argCtx is well-formed in ctx, and that r is well-typed in (ctx,argCtx);
 * the returned term is well-typed in (ctx,argCtx) *)
Definition recTp2Type (info : IndInfo) (argCtx : Ctx) (r : RecTp) : Term :=
  match r with
    | MkRecTp ctx indices =>
      makePi ctx (IndType (liftIndInfo 0 (ctxLen ctx + ctxLen argCtx) info) indices)
  end.
Fixpoint recTps2Types (info : IndInfo) (argCtx : Ctx) (rs : RecTpList) : TermList :=
  match rs with
    | RTL_nil => TL_nil
    | RTL_cons rs' r =>
      TL_cons (recTps2Types info argCtx rs') (recTp2Type info argCtx r)
  end.

(* NOTE: the below requires lifting each result of (recTp2Type info r)
Fixpoint makeRecTpPi (info : IndInfo) (l : RecTpList) (body : Term) : Term :=
  match l with
    | RTL_nil => body
    | RTL_cons l' r => makeRecTpPi info l' (Pi (recTp2Type info r) body)
  end.
Definition ctorPiType (info : IndInfo) (ctp : CtorType) : Term :=
  match ctp with
    | MkCtorType ctx recCtx indices =>
      makePi ctx (makeRecTpPi info recCtx (IndType info indices))
  end.
*)

(*
Fixpoint recTp2Type (info : IndInfo) (r : RecTp) : Term :=
  match r with
    | MkRecTp arg recArgs => IndType info args
    | RT_cons varTp r' => Pi varTp (recTp2Type info r')
  end.
*)


(*
Definition isArgType (ctor i : nat) (info : IndInfo) (T : Term) : Set :=
  match info with
    | MkIndInfo _ ctorTypes =>
      { al : TermList & { rtl : RecTpList & isNth_CTL (MkCtorType al rtl) ctor ctorTypes & isNth_TL T i al } }
  end.

Definition isRecArgType (ctor i : nat) (info : IndInfo) (T : Term) : Set :=
  

  match info with
    | MkIndInfo _ ctorTypes =>
      { al : TermList & { rtl : RecTpList & isNth_CTL (MkCtorType al rtl) ctor ctorTypes & isNth_TL T i al } }
  end.
*)





(*** convertability ***)

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
