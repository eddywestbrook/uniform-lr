Require Import List.
(* Require Import Coq.Arith.Compare_dec. *)
Require Import Coq.Arith.Arith_base.
Require Import Coq.Bool.Bool.

(*** things that should be in the StdLib... ***)
Inductive isNth (A : Type) (a : A) : nat -> list A -> Type :=
| isNth_base (l : list A) : isNth A a 0 (a :: l)
| isNth_cons (n : nat) (x : A) (l : list A)
  : isNth A a n l -> isNth A a (S n) (x :: l).


(*** terms and helper defs ***)

(* NOTE: We represent inductive types using strictly positive functors,
 * i.e., as least fixed-points mu X.F(X) where X can only occur inside sums,
 * pairs, or the right-hand sides of Pis in F. Our inductive types are also
 * indexed, meaning that X in F(X) is actually a type-level function, i.e.,
 * has type A -> Type for some given type A. IndType isP A Cin aout a is an
 * inductive type with:
 *
 * - flag isP that determines whether the type is predicative;
 * - index type A : Type (for some given universe);
 * - positive functor Cin of type (A -> Type) |- Type, i.e., the 0th free
 *   variable has type A -> Type (Cin stands for "constructor input");
 * - a function aout of type (X : A -> Type, [X/0]Cin) |- A that determines
 *   the index for any given constructor input; and
 * - index a of type A.
 *
 * The elements of IndType isP A Cin aout a have the form
 * CtorApp isP A Cin aout x  where a:A, x:[(Lam a.IndType... a)/0]Cin,
 * and [(Lam a.IndType... a)/1,x/0]aout = a. Finally, the eliminator
 * IndElim A Cin aout B f a x  eliminates x=CtorApp ... M  by first
 * checking that M is "canonical for Cin", meaning that M has pairs
 * for the pair types, lambdas for the pi types, etc. in the parts
 * of Cin that contain Var 0 free; it then returns f a (elimArg ... M),
 * where elimArg replaces each recursive subterm N of M (each subterm
 * corresponding to an occurrence of Var 0 in Cin) with the pair
 * (N, IndElim ... a' N), where a' (the index type for N) is also generated
 * from Cin.
 *)

Definition level := nat.

Inductive Term : Set :=
| Sort : level -> Term
| ZeroTp : Term
| OneTp : Term
| Pi : Term -> Term -> Term
| PairTp : Term -> Term -> Term
| SumTp : Term -> Term -> Term
| IndType : bool -> Term -> Term -> Term -> Term -> Term
| Var : nat -> Term
| ZeroElim : Term -> Term -> Term
(* ZeroElim A M  eliminates M : ZeroTp into any type A *)
| One : Term
| OneElim : Term -> Term -> Term -> Term
(* OneElim B M N  eliminates N : OneTp  by "casting" M : [One/0]B to [N/0]B;
 * rr rule:  OneElim B M One --> M *)
| Lam : Term -> Term -> Term
| App : Term -> Term -> Term
| Pair : Term -> Term -> Term
| ProjL : Term -> Term
| ProjR : Term -> Term
| SumL : Term -> Term
| SumR : Term -> Term
| SumElim : Term -> Term -> Term -> Term -> Term
(* SumElim B M1 M2 N  eliminates N : SumTp A1 A2 by returning M1 or M2:
 * SumElim B M1 M2 (SumL N) --> M1 N : [(SumL N)/0]B
 * SumElim B M1 M2 (SumR N) --> M2 N : [(SumR N)/0]B
 *)
| CtorApp : bool -> Term -> Term -> Term -> Term -> Term
(* CtorApp "contains" its type, represented by A, Cin, and aout *)
| IndElim : bool -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term
.

Definition Ctx : Set := list Term.
(* README: the last thing bound in a Ctx is on the LEFT *)

(*** substitution and lifting ***)

(* README: k is the amount we are incrementing the variables, and n is the
 * number of variable bindings under which we have traversed so far *)
Fixpoint lift (n k : nat) (M : Term) {struct M} : Term :=
  match M with
    | Sort i => Sort i
    | ZeroTp => ZeroTp
    | OneTp => OneTp
    | Pi A B => Pi (lift n k A) (lift (S n) k B)
    | PairTp A B => PairTp (lift n k A) (lift (S n) k B)
    | SumTp A B => PairTp (lift n k A) (lift n k B)
    | IndType isP A Cin aout a =>
      IndType isP (lift n k A) (lift (S n) k Cin) (lift (S (S n)) k aout) (lift n k a)
    | Var i =>
      match le_lt_dec n i with
        | left _ => Var (i + k) (* case: i >= n *)
        | right _ => Var i (* case: i < n *)
      end
    | ZeroElim A N => ZeroElim (lift n k A) (lift n k N)
    | One => One
    | OneElim B M N => OneElim (lift (S n) k B) (lift n k M) (lift n k N)
    | Lam A M1 => Lam (lift n k A) (lift (S n) k M1)
    | App M1 M2 => App (lift n k M1) (lift n k M2)
    | Pair M N => Pair (lift n k M) (lift n k N)
    | ProjL M => ProjL (lift n k M)
    | ProjR M => ProjR (lift n k M)
    | SumL M => SumL (lift n k M)
    | SumR M => SumR (lift n k M)
    | SumElim B M1 M2 N =>
      SumElim (lift (S n) k B) (lift n k M1) (lift n k M2) (lift n k N)
    | CtorApp isP A Cin aout x =>
      CtorApp isP (lift n k A) (lift (S n) k Cin) (lift (S (S n)) k aout) (lift n k x)
    | IndElim isP A Cin aout B f a scrut =>
      IndElim isP (lift n k A) (lift (S n) k Cin) (lift (S (S n)) k aout)
      (lift (S n) k B) (lift n k f) (lift n k a) (lift n k scrut)
  end.


Fixpoint substH (n : nat) (s : list Term) (M : Term) {struct M} : Term :=
  match M with
    | Sort i => Sort i
    | ZeroTp => ZeroTp
    | OneTp => OneTp
    | Pi A B => Pi (substH n s A) (substH (S n) s B)
    | PairTp A B => PairTp (substH n s A) (substH (S n) s B)
    | SumTp A B => SumTp (substH n s A) (substH n s B)
    | IndType isP A Cin aout a =>
      IndType isP (substH n s A) (substH (S n) s Cin) (substH (S (S n)) s aout) (substH n s a)
    | Var i =>
      match le_lt_dec n i with
        | right _ => Var i (* case: i < n *)
        | left _ => (* case: i >= n *)
          match nth_error s (i - n) with
            | Some N => lift 0 n N
            | None => Var (i + n)
          end
      end
    | ZeroElim A N => ZeroElim (substH n s A) (substH n s N)
    | One => One
    | OneElim B M N => OneElim (substH (S n) s B) (substH n s M) (substH n s N)
    | Lam A M1 => Lam (substH n s A) (substH (S n) s M1)
    | App M1 M2 => App (substH n s M1) (substH n s M2)
    | Pair M N => Pair (substH n s M) (substH n s N)
    | ProjL M => ProjL (substH n s M)
    | ProjR M => ProjR (substH n s M)
    | SumL M => SumL (substH n s M)
    | SumR M => SumR (substH n s M)
    | SumElim B M1 M2 N =>
      SumElim (substH (S n) s B) (substH n s M1) (substH n s M2) (substH n s N)
    | CtorApp isP A Cin aout x =>
      CtorApp isP (substH n s A) (substH (S n) s Cin) (substH (S (S n)) s aout) (substH n s x)
    | IndElim isP A Cin aout B f a scrut =>
      IndElim isP (substH n s A) (substH (S n) s Cin) (substH (S (S n)) s aout)
      (substH (S n) s B) (substH n s f) (substH n s a) (substH n s scrut)
  end.

Definition subst (s : list Term) (M : Term) := substH 0 s M.
Definition substOne (N M : Term) := substH 0 (N :: nil) M.


(** auxiliary defs dependent on substitution **)

(* lifts all elements of a list of types to create a context of
 * non-dependent types *)
Fixpoint typeList2Ctx (l : list Term) : Ctx :=
  match l with
    | nil => nil
    | A :: l' => (lift 0 (length l') A) :: (typeList2Ctx l')
  end.


(*** helper defs for inductive types ***)

(* checking variable occurrence *)
Fixpoint varOccurs (n : nat) (M : Term) {struct M} : bool :=
  match M with
    | Sort i => false
    | ZeroTp => false
    | OneTp => false
    | Pi A B => varOccurs n A || varOccurs (S n) B
    | PairTp A B => varOccurs n A || varOccurs (S n) B
    | SumTp A B => varOccurs n A || varOccurs n B
    | IndType isP A Cin aout a =>
      (varOccurs n A) || (varOccurs (S n) Cin) || (varOccurs (S (S n)) aout) || (varOccurs n a)
    | Var i =>
      match eq_nat_dec n i with
        | left _ => true
        | right _ => false
      end
    | ZeroElim A M => (varOccurs n A) || (varOccurs n M)
    | One => false
    | OneElim B M N => (varOccurs (S n) B) || (varOccurs n M) || (varOccurs n N)
    | Lam A M => (varOccurs n A) || (varOccurs (S n) M)
    | App M1 M2 => (varOccurs n M1) || (varOccurs n M2)
    | Pair M N => (varOccurs n M) || (varOccurs n N)
    | ProjL M => (varOccurs n M)
    | ProjR M => (varOccurs n M)
    | SumL M => (varOccurs n M)
    | SumR M => (varOccurs n M)
    | SumElim B M1 M2 N =>
      (varOccurs (S n) B) || (varOccurs n M1) || (varOccurs n M2)
        || (varOccurs n N)
    | CtorApp isP A Cin aout x =>
      (varOccurs n A) || (varOccurs (S n) Cin) || (varOccurs (S (S n)) aout) || (varOccurs n x)
    | IndElim isP A Cin aout B f a scrut =>
      (varOccurs n A) || (varOccurs (S n) Cin) || (varOccurs (S (S n)) aout)
        || (varOccurs (S n) B) || (varOccurs n f) || (varOccurs n a)
          ||  (varOccurs n scrut)
  end.


(* checking positivity *)
Fixpoint varIsPositive (n : nat) (M : Term) {struct M} : bool :=
  match M with
    | Pi A B => (negb (varOccurs n A)) && varIsPositive (S n) B
    | PairTp A B => varIsPositive n A && varIsPositive (S n) B
    | SumTp A B => varIsPositive n A && varIsPositive n B
    | App (Var i) a => negb (varOccurs n a) (* holds whether or not n = i *)
    | _ => negb (varOccurs n M)
  end.

(* check whether an arg to CtorApp can be eliminated *)
Fixpoint canElim (n : nat) (A M : Term) :=
  match A, M with
    | Pi _ B, Lam _ M => canElim (S n) B M
    | PairTp A B, Pair M1 M2 => (canElim n A M1) && (canElim (S n) B M2)
    | SumTp A B, SumL M => (canElim n A M)
    | SumTp A B, SumR M => (canElim n B M)
    | App (Var i) a, M => true
    | _, _ => true
  end.


(* transform a type into its elimination type, assuming it is positive;
 * README: ctx assumptions: A has context (ctx,(Pi Ae (Sort i)),ctx')
 * for some i and |ctx'| = n, Ae has context ctx, indTp has context
 * (ctx,Ae), Be has context (ctx,Ae,indTp), and the return context
 * should be (ctx,ctx')
 * NOTE: if A is positive, the substitutions of (Lam Ae indTp) into
 * subterms of A below are essentially no-ops, except they do lowering
 *)
Fixpoint elimType (n : nat) (A : Term) (Ae indTp Be : Term) :=
  match A with
    | Pi A B =>
      Pi (substH n (Lam Ae indTp :: nil) A) (elimType (S n) B Ae indTp Be)
    | PairTp A B =>
      PairTp (elimType n A Ae indTp Be) (elimType (S n) B Ae indTp Be)
    | SumTp A B =>
      SumTp (elimType n A Ae indTp Be) (elimType n B Ae indTp Be)
    | App (Var i) a =>
      match eq_nat_dec n i with
        | left _ =>
          PairTp (substOne (substH n (Lam Ae indTp :: nil) a) (lift 1 n indTp))
          (substH 1 (a :: nil) (lift 2 n Be))
        | right _ => substH n (Lam Ae indTp :: nil) A
      end
    | _ => substH n (Lam Ae indTp :: nil) A
  end.

(* construct the arg to the eliminator from an arg to CtorApp
 * README: (FIXME: contexts)
 * M is in context (ctx,ctx') *)
Fixpoint elimArg (n : nat) (A M : Term) (isP : bool) (Ae Cin aout Be f : Term) :=
  match A, M with
    | Pi _ B, Lam A M => Lam A (elimArg (S n) B M isP Ae Cin aout Be f)
    | PairTp A B, Pair M1 M2 =>
      Pair (elimArg n A M1 isP Ae Cin aout Be f)
      (elimArg (S n) B M2 isP Ae Cin aout Be f)
    | SumTp A B, SumL M => SumL (elimArg n A M isP Ae Cin aout Be f)
    | SumTp A B, SumR M => SumR (elimArg n B M isP Ae Cin aout Be f)
    | App (Var i) a, M =>
      match eq_nat_dec n i with
        | left _ =>
          Pair M (
            IndElim isP (lift 0 n Ae) (lift 1 n Cin) (lift 1 n aout)
            (lift 2 n Be) (lift 0 n f)
            (substH n (lift 0 n (Lam Ae (IndType isP Ae Cin aout (Var 0))) :: nil) a)
            M
          )
        | right _ => M
      end
    | _, _ => M
  end.


(*** convertability ***)

Inductive rrto : Term -> Term -> Set :=
| RR_OneElim : forall B M, rrto (OneElim B M One) M
| RR_Beta : forall A M N, rrto (App (Lam A M) N) (substOne N M)
| RR_PairElimL : forall M N, rrto (ProjL (Pair M N)) M
| RR_PairElimR : forall M N, rrto (ProjR (Pair M N)) M
| RR_SumElimL : forall B M1 M2 N,
  rrto (SumElim B M1 M2 (SumL N)) (App M1 N)
| RR_SumElimR : forall B M1 M2 N,
  rrto (SumElim B M1 M2 (SumR N)) (App M2 N)
| RR_iota : forall isP isP' Ae Ae' Cin Cin' aout aout' Be f a N,
  canElim 0 Cin N = true ->
  rrto (IndElim isP Ae Cin aout Be f a (CtorApp isP' Ae' Cin' aout' N))
  (App f (elimArg 0 Cin N isP Ae Cin aout Be f))
| RR_Pi1 : forall A A' B, rrto A A' -> rrto (Pi A B) (Pi A' B)
| RR_Pi2 : forall A B B', rrto B B' -> rrto (Pi A B) (Pi A B')
| RR_PairTp1 : forall A A' B, rrto A A' -> rrto (PairTp A B) (PairTp A' B)
| RR_PairTp2 : forall A B B', rrto B B' -> rrto (PairTp A B) (PairTp A B')
| RR_SumTp1 : forall A A' B, rrto A A' -> rrto (SumTp A B) (SumTp A' B)
| RR_SumTp2 : forall A B B', rrto B B' -> rrto (SumTp A B) (SumTp A B')
| RR_IndType1 : forall isP A A' Cin aout a,
  rrto A A' ->
  rrto (IndType isP A Cin aout a) (IndType isP A' Cin aout a)
| RR_IndType2 : forall isP A Cin Cin' aout a,
  rrto Cin Cin' ->
  rrto (IndType isP A Cin aout a) (IndType isP A Cin' aout a)
| RR_IndType3 : forall isP A Cin aout aout' a,
  rrto aout aout' ->
  rrto (IndType isP A Cin aout a) (IndType isP A Cin aout' a)
| RR_IndType4 : forall isP A Cin aout a a',
  rrto a a' ->
  rrto (IndType isP A Cin aout a) (IndType isP A Cin aout a')
| RR_ZeroElim1 : forall A A' M,
  rrto A A' ->
  rrto (ZeroElim A M) (ZeroElim A' M)
| RR_ZeroElim2 : forall A M M',
  rrto M M' ->
  rrto (ZeroElim A M) (ZeroElim A M')
| RR_OneElim1 : forall A A' M N,
  rrto A A' ->
  rrto (OneElim A M N) (OneElim A' M N)
| RR_OneElim2 : forall A M M' N,
  rrto M M' ->
  rrto (OneElim A M N) (OneElim A M' N)
| RR_OneElim3 : forall A M N N',
  rrto N N' ->
  rrto (OneElim A M N) (OneElim A M N')
| RR_Lam1 : forall A A' M, rrto A A' -> rrto (Lam A M) (Lam A' M)
| RR_Lam2 : forall A M M', rrto M M' -> rrto (Lam A M) (Lam A M')
| RR_App1 : forall M M' N , rrto M M' -> rrto (App M N) (App M' N)
| RR_App2 : forall M N N', rrto N N' -> rrto (App M N) (App M N')
| RR_Pair1 : forall M M' N , rrto M M' -> rrto (Pair M N) (Pair M' N)
| RR_Pair2 : forall M N N', rrto N N' -> rrto (Pair M N) (Pair M N')
| RR_ProjL : forall M M', rrto M M' -> rrto (ProjL M) (ProjL M')
| RR_ProjR : forall M M', rrto M M' -> rrto (ProjR M) (ProjR M')
| RR_SumL : forall M M', rrto M M' -> rrto (SumL M) (SumL M')
| RR_SumR : forall M M', rrto M M' -> rrto (SumR M) (SumR M')
| RR_SumElim1 : forall B B' M1 M2 N,
  rrto B B' ->
  rrto (SumElim B M1 M2 N) (SumElim B' M1 M2 N)
| RR_SumElim2 : forall B M1 M1' M2 N,
  rrto M1 M1' ->
  rrto (SumElim B M1 M2 N) (SumElim B M1' M2 N)
| RR_SumElim3 : forall B M1 M2 M2' N,
  rrto M2 M2' ->
  rrto (SumElim B M1 M2 N) (SumElim B M1 M2' N)
| RR_SumElim4 : forall B M1 M2 N N',
  rrto N N' ->
  rrto (SumElim B M1 M2 N) (SumElim B M1 M2 N')
| RR_CtorApp1 : forall isP A A' Cin aout N,
  rrto A A' ->
  rrto (CtorApp isP A Cin aout N) (CtorApp isP A' Cin aout N)
| RR_CtorApp2 : forall isP A Cin Cin' aout N,
  rrto Cin Cin' ->
  rrto (CtorApp isP A Cin aout N) (CtorApp isP A Cin' aout N)
| RR_CtorApp3 : forall isP A Cin aout aout' N,
  rrto aout aout' ->
  rrto (CtorApp isP A Cin aout N) (CtorApp isP A Cin aout' N)
| RR_CtorApp4 : forall isP A Cin aout N N',
  rrto N N' ->
  rrto (CtorApp isP A Cin aout N) (CtorApp isP A Cin aout N')
| RR_IndElim1 : forall isP A A' Cin aout B f a x,
  rrto A A' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A' Cin aout B f a x)
| RR_IndElim2 : forall isP A Cin Cin' aout B f a x,
  rrto Cin Cin' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin' aout B f a x)
| RR_IndElim3 : forall isP A Cin aout aout' B f a x,
  rrto aout aout' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin aout' B f a x)
| RR_IndElim4 : forall isP A Cin aout B B' f a x,
  rrto B B' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin aout B' f a x)
| RR_IndElim5 : forall isP A Cin aout B f f' a x,
  rrto f f' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin aout B f' a x)
| RR_IndElim6 : forall isP A Cin aout B f a a' x,
  rrto a a' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin aout B f a' x)
| RR_IndElim7 : forall isP A Cin aout B f a x x',
  rrto x x' ->
  rrto (IndElim isP A Cin aout B f a x) (IndElim isP A Cin aout B f a x')
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
| SubTp_Refl : forall A , subtype A A
| SubTp_Sort : forall i j , i <= j -> subtype (Sort i) (Sort j)
| SubTp_Pi : forall A B B' , subtype B B' -> subtype (Pi A B) (Pi A B')
.


(*** typing ***)

Inductive HasTp (ctx : Ctx) : Term -> Term -> Set :=
| HT_convR : forall M A A' , HasTp ctx M A -> rrto A A' -> HasTp ctx M A'
| HT_convL : forall M A A' , HasTp ctx M A -> rrto A' A -> HasTp ctx M A'
| HT_sub : forall M A A' , HasTp ctx M A -> subtype A A' -> HasTp ctx M A'
| HT_Sort : forall i, HasTp ctx (Sort i) (Sort (S i))
| HT_ZeroTp : HasTp ctx ZeroTp (Sort 0)
| HT_OneTp : HasTp ctx OneTp (Sort 0)
| HT_Pi_Pred : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) B (Sort i) ->
  HasTp ctx (Pi A B) (Sort i)
| HT_Pi_Impred : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) B (Sort 0) ->
  HasTp ctx (Pi A B) (Sort 0)
| HT_PairTp_Pred : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) B (Sort i) ->
  HasTp ctx (PairTp A B) (Sort i)
| HT_PairTp_Impred : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) B (Sort 0) ->
  HasTp ctx (PairTp A B) (Sort 0)
| HT_SumTp : forall i A B ,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) B (Sort i) ->
  HasTp ctx (SumTp A B) (Sort i)
| HT_IndType_Pred : forall A Cin aout a i,
  HasTp ctx A (Sort (S i)) ->
  HasTp ((Pi A (Sort (S i))) :: ctx) Cin (Sort (S i)) ->
  varIsPositive 0 Cin = true ->
  HasTp (Cin :: (Pi A (Sort (S i))) :: ctx) aout A ->
  HasTp ctx a A ->
  HasTp ctx (IndType true A Cin aout a) (Sort (S i))
| HT_IndType_Impred : forall A Cin aout a i,
  HasTp ctx A (Sort i) ->
  HasTp ((Pi A (Sort i)) :: ctx) Cin (Sort i) ->
  varIsPositive 0 Cin = true ->
  HasTp (Cin :: (Pi A (Sort i)) :: ctx) aout A ->
  HasTp ctx a A ->
  HasTp ctx (IndType false A Cin aout a) (Sort 0)
| HT_Var : forall i A, isNth Term A i ctx ->
  HasTp ctx (Var i) A
| HT_ZeroElim : forall A i M,
  HasTp ctx A (Sort i) ->
  HasTp ctx M ZeroTp ->
  HasTp ctx (ZeroElim A M) A
| HT_One : HasTp ctx One OneTp
| HT_OneElim : forall B i M N,
  HasTp (OneTp :: ctx) B (Sort i) ->
  HasTp ctx N OneTp ->
  HasTp ctx M (substOne One B) ->
  HasTp ctx (OneElim B M N) (substOne N B)
| HT_Lam : forall A i M B,
  HasTp ctx A (Sort i) ->
  HasTp (A :: ctx) M B ->
  HasTp ctx (Lam A M) (Pi A B)
| HT_App : forall A B M N,
  HasTp ctx M (Pi A B) -> HasTp ctx N A ->
  HasTp ctx (App M N) (substOne N B)
| HT_Pair : forall A B i M N,
  HasTp ctx M A -> HasTp (A :: ctx) B (Sort i) ->
  HasTp ctx N (substOne M B) ->
  HasTp ctx (Pair M N) (PairTp A B)
| HT_ProjL : forall A B M,
  HasTp ctx M (PairTp A B) ->
  HasTp ctx (ProjL M) A
| HT_ProjR : forall A B M,
  HasTp ctx M (PairTp A B) ->
  HasTp ctx (ProjR M) (substOne (ProjL M) B)
| HT_SumL : forall A B i M,
  HasTp ctx M A -> HasTp ctx B (Sort i) ->
  HasTp ctx (SumL M) (SumTp A B)
| HT_SumR : forall A B i M,
  HasTp ctx M B -> HasTp ctx A (Sort i) ->
  HasTp ctx (SumR M) (SumTp A B)
| HT_SumElim : forall A1 A2 B i M1 M2 N,
  HasTp ctx N (SumTp A1 A2) ->
  HasTp (SumTp A1 A2 :: ctx) B (Sort i) ->
  HasTp ctx M1 (Pi A1 (substOne (SumL (Var 0)) (lift 1 1 B))) ->
  HasTp ctx M2 (Pi A2 (substOne (SumL (Var 0)) (lift 1 1 B))) ->
  HasTp ctx (SumElim B M1 M2 N) (substOne N B)
| HT_CtorApp : forall isP A Cin aout x i,
  HasTp ctx A (Sort i) ->
  HasTp ((Pi A (Sort i)) :: ctx) Cin (Sort i) ->
  varIsPositive 0 Cin = true ->
  HasTp (Cin :: (Pi A (Sort i)) :: ctx) aout A ->
  HasTp ctx x (substOne (Lam A (IndType isP A Cin aout (Var 0))) Cin) ->
  HasTp ctx (CtorApp isP A Cin aout x)
  (IndType isP A Cin aout
    (subst (x :: Lam A (IndType isP A Cin aout (Var 0)) :: nil) aout))
| HT_IndElim_Pred : forall i A Cin aout Be f a N,
  HasTp ctx A (Sort i) ->
  HasTp ((Pi A (Sort i)) :: ctx) Cin (Sort i) ->
  varIsPositive 0 Cin = true ->
  HasTp (Cin :: (Pi A (Sort i)) :: ctx) aout A ->
  HasTp (IndType true (lift 0 1 A) (lift 1 1 Cin) (lift 2 1 aout) (Var 0) :: A :: ctx) Be (Sort i) ->
  HasTp ctx f (Pi A (Pi (IndType true (lift 0 1 A) (lift 1 1 Cin) (lift 2 1 aout) (Var 0)) Be)) ->
  HasTp ctx a A ->
  HasTp ctx N (IndType true A Cin aout a) ->
  HasTp ctx (IndElim true A Cin aout Be f a N) (subst (a :: N :: nil) Be)
| HT_IndElim_Impred : forall i A Cin aout Be f a N,
  HasTp ctx A (Sort i) ->
  HasTp ((Pi A (Sort i)) :: ctx) Cin (Sort i) ->
  varIsPositive 0 Cin = true ->
  HasTp (Cin :: (Pi A (Sort i)) :: ctx) aout A ->
  HasTp (IndType true (lift 0 1 A) (lift 1 1 Cin) (lift 2 1 aout) (Var 0) :: A :: ctx) Be (Sort 0) ->
  HasTp ctx f (Pi A (Pi (IndType true (lift 0 1 A) (lift 1 1 Cin) (lift 2 1 aout) (Var 0)) Be)) ->
  HasTp ctx a A ->
  HasTp ctx N (IndType true A Cin aout a) ->
  HasTp ctx (IndElim true A Cin aout Be f a N) (subst (a :: N :: nil) Be)
.

Inductive WfCtx : Ctx -> Set :=
| WfCtx_nil : WfCtx nil
| WfCtx_cons ctx A i : WfCtx ctx -> HasTp ctx A (Sort i) -> WfCtx (A :: ctx)
.
