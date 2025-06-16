(* Require Import ZArith. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
Require Import monad_model.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* ======== *)

Module MLTypes.
Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_uvar
  | ml_uterm.

Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.

Definition val_nonempty (M : UU0 -> UU0) := tt.

Notation loc := (@loc _ monad_model.locT_nat).

Inductive uterm : Type :=
| uLink : loc ml_uvar -> uterm
| uInt : nat -> uterm
| uNode : uterm -> uterm -> uterm.

Inductive uvar : Type :=
| uVar : nat -> uvar
| uTerm : uterm -> uvar.

Definition ml_type_eq_mixin := hasDecEq.Build _ (comparePc MLTypes.ml_type_eq_dec).
HB.instance Definition ml_type_eqType := ml_type_eq_mixin.

End MLTypes.

(* ======== *)

Module CoqTypeNat.
Import MLTypes.

Section with_monad.
Context [M : Type -> Type].

Fixpoint coq_type_nat (T : ml_type) : Type :=
  match T with
  | ml_int => nat
  | ml_bool => bool
  | ml_unit => unit
  | ml_arrow T1 T2 => coq_type_nat T1 -> M (coq_type_nat T2)
  | ml_ref T1 => loc T1
  | ml_uvar => uvar
  | ml_uterm => uterm
  end.
End with_monad.

HB.instance Definition _ := @isML_universe.Build ml_type coq_type_nat ml_unit val_nonempty.

#[short(type=typedStoreFailMonad)]
HB.structure Definition MonadTypedStoreFail S S0 op :=
  {M of isMonadTypedStore S S0 op M & MonadFail M }.

Definition typedStoreFailMonad (N : monad) :=
  typedStoreFailMonad ml_type N monad_model.locT_nat.

Definition typedStoreMonad (N : monad) :=
  typedStoreMonad ml_type N monad_model.locT_nat.

(*
Definition typedStoreRunMonad (N : monad) :=
  typedStoreRunMonad ml_type N monad_model.locT_nat.
*)

(* ======== *)

Require Import List.
Import ListNotations.

Section Unification.

Variables (N : monad) (M : typedStoreFailMonad N).
Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Section Definitions.

(*
Inductive uterm : Type :=
| uLink : loc ml_uvar -> uterm
| uInt : nat -> uterm
| uNode : uterm -> uterm -> uterm.

Inductive uvar : Type :=
| uVar : nat -> uvar
| uTerm : uterm -> uvar.
*)

Definition uget (v : loc ml_uvar) : M uvar := cget v.

Definition uset (v : loc ml_uvar) : uvar -> M unit := cput v.

Definition constr_list : Type := list (uterm * uterm)%type.

End Definitions.

Section unify.

Fixpoint unify (h : nat) (l : constr_list) : M unit :=
if h is h.+1 then match l with
| [::] => Ret tt

| (uInt m, uInt n) :: l' =>
  if m == n then unify h l' else fail

| (uNode tl1 tl2, uNode tr1 tr2) :: l' =>
  unify h ((tl1, tr1) :: (tl2, tr2) :: l')

| (uLink v1, uLink v2) :: l' =>
  do get1 <- uget v1;
  do get2 <- uget v2;
  match get1, get2 with
  | uVar m, uVar n =>
    if m == n then unify h l'
    else uset v1 get2 >> unify h l'
  | uVar _, uTerm _ => uset v1 get2 >> unify h l'
  | uTerm _, uVar _ => uset v2 get1 >> unify h l'
  | uTerm t1, uTerm t2 => unify h ((t1, t2) :: l')
  end

| (uLink v1, t2) :: l' => uset v1 (uTerm t2) >> unify h l'
| (t1, uLink v2) :: l' => uset v2 (uTerm t1) >> unify h l'

| _ => fail
end else fail.

End unify.
End Unification.

End CoqTypeNat.