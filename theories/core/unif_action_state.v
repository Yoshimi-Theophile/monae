From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From mathcomp Require Import finmap.

Require Import preamble hierarchy monad_lib fail_lib state_lib.
From HB Require Import structures.
Require Import monad_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Require Import unif.

Module ActionMonad.
Section actionMonad.

Import Monoid.Theory.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (SM : stateMonad S).

Definition acto := let op := op in SM.
Local Notation M := acto.

HB.instance Definition _ := Monad.on acto.

Let action {A : UU0} s2 (m : M A) : M A :=
  get >>= fun s1 => put (op s1 s2) >> m.

Let action0 A : @action A S0 = id.
Proof.
apply:boolp.funext => x.
rewrite /action.
under [in LHS]eq_bind do rewrite mulm1.
by rewrite -bindA getput bindskipf.
Qed.

Let actionA A (x y : S) (m : M A) :
  action x (action y m) = action (op x y) m.
Proof.
rewrite /action.
apply: eq_bind => s1.
by rewrite -bindA putget bindA bindretf -bindA putput mulmA.
Qed.

Let actionBind A B (s : S) (m : M A) (f : A -> M B) :
  action s (bind m f) = bind (action s m) f :> M B.
Proof.
rewrite /action /action.
by rewrite -!bindA.
Qed.

HB.instance Definition _ :=
  isMonadAction.Build S S0 op M action0 actionA actionBind.
End actionMonad.