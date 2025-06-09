From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From mathcomp Require Import finmap.

Require Import preamble hierarchy monad_lib fail_lib state_lib.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Require Import unif.

Module ActionMonad.
Section actionMonad.

Import Monoid.Theory.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (N : monad).

Variables SM : stateRunMonad S N.

Definition acto : UU0 -> UU0 :=
  let op := op in fun A => SM A.
Local Notation M := acto.

Let ret : idfun ~~> M := fun A => Ret.
Let bind A B (m : M A) (f : A -> M B) : M B := m >>= f.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof. exact:bindretf. Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof. exact:bindmret. Qed.

Let associative : BindLaws.associative bind.
Proof. exact:bindA. Qed.

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

HB.instance Definition _ :=
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.

Let actionBind A B (s : S) (m : M A) (f : A -> M B) :
  action s (bind m f) = bind (action s m) f :> M B.
Proof.
rewrite /action /action.
by rewrite -!bindA.
Qed.

Let runActionT (A : UU0) (m : M A) : N (A * S)%type :=
  runStateT m S0.

Let runActionTret (A : UU0) (a : A) :
  runActionT (ret a) = Ret (a, S0).
Proof. by rewrite /runActionT runStateTret. Qed.

Let runActionTbind (A B : UU0) (m : M A) (f : A -> M B) :
  runActionT (bind m f) =
  runActionT m >>=
    fun x => runActionT (f x.1) >>=
    fun y => Ret (y.1, op x.2 y.2).
Proof.
rewrite /runActionT.
rewrite runStateTbind.
apply eq_bind => -[a s1] /=.
(*
have H: runStateT (f a) s1 =
        runStateT (f a) s1 >>= fun x => runStateT (Ret x.1) x.2.
  move => ?; rewrite -[LHS]bindmret.
  apply: eq_bind => x.
  rewrite runStateTret.
  by case: x.
rewrite (H SM).
have H2: forall (x : B) (s : S),
        Ret (x, op s1 s) = runStateT (Ret x) (op s1 s)
by move => *; rewrite runStateTret.
under [RHS]eq_bind do rewrite (H2 N SM).
rewrite -runStateTbind.

Qed.
*)
Admitted.

Let runActionTaction (A : UU0) (s : S) (m : M A) :
    runActionT (action s m) = 
    runActionT m >>= fun x => Ret (x.1, op s x.2).
Proof.
rewrite /runActionT /action.
rewrite runStateTbind runStateTget bindretf runStateTbind runStateTput bindretf /=.
Admitted.
(*apply eq_bind => -[a s1] //=.
Qed.
*)
HB.instance Definition _ :=
  isMonadAction.Build S S0 op acto action0 actionA actionBind.

HB.instance Definition _ :=
  isMonadActionRun.Build S S0 op N acto runActionTret runActionTbind runActionTaction.

End actionMonad.
End ActionMonad.
HB.export ActionMonad.

(*
Module ActionFailMonad.
Section actionFailMonad.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (N : failMonad).

Definition acto : UU0 -> UU0 := ActionMonad.acto op N.
Local Notation M := acto.

Let failM (A : UU0) : M A := fail.

Let bindfailf : BindLaws.left_zero (@bind M) failM.
Proof. by move => *; rewrite /failM /bind /= bindfailf. Qed.

Let runActionTfail A : runActionT (failM A) = fail.
Proof. done. Qed.

HB.instance Definition _ := MonadActionRun.on M.

HB.instance Definition _ := isMonadFail.Build acto bindfailf.

HB.instance Definition _ :=
  isMonadActionRunFail.Build S S0 op N acto runActionTfail.

End actionFailMonad.
End ActionFailMonad.
HB.export ActionFailMonad.
*)