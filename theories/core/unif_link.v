(* Require Import ZArith. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Notation loc := (@loc _ nat).

(* ======== *)

Module MLTypes.
Inductive ml_type : Set :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type)
  | ml_list (_ : ml_type)
  | ml_option (_ : ml_type)
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

Inductive uterm : Type :=
| uLink : loc ml_uvar -> uterm
| uInt : nat -> uterm
| uNode : uterm -> uterm -> uterm.

Inductive uvar : Type :=
| uVar : nat -> uvar
| uTerm : uterm -> uvar.

Inductive btree : Type :=
| btVar : nat -> btree
| btInt : nat -> btree
| btNode : btree -> btree -> btree.

Scheme Equality for btree.

Lemma btree_eq_boolP : Equality.axiom btree_eq_dec.
Proof. move=> x y. case: btree_eq_dec => //= H; by constructor. Qed.
HB.instance Definition _ := hasDecEq.Build _ btree_eq_boolP.


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
  | ml_list T1 => list (coq_type_nat T1)
  | ml_option T1 => option (coq_type_nat T1)
  | ml_ref T1 => loc T1
  | ml_uvar => uvar
  | ml_uterm => uterm
  end.
End with_monad.

HB.instance Definition _ := @isML_universe.Build ml_type coq_type_nat ml_unit val_nonempty.

#[short(type=typedStoreFailRunMonad)]
HB.structure Definition MonadTypedStoreFailRun S S0 op :=
  {M of isMonadTypedStoreRun S S0 op M & MonadFail M }.

Definition typedStoreFailRunMonad (N : monad) :=
  typedStoreFailRunMonad ml_type N nat.

Definition typedStoreMonad (N : monad) :=
  typedStoreMonad ml_type N nat.

(*
Definition typedStoreRunMonad (N : monad) :=
  typedStoreRunMonad ml_type N nat.
*)

(* ======== *)

(*Require Import List.
Import ListNotations.*)

Section Unification.

Variables (N : monad) (M : typedStoreFailRunMonad N).
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

Inductive represents : M uterm -> btree -> Prop :=
  | RVar (m : M uterm) (n : nat) :
    (do u <- m; if u is uLink v then uget v else fail) = m >> Ret (uVar n) ->
    represents m (btVar n)
  | RInt (m : M uterm) (n : nat) :
    m = m >> Ret (uInt n) ->
    represents m (btInt n)
  | RNode (m : M uterm) u1 u2 bt1 bt2 :
    m = m >> Ret (uNode u1 u2) ->
    represents (m >> Ret u1) bt1 ->
    represents (m >> Ret u2) bt2 ->
    represents m (btNode bt1 bt2)
  | RLink (m : M uterm) (v : loc ml_uvar) (u : uterm) (bt : btree) :
    m = m >> Ret (uLink v) ->
    m >> uget v = m >> Ret (uTerm u)  ->
    represents (m >> Ret u) bt ->
    represents m bt.

Section repr.
Variable vars_loc : loc (ml_list (ml_option (ml_ref ml_uvar))).
Definition add_var n : M (loc ml_uvar) :=
  do vars <- cget vars_loc;
  if seq.nth None vars n is Some l then Ret l else
  do l <- cnew ml_uvar (uVar n);
  cput vars_loc (set_nth None vars n (Some l)) >> Ret l.

Definition add_var_skip n : M unit :=
  do vars <- cget vars_loc;
  if nth None vars n then skip else
  do l <- cnew ml_uvar (uVar n);
  cput vars_loc (set_nth None vars n (Some l)).

Lemma add_var_skipE n : add_var n >> skip = add_var_skip n.
Proof.
rewrite !bindA.
apply: eq_bind => vars.
case Hnth: (nth None vars n) => [l|] /=.
  by rewrite !bindretf.
rewrite !bindA.
by under eq_bind do rewrite bindA bindretf bindmskip.
Qed.

Fixpoint repr_btree (bt : btree) : M uterm :=
  match bt with
  | btVar n =>
      do l <- add_var n;
      Ret (uLink l)
  | btInt n =>
      Ret (uInt n)
  | btNode bt1 bt2 =>
      do u1 <- repr_btree bt1;
      do u2 <- repr_btree bt2;
      Ret (uNode u1 u2)
  end.
End repr.

Definition cenv (vs : list nat) :=
  do vars <- cnew (ml_list (ml_option (ml_ref ml_uvar))) nil;
  foldr (fun n m => add_var_skip vars n >> m) (Ret vars) vs.

Lemma cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2)
  (s1 : coq_type N T1) (A : UU0) (k : coq_type N T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> (cget r2 >>= k) =
  cget r2 >>= (fun v : coq_type N T2 => cput r1 s1 >> k v).
Proof. by move=> *; rewrite -bindA cputgetC. Qed.

Lemma cenv_cat vs1 vs2 :
  cenv (vs1 ++ vs2) = cenv vs1 >>= fun vars =>
    foldr (fun n m => add_var_skip vars n >> m) (Ret vars) vs2.
Proof.
rewrite bindA /cenv.
apply: eq_bind => r.
elim: vs1 => [|n vs1 IH] /=.
  by rewrite bindretf.
rewrite !bindA.
apply: eq_bind => vars.
case Hnth: nth => [rn|].
  by rewrite !bindretf IH.
rewrite !bindA.
apply: eq_bind => rn.
by rewrite IH.
Qed.

Lemma cenv_chk vs : cenv vs >>= (fun r => cchk r >> Ret r) = cenv vs.
Proof.
elim/last_ind: vs => [|vs n _].
  rewrite bindA.
  under eq_bind do rewrite bindretf.
  by rewrite cnewchk.
rewrite -cats1 cenv_cat.
rewrite bindA.
apply: eq_bind=> r /=.
rewrite bindA bindretf -bindA.
congr (_ >> _).
rewrite !bindA -[LHS]cgetchk -[RHS]cgetchk.
apply: eq_bind => vars.
case Hnth: nth => [rn|].
  by rewrite !bindretf bindmskip cchkdup.
apply: eq_bind => _ /=.
rewrite !bindA.
by under eq_bind do rewrite cputchk.
Qed.

Lemma cenv_get_nth vs : forall T i (k : _ -> _ -> bool -> M T),
  do r <- cenv vs; do vars <- cget r; k r vars (nth None vars i) =
  do r <- cenv vs; do vars <- cget r; k r vars (i \in vs).
Proof.
elim/last_ind: vs => [|vs n IH] T i k.
  by rewrite /cenv /= bindmret !cnewget /= in_nil nth_default.
rewrite -{1 2}cats1 cenv_cat /= 2!bindA.
under eq_bind do rewrite bindA bindretf !bindA.
under [RHS]eq_bind do rewrite bindA bindretf !bindA.
rewrite (IH _ _ (fun _ _ cond => (if cond then _ else _) >> _)).
rewrite (IH _ _ (fun _ _ cond => (if cond then _ else _) >> _)).
case/boolP: (n \in vs) => Hn.
  under eq_bind do rewrite bindskipf cgetget.
  rewrite IH.
  under [RHS]eq_bind do rewrite bindskipf cgetget.
  rewrite mem_rcons in_cons.
  have [-> |] //= := eqVneq i n.
  by rewrite Hn.
under [LHS]eq_bind do under eq_bind do
    (rewrite bindA; under eq_bind do rewrite cputget nth_set_nth /=).
under [RHS]eq_bind do under eq_bind do
    (rewrite bindA; under eq_bind do rewrite cputget).
rewrite mem_rcons in_cons.
have [-> | Hin] //= := eqVneq i n.
by rewrite (IH _ _ (fun _ _ cond => _ >>= fun l => _ >> k _ _ cond)).
Qed.

Lemma crunenv vs : crun (cenv vs).
Proof.
elim/last_ind: vs => [|vs n IH].
  by rewrite /cenv bindmret crunnew0.
rewrite -cats1 cenv_cat /=.
rewrite -crunmskip bindA.
under eq_bind do rewrite bindA bindretf bindmskip.
rewrite (cenv_get_nth _ _ (fun _ _ cond => if cond then _ else _)).
case/boolP: (n \in vs) => Hn.
  under eq_bind => r do
    rewrite -(bindretf r (fun=>skip)) -(bindretf tt (fun=>Ret r))
            -!bindA -/(cchk r).
  by rewrite -bindA crunmskip cenv_chk.
rewrite -bindA_uncurry.
rewrite -[_ >>= fun _ : _ * _ => _]bindA_uncurry.
apply: crungetput.
rewrite (bindA_uncurry _ _ (fun (x : _ * _) y => cget x.1)).
rewrite (bindA_uncurry _ _ (fun x y => _ >> cget x)).
rewrite -crunmskip bindA.
under eq_bind do
  rewrite bindA -[cget _ >> _]bindmret !bindA cgetnewD bindretf -bindA.
rewrite -bindA crunmskip -bindA.
apply: crunnew.
rewrite -crunmskip bindA.
under eq_bind => r do
  rewrite -(bindretf r (fun=>skip)) -(bindskipf (Ret r)) -!bindA -/(cchk r).
by rewrite -(bindA (cenv vs)) crunmskip cenv_chk.
Qed.

Lemma repr_btree_ok vs bt : represents (cenv vs >>= repr_btree^~ bt) bt.
Proof.
elim: bt vs => /= [n | n | bt1 IH1 bt2 IH2] vs.
- constructor.
  rewrite !bindA.
  rewrite -(cnewput (ml_list _) nil) -[RHS](cnewput (ml_list _) nil).
  apply: eq_bind => vars.
  set ws := nil.
  have : seq.nth None ws n = None by case n.
  elim: vs ws => /= [|a vs IH] ws Hws.
    rewrite !bindretf !bindA !cputget Hws.
    rewrite -cputchk bindA [RHS]bindA.
    apply: eq_bind => _.
    rewrite [X in _ >> X]bindA.
    under cchknewE => l Hl.
      under eq_bind do rewrite bindretf.
      rewrite bindA bindretf -[uget _]cgetret cputgetC //.
      over.
    rewrite cnewget [X in _ = _ >> X]bindA.
    apply: cchknewE => l _.
    by rewrite bindA !bindretf.
  have [<-|na] := eqVneq n a.
    rewrite !bindA !cputget.
    under eq_bind do rewrite Hws.
    under [RHS]eq_bind do rewrite Hws.
    rewrite -cputchk !bindA !bindskipf.
    apply eq_bind => _.
    rewrite -(cnewput ml_uvar (uVar n)).
    rewrite -[in RHS](cnewput ml_uvar (uVar n)).
    apply: cgetnewE => l Hl.
    elim: vs ws {IH Hws} => /= [|b vs IH] ws.
      rewrite !bindretf !bindA !cputget.
      rewrite nth_set_nth /= eqxx !bindretf.
      by rewrite -[uget _]cgetret cputgetC // cputget.
    rewrite !bindA !cputget nth_set_nth /=.
    case/boolP: (b == n) => bn.
      by rewrite !bindretf IH.
    case nthb: (seq.nth None ws b) => [l'|].
      by rewrite !bindretf IH.
    rewrite !bindA -!cputnewC.
    rewrite !cputgetC 1?eq_sym // -!cputnewC.
    apply: eq_bind => _.
    apply: eq_bind => _.
    apply: eq_bind => r.
    rewrite -[cput vars _ >> _]bindA cputput.
    rewrite -[cput vars _ >> (cput _ _ >> _)]bindA cputput.
    rewrite (_ : set_nth _ _ _ _ =
                 set_nth None (set_nth None ws b (Some r)) n (Some l)).
      by rewrite IH.
    by rewrite set_set_nth eq_sym (negbTE bn).
  rewrite !bindA !cputget.
  case ntha: (seq.nth None ws a) => [l|].
    by rewrite !bindretf IH.
  rewrite !bindA.
  rewrite -!cputnewC.
  apply: eq_bind => _.
  apply: eq_bind => l.
  rewrite IH //.
  by rewrite nth_set_nth /= (negbTE na).
- constructor.
  by rewrite [RHS]bindA bindretf.
- apply: (@RNode _ (uInt 1) (uInt 2)).
Abort.

Fixpoint repr_uterm h (t : uterm) : M btree :=
  if h is h.+1 then
    match t with
    | uInt n => Ret (btInt n)
    | uNode t1 t2 =>
        do bt1 <- repr_uterm h t1;
        do bt2 <- repr_uterm h t2;
        Ret (btNode bt1 bt2)
    | uLink r =>
        do v <- uget r;
        match v with
        | uVar n => Ret (btVar n)
        | uTerm u => repr_uterm h u
        end
    end
  else fail.

Definition represents' (m : M uterm) (bt : btree) :=
  exists h, m >>= repr_uterm h = m >> Ret bt.

Definition represents2 (m : M uterm) (bt : btree) :=
  exists h, m >>= repr_uterm h >>= (fun x => guard (x == bt)) = m >> Ret tt.

Definition represents3 (m : M uterm) (bt : btree) :=
  exists h,
    m = m >>= fun u => repr_uterm h u >>= fun x => guard (x == bt) >> Ret u.

Lemma repr_btree_ok vs bt : represents' (cenv vs >>= repr_btree^~ bt) bt.
Proof.
elim: bt vs => /= [n | n | bt1 IH1 bt2 IH2] vs.
- exists 1.
  rewrite !bindA.
  rewrite -(cnewput (ml_list _) nil) -[RHS](cnewput (ml_list _) nil).
  apply: eq_bind => vars.
  set ws := nil.
  have : seq.nth None ws n = None by case n.
  elim: vs ws => /= [|a vs IH] ws Hws.
    rewrite !bindretf !bindA !cputget Hws.
    rewrite -cputchk bindA [RHS]bindA.
    apply: eq_bind => _.
    rewrite [X in _ >> X]bindA.
    under cchknewE => l Hl.
      under eq_bind do rewrite bindretf.
      rewrite bindA bindretf /uget.
      rewrite [cput _ _ >> _](cputgetC _ _ Hl).
      over.
    rewrite cnewget [X in _ = _ >> X]bindA.
    apply: cchknewE => l _.
    by rewrite bindA !bindretf.
  have [<-|na] := eqVneq n a.
    rewrite !bindA !cputget.
    under eq_bind do rewrite Hws.
    under [RHS]eq_bind do rewrite Hws.
    rewrite -cputchk !bindA !bindskipf.
    apply eq_bind => _.
    rewrite -(cnewput ml_uvar (uVar n)).
    rewrite -[in RHS](cnewput ml_uvar (uVar n)).
    apply: cgetnewE => l Hl.
    elim: vs ws {IH Hws} => /= [|b vs IH] ws.
      rewrite !bindretf !bindA !cputget.
      rewrite nth_set_nth /= eqxx !bindretf.
      by rewrite (cputgetC _ _ Hl) cputget.
    rewrite !bindA !cputget nth_set_nth /=.
    case/boolP: (b == n) => bn.
      by rewrite !bindretf IH.
    case nthb: (seq.nth None ws b) => [l'|].
      by rewrite !bindretf IH.
    rewrite !bindA -!cputnewC.
    rewrite !cputgetC 1?eq_sym // -!cputnewC.
    apply: eq_bind => _.
    apply: eq_bind => _.
    apply: eq_bind => r.
    rewrite -[cput vars _ >> _]bindA cputput.
    rewrite -[cput vars _ >> (cput _ _ >> _)]bindA cputput.
    rewrite (_ : set_nth _ _ _ _ =
                 set_nth None (set_nth None ws b (Some r)) n (Some l)).
      by rewrite IH.
    by rewrite set_set_nth eq_sym (negbTE bn).
  rewrite !bindA !cputget.
  case ntha: (seq.nth None ws a) => [l|].
    by rewrite !bindretf IH.
  rewrite !bindA.
  rewrite -!cputnewC.
  apply: eq_bind => _.
  apply: eq_bind => l.
  rewrite IH //.
  by rewrite nth_set_nth /= (negbTE na).
- exists 1. by rewrite bindA [RHS]bindA !bindretf.
- case: (IH1 vs) => h1.
Abort.

Lemma repr_btree_ok vs bt :
  exists h vs',
    cenv vs >>= repr_btree^~ bt >>= repr_uterm h = cenv (vs++vs') >> Ret bt.
Proof.
elim: bt vs => /= [n | n | bt1 IH1 bt2 IH2] vs.
- exists 1, [:: n].
  rewrite !bindA.
  rewrite -(cnewput (ml_list _) nil) -[RHS](cnewput (ml_list _) nil).
  apply: eq_bind => vars.
  set ws := nil.
  have : seq.nth None ws n = None by case n.
  elim: vs ws => [|a vs IH] ws Hws.
    rewrite !bindretf !bindA !cputget Hws.
    rewrite -cputchk bindA [RHS]bindA.
    apply: eq_bind => _.
    rewrite [X in _ >> X]bindA.
    under cchknewE => l Hl.
      under eq_bind do rewrite bindretf.
      rewrite bindA bindretf /uget.
      rewrite [cput _ _ >> _](cputgetC _ _ Hl).
      over.
    rewrite cnewget [X in _ = _ >> X]bindA.
    apply: cchknewE => l _.
    by rewrite !bindretf.
  rewrite [repr_uterm]lock /=.
  have [<-|na] := eqVneq n a.
    rewrite 4!bindA !cputget.
    under eq_bind do rewrite Hws.
    under [RHS]eq_bind do rewrite Hws.
    rewrite -cputchk !bindA !bindskipf.
    apply eq_bind => _.
    rewrite -(cnewput ml_uvar (uVar n)).
    rewrite -[in RHS](cnewput ml_uvar (uVar n)).
    apply: cgetnewE => l Hl.
    elim: vs ws {IH Hws} => /= [|b vs IH] ws.
      rewrite !bindretf !bindA !cputget.
      rewrite nth_set_nth /= eqxx !bindretf -lock.
      by rewrite (cputgetC _ _ Hl) cputget.
    rewrite !bindA !cputget nth_set_nth /=.
    case/boolP: (b == n) => bn.
      by rewrite !bindretf IH.
    case nthb: (seq.nth None ws b) => [l'|].
      by rewrite !bindretf IH.
    rewrite !bindA -!cputnewC.
    rewrite !cputgetC 1?eq_sym // -!cputnewC.
    apply: eq_bind => _.
    apply: eq_bind => _.
    apply: eq_bind => r.
    rewrite -[cput vars _ >> (cput _ _ >> _)]bindA cputput.
    rewrite (_ : set_nth _ _ _ _ =
                 set_nth None (set_nth None ws b (Some r)) n (Some l)).
      by rewrite IH -[cput vars _ >> (cput _ _ >> _)]bindA cputput.
    by rewrite set_set_nth eq_sym (negbTE bn).
  rewrite !bindA !cputget.
  case ntha: (seq.nth None ws a) => [l|].
    by rewrite -lock !bindretf IH.
  rewrite !bindA.
  rewrite -!cputnewC.
  apply: eq_bind => _.
  apply: eq_bind => l.
  rewrite -lock IH //.
  by rewrite nth_set_nth /= (negbTE na).
- exists 1, nil. by rewrite bindA bindretf cats0.
- case: (IH1 vs) => h1 [vs1] {}IH1.
  case: (IH2 (vs++vs1)) => h2 [vs2] {}IH2.
  exists (maxn h1 h2).+1, (vs1++vs2).
Abort.

Fixpoint expand_head (h : nat) (t : uterm) :=
  if h is h.+1 then
    if t is uLink v then
      do vt <- uget v;
      if vt is uTerm t' then expand_head h t' else Ret t
    else Ret t
  else fail.

Fixpoint occurs_ref h (v : loc ml_uvar) t :=
  if h is h.+1 then
    match t with
    | uLink w =>
        if loc_id v == loc_id w then fail else
        do wt <- uget w;
        if wt is uTerm t' then occurs_ref h v t' else Ret tt
    | uInt _ => Ret tt
    | uNode t1 t2 =>
        do _ <- occurs_ref h v t1;
        occurs_ref h v t2
    end
  else fail.

Fixpoint unify (h : nat) (l : constr_list) : M unit :=
  if h is h.+1 then
    if l is (t1, t2) :: l' then
      do t1 <- expand_head h t1;
      do t2 <- expand_head h t2;
      match t1, t2 with
      | uInt m, uInt n =>
          if m == n then unify h l' else fail
      | uNode tl1 tl2, uNode tr1 tr2 =>
          unify h ((tl1, tr1) :: (tl2, tr2) :: l')
      | uLink v1, uLink v2 =>
          if loc_id v1 == loc_id v2 then unify h l'
          else uset v1 (uTerm t2) >> unify h l'
      | uLink v1, _ =>
          do _ <- occurs_ref h v1 t2;
          uset v1 (uTerm t2) >> unify h l'
      | _, uLink v2 =>
          do _ <- occurs_ref h v2 t1;
          uset v2 (uTerm t1) >> unify h l'
      | _, _ => fail
      end
    else Ret tt
else fail.

End unify.
End Unification.

End CoqTypeNat.
