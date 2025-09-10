(* Require Import ZArith. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib fail_lib.
Require Import action_monad action_model unif_actionrun.
Require Import monad_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Arguments loc [ml_type locT].

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
| uLink : @loc _ nat ml_uvar -> uterm
| uInt : nat -> uterm
| uNode : uterm -> uterm -> uterm.

Inductive uvar : Type :=
| uVar : nat -> uvar
| uTerm : uterm -> uvar.

Definition ml_type_eq_mixin := hasDecEq.Build _ (comparePc MLTypes.ml_type_eq_dec).
HB.instance Definition ml_type_eqType := ml_type_eq_mixin.

Definition loc_eq_dec (T : ml_type) (l1 l2 : @loc _ nat T) : decidable (l1=l2).
case: T/ l1 l2 => T n.
case: T/ => T m. Search nat "eq" "dec".
have [-> | /eqP nm] := eqVneq n m.
  by left.
by right; case.
Qed.
Lemma loc_eqP T : Equality.axiom (@loc_eq_dec T).
Proof. by move=> x y; case: loc_eq_dec => xy; constructor. Qed.
HB.instance Definition _ T := hasDecEq.Build _ (@loc_eqP T).

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
  | ml_ref T1 => @loc _ nat T1
  | ml_uvar => uvar
  | ml_uterm => uterm
  end.
End with_monad.

HB.instance Definition _ := @isML_universe.Build ml_type coq_type_nat ml_unit val_nonempty.

Definition typedStoreFailRunMonad (N : monad) :=
  typedStoreFailRunMonad ml_type N nat.

Definition typedStoreMonad (N : monad) :=
  typedStoreMonad ml_type N nat.

(* ======== *)

Section Unification.

Variables (N : monad) (M : typedStoreFailRunMonad N).
Local Notation coq_type := hierarchy.coq_type.
Local Open Scope do_notation.

Local Notation foldM := (foldr (fun m1 m2 => m1 >> m2)).

Lemma foldr_bindA A B (s : seq (M A)) (m : M B) :
  foldM m s = foldM skip s >> m.
Proof.
elim: s => /= [|m1 s IH].
  by rewrite bindskipf.
by rewrite IH bindA.
Qed.

Section Definitions.
Definition constr_list : Type := list (uterm * uterm)%type.

Fixpoint free_vars bt :=
  match bt with
  | btVar n => [:: n]
  | btInt _ => [::]
  | btNode bt1 bt2 => free_vars bt1 ++ free_vars bt2
  end.
End Definitions.

Section monad_lemmas.

Lemma bindifsomeret (A B : UU0) (a : option A) (m : M A) (g : A -> M B) :
  (if a is Some a then Ret a else m) >>= g =
  if a is Some a then g a else m >>= g.
Proof. case: a => // ?. by rewrite bindretf. Qed.

Lemma matchifsomebool (A B : UU0) (a : option A) (m m' : M B) (f : A -> M B) :
  (if a is Some a then f a else m) =
  if isSome a then (if a is Some a then f a else m') else m.
Proof. by case: a. Qed.

Lemma bindmskipf (A B : UU0) (m : M A) (m' : M B) :
  m >> skip >> m' = m >> m'.
Proof. by rewrite bindA bindskipf. Qed.

Lemma cgetputk T A (r : loc T) (k : _ -> M A) :
  cget r >>= (fun x => cput r x >> k x) = cget r >>= k.
Proof.
symmetry.
rewrite -(cgetget _ r _ (fun _ x => k x)).
rewrite -[X in _ >> X]bindskipf -bindA -cgetputskip bindA.
apply: eq_bind => x.
by rewrite cputget.
Qed.

End monad_lemmas.

Section repr.

Variable vars_loc : @loc _ nat (ml_list (ml_option (ml_ref ml_uvar))).
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

Lemma add_var_skipE A n (m : M A) : add_var_skip n >> m = add_var n >> m.
Proof.
rewrite !bindA.
apply: eq_bind => vars.
case Hnth: (nth None vars n) => [l|] /=.
  by rewrite !bindretf.
rewrite !bindA.
by under [RHS]eq_bind do rewrite bindA bindretf.
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

Check foldM.

Fixpoint repr_btree_list (l : list btree) : M (list uterm) :=
  match l with
  | nil => Ret nil
  | bt :: r =>
    do t <- repr_btree bt;
    do r' <- repr_btree_list r;
    Ret (t :: r')
  end.

Definition repr_btree_pairs (l : list (btree * btree)) : M (list (uterm * uterm)) :=
  do l1 <- repr_btree_list (unzip1 l);
  do l2 <- repr_btree_list (unzip2 l);
  Ret (zip l1 l2).

(*
Lemma repr_btree_list_cons A bt l (k : _ -> M A) :
  repr_btree_list (bt :: l) >>= k =
  do t <- repr_btree bt;
  do l' <- repr_btree_list l;
  k (t :: l').
Proof.
under [RHS]eq_bind => t.
  under eq_bind => l'.
    rewrite -bindretf.
  over. rewrite -bindA.
over. by rewrite bindA.
Qed.
*)

Lemma repr_btree_cons A bt1 bt2 l (k : _ -> M A) :
  repr_btree_pairs ((bt1, bt2) :: l) >>= k =
  do t1 <- repr_btree bt1;
  do l1 <- repr_btree_list (unzip1 l);
  do t2 <- repr_btree bt2;
  do l2 <- repr_btree_list (unzip2 l);
  k ((t1, t2) :: (zip l1 l2)).
Proof.
rewrite bindA /= bindA.
apply: eq_bind => t1.
rewrite bindA.
apply: eq_bind => l1.
rewrite bindretf 2!bindA.
apply: eq_bind => t2.
rewrite bindA.
apply: eq_bind => l2.
by rewrite 2!bindretf.
Qed.

Lemma repr_btree_pairs_zip A l (k : _ -> M A) :
  repr_btree_pairs l >>= k =
  do l1 <- repr_btree_list (unzip1 l);
  do l2 <- repr_btree_list (unzip2 l);
  k (zip l1 l2).
Proof.
rewrite bindA.
apply: eq_bind => ?.
rewrite bindA.
apply: eq_bind => ?.
by rewrite bindretf.
Qed.

Lemma repr_btree_node A bt1 bt2 (k : _ -> M A) :
  (do t1 <- repr_btree bt1; do t2 <- repr_btree bt2; Ret (uNode t1 t2)) >>= k =
  do t1 <- repr_btree bt1; do t2 <- repr_btree bt2; k (uNode t1 t2).
Proof.
rewrite bindA.
apply: eq_bind => ?.
rewrite bindA.
apply: eq_bind => ?.
by rewrite bindretf.
Qed.

End repr.

Section add_vars.

Definition add_vars vs r :=
  foldr (fun n m => add_var_skip r n >> m) (Ret r) vs.

Lemma add_varD A r n (k : _ -> _ -> M A) :
  add_var r n >>= (fun v => add_var r n >>= k v) =
  add_var r n >>= fun v => k v v.
Proof.
rewrite !bindA.
rewrite -[LHS]cgetputk -[RHS]cgetputk.
apply: eq_bind => vars.
case Hnth: nth => [v|].
  by rewrite !bindretf !bindA cputget Hnth bindretf.
rewrite !bindA.
apply: eq_bind => _.
apply: eq_bind => v.
by rewrite !bindA bindretf bindA cputget nth_set_nth /= eqxx !bindretf.
Qed.

Lemma add_varC_present A (r : loc (ml_list (ml_option (ml_ref ml_uvar))))
      vars m n (k : _ -> _ -> M A) :
  nth None vars n ->
  cput r vars >> (add_var r n >>= fun v => add_var r m >>= k v) =
  cput r vars >> (add_var r m >>= fun w => add_var r n >>= k ^~ w).
Proof.
move=> Hn.
rewrite bindA [in RHS]bindA !cputget.
case Hnth: nth Hn => [v|] // _.
rewrite bindretf bindA cputget.
case Hnth': nth => [v'|] /=.
  by rewrite !bindretf bindA cputget Hnth bindretf.
apply: eq_bind => _.
rewrite 2!bindA.
apply: eq_bind => v'.
rewrite !bindA !bindretf bindA cputget nth_set_nth /=.
case: ifPn => nm.
  by rewrite (eqP nm) Hnth' in Hnth.
by rewrite Hnth bindretf.
Qed.

Lemma add_varC A (r : loc (ml_list (ml_option (ml_ref ml_uvar))))
      m n (k : _ -> _ -> M A) :
  add_var r n >>= (fun v => add_var r m >>= k v) =
  add_var r n >> (add_var r m >>= fun w => add_var r n >>= k ^~ w).
Proof.
rewrite -[LHS](add_varD r n (fun _ _ => _ >>= _)).
rewrite {1 4}/add_var.
rewrite -cgetputk bindA [in RHS]bindA.
apply: eq_bind => vars.
rewrite bindA [RHS]bindA.
case Hnth: nth => [v|].
  by rewrite !bindretf add_varC_present ?Hnth.
rewrite bindA [in RHS]bindA.
apply: eq_bind => _.
apply: eq_bind => v.
rewrite bindA [in RHS]bindA !bindretf.
by rewrite -[RHS]add_varC_present // nth_set_nth /= eqxx.
Qed.

Lemma add_varsC A r n s (k : _ -> M A) :
  (do v <- add_var r n; add_vars s r >> k v) =
  add_var r n >> (add_vars s r >> (add_var r n >>= k)).
Proof.
elim: s => [|m s IH] /=.
  rewrite bindretf add_varD.
  by under eq_bind do rewrite bindretf.
rewrite add_var_skipE bindA add_varC -IH -add_varC.
by under eq_bind do rewrite bindA.
Qed.

Lemma add_vars_ret r vs : add_vars vs r >> Ret r = add_vars vs r.
Proof. elim: vs => /= [|n vs IH]; by [rewrite bindretf | rewrite bindA IH]. Qed.

Lemma add_vars_cat r vs1 vs2 :
  add_vars (vs1 ++ vs2) r = add_vars vs1 r >> add_vars vs2 r.
Proof. elim: vs1 => /= [|n vs IH]; by [rewrite bindretf|rewrite bindA IH]. Qed.

End add_vars.

Section cenv.

Definition cenv (vs : list nat) :=
  do vars <- cnew (ml_list (ml_option (ml_ref ml_uvar))) nil;
  foldr (fun n m => add_var_skip vars n >> m) (Ret vars) vs.

Lemma cenv_cat vs1 vs2 : cenv (vs1 ++ vs2) = cenv vs1 >>= add_vars vs2.
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

Lemma crunenvadd n vs :
  crun (cenv vs) ->
  crun (do r <- cenv vs;
        do vars <- cget r;
        do l <- cnew ml_uvar (uVar n);
        cput r (set_nth None vars n (Some l))).
Proof.
move => H.
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
  rewrite -(bindretf r (fun=>skip)) -(bindskipf (Ret r)) -!bindA -cchkE.
by rewrite -(bindA (cenv vs)) crunmskip cenv_chk.
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
            -!bindA -cchkE.
  by rewrite -bindA crunmskip cenv_chk.
exact: crunenvadd.
Qed.

Section vars_loc.
Definition vars_loc_spec : {r | crun (cenv [::]) = Some r}.
have := crunenv [::].
case: (crun _) => [r|] // _.
by exists r.
Defined.

Definition vars_loc := proj1_sig vars_loc_spec.

Lemma eq_crunenv vs : crun (cenv vs) = Some vars_loc.
Proof.
elim/last_ind: vs => //= [|vs n IH].
  by rewrite (proj2_sig vars_loc_spec).
rewrite -cats1 cenv_cat (crunbind _ _ vars_loc) //=.
rewrite -bindA crunret //. 
rewrite -(crunbind _ _ vars_loc _ (fun r => add_var_skip r n)) //.
rewrite -crunmskip bindA.
under eq_bind => r' do rewrite -(bindretf r' (fun=>skip)) -bindA.
by rewrite -bindA crunmskip -(cenv_cat vs [::n]) crunenv.
Qed.
End vars_loc.

Lemma cenv_var A vs n (k' : _ -> _ -> M A) :
  n \in vs ->
  cenv vs >>= (fun r => add_var r n >>= cget (T:=_) >>= k' r) =
  cenv vs >>= k' ^~ (uVar n).
Proof.
  move => Hin.
  under eq_bind do (rewrite !bindA; under eq_bind do rewrite bindifsomeret).
  under eq_bind do rewrite -[_ >> _]bindmret bindA.
  rewrite !bindA /= -(cnewput (ml_list _) nil) -[RHS](cnewput (ml_list _) nil).
  apply: eq_bind => vars.
  set ws := nil.
  move: Hin.
  have : seq.nth None ws n = None by case n.
  elim: vs ws => /= [//|a vs IH] ws Hws.
  rewrite in_cons. 
  case/boolP : (n == a) => [/eqP <- _|na Hin].
    rewrite !bindA !cputget.
    under eq_bind do rewrite Hws.
    under [RHS]eq_bind do rewrite Hws.
    rewrite -cputchk cchkE !bindA !bindskipf.
    apply eq_bind => _.
    rewrite -(cnewput ml_uvar (uVar n)).
    rewrite -[in RHS](cnewput ml_uvar (uVar n)).
    apply: cgetnewE => l Hl.
    elim: vs ws {IH Hws} => /= [|b vs IH] ws.
      rewrite !bindretf !cputget nth_set_nth /= eqxx bindA cputgetC // cputget.
      by rewrite bindmret.
    rewrite !bindA !cputget nth_set_nth /=.
    case/boolP : (b == n) => bn.
      by rewrite !bindretf IH.
    case nthb: (seq.nth None ws b) => [l'|].
      by rewrite !bindretf IH.
    rewrite !bindA -!cputnewC !cputgetC 1?eq_sym // -!cputnewC.
    apply: eq_bind => _.
    apply: eq_bind => _.
    apply: eq_bind => r.
    rewrite -2![cput vars _ >> (cput _ _ >> _)]bindA cputput.
    rewrite (_ : set_nth _ _ _ _ =
                 set_nth None (set_nth None ws b (Some r)) n (Some l)).
      by rewrite IH.
    by rewrite set_set_nth eq_sym (negbTE bn).
  rewrite !bindA !cputget.
  case ntha: (seq.nth None ws a) => [l|].
    by rewrite !bindretf IH.
  rewrite !bindA -!cputnewC.
  apply: eq_bind => _.
  apply: eq_bind => l.
  rewrite IH //.
  by rewrite nth_set_nth /= (negbTE na).
Qed.

End cenv.

Section represents.

Inductive represents : M uterm -> btree -> Prop :=
| RVar (m : M uterm) v (n : nat) :
  crun m = Some (uLink v) ->
  crun (m >> cget v) = Some (uVar n) ->
  represents m (btVar n)
| RInt (m : M uterm) (n : nat) :
  crun m = Some (uInt n) ->
  represents m (btInt n)
| RNode (m : M uterm) u1 u2 bt1 bt2 :
  crun m = Some (uNode u1 u2) ->
  represents (m >> Ret u1) bt1 ->
  represents (m >> Ret u2) bt2 ->
  represents m (btNode bt1 bt2)
| RLink (m : M uterm) (v : loc ml_uvar) (u : uterm) (bt : btree) :
  crun m = Some (uLink v) ->
  crun (m >> cget v) = Some (uTerm u) ->
  represents (m >> Ret u) bt ->
  represents m bt.

Lemma represents_run m bt :
  represents m bt ->
  exists2 u, crun m = Some u & represents (m >> Ret u) bt.
Proof.
elim: bt / => {}m.
- move=> v n Hm Hv.
  exists (uLink v) => //.
  apply (@RVar _ v n).
    by rewrite crunret // Hm.
  by rewrite bindA bindretf.
- move=> n Hm.
  exists (uInt n) => //.
  constructor.
  by rewrite crunret // Hm.
- move=> u1 u2 bt1 bt2 Hm Hu1 IHu1 Hu2 IHu2.
  exists (uNode u1 u2) => //.
  apply: (@RNode _ u1 u2).
      by rewrite crunret // Hm.
    by rewrite bindA bindretf.
  by rewrite bindA bindretf.
- move=> v u bt Hm Hv Hu.
  exists (uLink v) => //.
  apply (@RLink _ v u).
      by rewrite crunret // Hm.
    by rewrite bindA bindretf.
  by rewrite bindA bindretf.
Qed.

Lemma cenv_repr_k (A : UU0) vs bt (k : _ -> M A) :
    cenv vs >>= (fun x => repr_btree x bt >> k x) =
    cenv (vs ++ free_vars bt) >>= k.
Proof.
elim: bt vs k => [v | n | bt1 IH1 bt2 IH2 /=] vs k.
- rewrite /cenv /= bindA.
  under eq_bind => vars.
    under eq_bind => x.
      rewrite bindA.
      under eq_bind do rewrite bindretf.
      rewrite -add_var_skipE.
    over.
  over.
  rewrite !bindA.
  apply eq_bind => vars /=.
  rewrite cats1 foldr_rcons.
  elim: vs => /= [|a vs IH].
    by rewrite [RHS]bindA 2!bindretf.
  by rewrite bindA [RHS]bindA IH.
- under eq_bind do rewrite bindretf.
  by rewrite cats0.
- under eq_bind => x.
    rewrite bindA.
    under eq_bind => u1.
      rewrite bindA.
      under eq_bind do rewrite bindretf.
    over.
  over.
  by rewrite IH1 IH2 catA.
Qed.

Lemma equiv_run_represents (m1 m2 : M uterm) bt :
  (forall (A : UU0) (k : uterm -> M A), crun (m1 >>= k) = crun (m2 >>= k)) ->
  represents m1 bt -> represents m2 bt.
Proof.
move=> Heq Hrepr.
elim: bt/ Hrepr m2 Heq => {}m1.
- move=> v n Hv Hn m2 Heq.
  apply: (@RVar _ v n).
    by rewrite -(bindmret m2) -Heq bindmret.
  by rewrite -Heq.
- move=> n Hn m2 Heq.
  constructor.
  by rewrite -(bindmret m2) -Heq bindmret.
- move=> u1 u2 bt1 bt2 Hm1 Hu1 IH1 Hu2 IH2 m2 Heq.
  apply: (@RNode _ u1 u2).
  + by rewrite -(bindmret m2) -Heq bindmret.
  + apply: IH1 => A k.
    by rewrite !bindA Heq.
  + apply: IH2 => A k.
    by rewrite !bindA Heq.
- move=> v u bt Hm1 Hget Hru IH m2 Heq.
  apply: (@RLink _ v u).
  + by rewrite -(bindmret m2) -Heq bindmret.
  + by rewrite -Heq.
  + apply: IH => A k.
    by rewrite !bindA Heq.
Qed.

Lemma repr_btree_add_vars A r bt vs (k : _ -> M A) :
  (repr_btree r bt >>= fun u => add_vars vs r >> k u)
  = add_vars (free_vars bt ++ vs) r >> (repr_btree r bt >>= k).
Proof.
elim: bt vs k => [n|n|bt1 IH1 bt2 IH2] vs k /=.
- rewrite 2!bindA /= add_var_skipE bindA -add_varsC.
  apply: eq_bind => v.
  by rewrite -[in RHS]add_vars_ret [RHS]bindA !bindretf.
- by rewrite !bindretf.
- under [RHS]eq_bind do rewrite bindA.
  rewrite -catA -IH1 bindA.
  apply: eq_bind => u1.
  rewrite bindA.
  under eq_bind do rewrite bindretf.
  rewrite IH2 bindA.
  by under [X in _ = _ >> X]eq_bind do rewrite bindretf.
Qed.

Lemma repr_btree_ok vs bt : represents (cenv vs >>= repr_btree^~ bt) bt.
Proof.
elim: bt vs => /= [n | n | bt1 IH1 bt2 IH2] vs.
- have Hrun : (crun (cenv vs >>= fun x => add_var x n)).
    rewrite -crunmskip bindA.
    under eq_bind => r.
      rewrite -add_var_skipE -[skip](bindretf r).
      rewrite -bindA.
      rewrite -/(foldr (fun n m => add_var_skip r n >> m) (Ret r) [:: n]).
      over.
    by rewrite -bindA crunmskip -cenv_cat crunenv.
  move: (Hrun).
  case Hl: (crun _) => [l|] // _.
  apply: (@RVar _ l n).
    by rewrite -bindA (crunbind _ _ l) // crunret.
  rewrite bindA.
  under eq_bind do rewrite bindA.
  under eq_bind do under eq_bind do rewrite bindretf.
  rewrite -bindA -crunbind //.
  case/boolP: (n \in vs) => Hin.
    rewrite bindA -[X in crun X]bindmret bindA.
    by rewrite cenv_var // crunret // crunenv.
  rewrite /add_var.
  under [cenv vs >> _]eq_bind => r do under eq_bind do rewrite (matchifsomebool _ _ fail).
  rewrite (cenv_get_nth _ _ (fun _ _ cond => if cond then _ else _)) (negbTE Hin).
  rewrite bindA.
  under eq_bind => r.
    rewrite bindA.
    under eq_bind => vars.
      rewrite !bindA.
      under eq_bind do rewrite bindA; under eq_bind do rewrite !bindretf.
    over.
    rewrite -cgetchk.
    under eq_bind => vars.
      under cchknewE => r2 Hr2 do rewrite -[X in _ >> X]bindmret cputgetC //.
      rewrite cnewget.
    over.
    rewrite cgetchk.
    under eq_bind do rewrite -bindA.
    rewrite -bindA.
  over.
  rewrite -bindA crunret //.
  exact/crunenvadd/crunenv.
- constructor.
  by rewrite crunret // crunenv.
- case: (represents_run (IH1 vs)) => u1 Hbt1 _.
  case: (represents_run (IH2 (vs ++ free_vars bt1))) => u2 Hbt2 _.
  apply: (@RNode _ u1 u2).
      move: (crunenv vs).
      case Hr: (crun _) => [r|] // _.
      rewrite (crunbind _ _ r) //.
      pose r' := r.
      rewrite -{1}/r' -(crunbind _ _ r' _ (fun r => repr_btree r bt1 >>= _)) //.
      rewrite -bindA {r'}.
      rewrite (crunbind _ _ u1) //.
      rewrite bindA cenv_repr_k.
      have Hr' : crun (cenv (vs ++ free_vars bt1)) = Some r.
        by rewrite -Hr !eq_crunenv.
      rewrite -bindA (crunbind _ _ u2) //.
        rewrite crunret //.
        by rewrite -(crunbind _ _ r _ (fun r => repr_btree r bt2)) // Hbt2.
      by rewrite -(crunbind _ _ r _ (fun r => repr_btree r bt2)) // Hbt2.
    apply/equiv_run_represents/(IH1 (vs ++ free_vars bt1 ++ free_vars bt2)).
    move=> a k.
    rewrite 2!bindA cenv_cat bindA.
    under eq_bind do rewrite -add_vars_ret bindA bindretf -repr_btree_add_vars.
    rewrite (crunbind _ _ vars_loc) ?eq_crunenv // [in RHS]bindA.
    rewrite [RHS](crunbind _ _ vars_loc) ?eq_crunenv //.
    rewrite bindA.
    under [X in _ = crun (_ >> X)]eq_bind => u0.
      rewrite bindA.
      under eq_bind do rewrite -bindA bindretf.
    over.
    rewrite -!bindA 2![in RHS]bindA bindretf.
    rewrite (crunbind _ _ u1); last first.
      rewrite -(crunbind _ _ vars_loc _ (fun r => repr_btree r bt1)) ?eq_crunenv //.
    rewrite bindA [in RHS]bindA.
    rewrite -(crunbind _ _ vars_loc _
      (fun r => repr_btree r bt1 >> (add_vars (free_vars bt2) r >> k u1))) ?eq_crunenv //.
    rewrite -(crunbind _ _ vars_loc _
      (fun r => repr_btree r bt1 >> (repr_btree r bt2 >> k u1))) ?eq_crunenv //.
    by rewrite !cenv_repr_k -bindA -cenv_cat.
  apply/equiv_run_represents/(IH2 (vs ++ free_vars bt1)).
  move=> a k.
  rewrite bindA [in RHS]bindA.
  rewrite (crunbind _ _ u2) ?eq_crunenv //.
  under [in RHS]eq_bind => r.
    rewrite bindA.
    under eq_bind do rewrite bindA bindretf.
    under eq_bind do under eq_bind do rewrite bindretf.
    over.
  rewrite bindA.
  by rewrite 3!cenv_repr_k.
Qed.

End represents.

Section csubst.

Definition csubst r v bt :=
  do t <- repr_btree r bt;
  add_var r v >>= fun x => cput x (uTerm t).

Definition csubst_list r s :=
  foldM skip [seq csubst r x.1 x.2 | x <- s].

Definition subst_list_back (s : substType) t : btree :=
  foldr (fun (p : var * btree) t => subst p.1 p.2 t) t s.

Fixpoint norm_subst (s : substType) :=
  match s with
  | nil => nil
  | (v, t) :: s' =>
    let ns' := norm_subst s' in
    (v, subst_list_back ns' t) :: ns'
  end.

Lemma repr_btree_subst_ok vs bt s:
  represents
    (cenv vs >>= fun x => csubst_list x s >> repr_btree x bt)
    (subst_list (norm_subst s) bt).
Proof.
move: bt.
elim: s => [|[v t] s IH /=] bt.
  under eq_bind do rewrite bindskipf.
  exact: repr_btree_ok.
rewrite /csubst_list /=.
Abort.

End csubst.

Section unify.

Fixpoint expand_head (h : nat) (t : uterm) :=
  if h is h.+1 then
    if t is uLink v then
      do vt <- (cget v : M uvar);
      if vt is uTerm t' then expand_head h t' else Ret t
    else Ret t
  else Ret t.

Fixpoint size_uterm (t : uterm) : nat :=
  if t is uNode t1 t2 then 1 + size_uterm t1 + size_uterm t2 else 1.

Definition size_pairs (l : constr_list) :=
  sumn [seq size_uterm p.1 + size_uterm p.2 | p <- l].

Section occurs_ref1.
Variable occurs_ref2 : @loc _ nat ml_uvar -> uterm -> M unit.

Definition occurs_ref_link (v w : loc ml_uvar) :=
  if loc_id v == loc_id w then fail else
    do wt <- (cget w : M uvar);
    if wt is uTerm t' then occurs_ref2 v t' else Ret tt.

Fixpoint occurs_ref1 (v : loc ml_uvar) t :=
  match t with
  | uLink w => occurs_ref_link v w
  | uInt _ => Ret tt
  | uNode t1 t2 =>
      do _ <- occurs_ref1 v t1;
      occurs_ref1 v t2
  end.
End occurs_ref1.

Fixpoint occurs_ref h (v : loc ml_uvar) t :=
  if h is h.+1 then occurs_ref1 (occurs_ref h) v t else fail.

Definition unify_link (unify1 : constr_list -> _) (v : loc ml_uvar) t l : M unit :=
  cput v (uTerm t) >> unify1 l.

Fixpoint unify1 (h he : nat) (l : constr_list) : M unit :=
  if h is h.+1 then
    if l is (t1, t2) :: l' then
      do t1 <- expand_head he t1;
      do t2 <- expand_head he t2;
      match t1, t2 with
      | uInt m, uInt n =>
          if m == n then unify1 h he l' else fail
      | uNode tl1 tl2, uNode tr1 tr2 =>
          unify1 h he ((tl1, tr1) :: (tl2, tr2) :: l')
      | uLink v1, uLink v2 =>
          if loc_id v1 == loc_id v2 then unify1 h he l'
          else unify_link (unify1 h he.+1) v1 t2 l'
      | uLink v1, _ =>
          do _ <- occurs_ref he v1 t2; unify_link (unify1 h he.+1) v1 t2 l'
      | _, uLink v2 =>
          do _ <- occurs_ref he v2 t1; unify_link (unify1 h he.+1) v2 t1 l'
      | _, _ => fail
      end
    else Ret tt
  else fail.

End unify.

Section equiv.

HB.about ExceptMonad.acto.

Local Notation N' := option_monad.

Definition M' : actionRunFailMonad op N' :=
  ActionFailMonad.acto op N'.

Local Notation bt_unify2 := (unif_actionrun.unify2 M').
Local Notation bt_unify1 := (@unif_actionrun.unify1 N' M').
Local Notation bt_size_pairs := unif_actionrun.size_pairs.

Lemma expandgetC T A h t (l : loc T) (k : _ -> _ -> M A) :
  cchk l >> (
    do t' <- expand_head h t;
    do x <- cget l;
    k t' x) =
    do x <- cget l;
    do t' <- expand_head h t;
    k t' x.
Proof.
elim: h t => [|h IHh] t /=.
  rewrite bindretf cchkget.
  by under [RHS]eq_bind do rewrite bindretf.
case: t => [l'|n|t1 t2] /=.
- rewrite ![X in cchk _ >> X]bindA.
  rewrite (cchkgetC l l').
  under [RHS]eq_bind => x do rewrite bindA.
  rewrite (cgetC _ _ l l').
  apply: eq_bind => -[n|t].
    rewrite bindretf cchkget.
    by under [RHS]eq_bind do rewrite bindretf.
  exact: IHh.
- rewrite bindretf cchkget.
  by under [RHS]eq_bind do rewrite bindretf.
- rewrite bindretf cchkget.
  by under [RHS]eq_bind do rewrite bindretf.
Qed.

Lemma expand_same A h t (k : _ -> _ -> M A) :
  do t1 <- expand_head h t;
  do t2 <- expand_head h t;
    k t1 t2 =
  do t' <- expand_head h t;
    k t' t'.
Proof.
  elim: h t => [/=|h IHh t].
    by move=> t; rewrite !bindretf.
  elim: t IHh => [l|n /=|t1 IH1 t2 IH2 /=] IHh.
  - rewrite /= bindA [RHS]bindA.
    under eq_bind => t1 do under eq_bind => t2 do rewrite bindA.
    rewrite -[LHS](cgetchk l).
    under eq_bind => s.
    have ->: forall (k : _ -> _ -> M _),
      cchk l >> (match s with
       | uVar _ => Ret (uLink l)
       | uTerm t' => expand_head h t'
       end >>= (fun t2 : uterm => cget l >>= k t2)) = 
      cget l >>= (fun x => (match s with
       | uVar _ => Ret (uLink l)
       | uTerm t' => expand_head h t'
       end >>= (fun t2 : uterm => k t2 x))).
      move: s => [n|t] T k'.
        rewrite bindretf cchkget.
        by under [RHS]eq_bind do rewrite bindretf.
      exact: expandgetC.
    over.
    rewrite cgetget.
    apply: eq_bind => -[n|//].
    by rewrite !bindretf.
  - by rewrite !bindretf.
  - by rewrite !bindretf.
Qed.

(*
Lemma repr_btree_add_vars A r bt vs (k : _ -> M A) :
  (repr_btree r bt >>= fun u => add_vars vs r >> k u)
  = add_vars (free_vars bt ++ vs) r >> (repr_btree r bt >>= k).
Proof.
elim: bt vs k => [n|n|bt1 IH1 bt2 IH2] vs k /=.
- rewrite 2!bindA /= -add_var_skipE 2!bindA bindskipf -add_varsC.
  apply: eq_bind => v.
  by rewrite -[in RHS]add_vars_ret [RHS]bindA !bindretf.
- by rewrite !bindretf.
- under [RHS]eq_bind do rewrite bindA.
  rewrite -catA -IH1 bindA.
  apply: eq_bind => u1.
  rewrite bindA.
  under eq_bind do rewrite bindretf.
  rewrite IH2 bindA.
  by under [X in _ = _ >> X]eq_bind do rewrite bindretf.
Qed.
*)

Lemma unify1_eq h1 h2 h' l :
  h1 <= h2 ->
  h1 > bt_size_pairs l ->
  h' >= size (vars_pairs l) ->
  bt_unify1 (bt_unify2 h') h1 l = bt_unify1 (bt_unify2 h') h2 l.
Proof.
move => Hle Hh1 Hh'.
rewrite -ltnS in Hh'.
have Hlf: le_fail_f (bt_unify2 h') (bt_unify2 h') by left.
case: (unify1_mono Hle Hlf l) => // H.
case Hu2: (bt_unify1 (bt_unify2 h') h2 l) => [[]|[[] s]] //.
have Hu: unifiesb_pairs s l.
  have := (@unify1_sound N' M' (bt_unify2 h') h2 l).
  rewrite /= /runActionT /= Hu2 => Ha.
  have Ha' l' : always (fun x => unifiesb_pairs x.2 l') (bt_unify2 h' l')
    by apply: (unify2_sound M').
  move: (Ha Ha').
  rewrite /always bindretf assertE.
  by case: (unifiesb_pairs s l).
case: (unify2_complete M' Hh' Hu) => /= x [].
rewrite -addn1 in Hh1.
case: (unify1_mono Hh1 Hlf l) => -> //.
by rewrite H.
Qed.

Lemma size_tree_gt0 bt : size_tree bt > 0.
Proof. by case: bt. Qed.

Section vars_defs.
Variable vars_loc : @loc _ nat (ml_list (ml_option (ml_ref ml_uvar))).

Definition loc_id_vars := pmap (omap (@loc_id _ nat ml_uvar)).
Definition vars_loc_uniq vars := uniq (loc_id vars_loc :: loc_id_vars vars).

Definition cchkvars (vars : seq (option (loc ml_uvar))) : M unit :=
  foldM skip [seq if o is Some v then cchk v else skip | o <- vars].

Definition has_vars vs : M _ :=
  do vars <- cget vars_loc;
  cchkvars vars >> guard (all (nth None vars) vs && vars_loc_uniq vars).       
End vars_defs.

Lemma guardC b (m : M unit) : guard b >> m = m >> guard b.
Proof.
by case: b; rewrite (guardT,guardF) !(bindskipf,bindmskip,bindfailf,bindmfail).
Qed.

Lemma has_vars_undup r vs : has_vars r vs = has_vars r (rev (undup (rev vs))).
Proof. by apply: eq_bind => vars; rewrite all_rev all_undup all_rev. Qed.

Lemma cput_cchkvarsC (T : ml_type) vars (r : loc T) (x : coq_type N T) :
  cput r x >> cchkvars vars = cchkvars vars >> cput r x.
Proof.
elim: vars => [|v vars IH].
  by rewrite bindmskip bindskipf.
rewrite /cchkvars /= -bindA.
case: v => [v|].
  by rewrite -cchkputC bindA IH [RHS]bindA.
by rewrite bindmskip bindskipf.
Qed.

Lemma cget_cchkvarsC A (T : ml_type) vars (r : loc T) (k : _ -> M A) :
  cget r >>= (fun a => cchkvars vars >> k a) =
  cchkvars vars >> (cget r >>= k).
Proof.
elim: vars => [|v vars IH].
  by rewrite !bindskipf; under eq_bind do rewrite bindskipf.
rewrite /cchkvars /= -bindA.
case: v => [v|].
  under eq_bind do rewrite bindA.
  by rewrite -cchkgetC IH 2![RHS]bindA.
by rewrite !bindskipf [RHS]bindA.
Qed.

Corollary cchk_cchkvarsC T (r : loc T) vars :
  cchk r >> cchkvars vars = cchkvars vars >> cchk r.
Proof.
by rewrite cchkE -cget_cchkvarsC bindmskip -[X in _ = _ >> X]bindskipf bindA.
Qed.

Lemma cnew_cchkvarsC A (T : ml_type) (x : coq_type N T) vars (k : _ -> M A) :
  do r <- cnew T x;
  cchkvars vars >> (guard (loc_id r \notin loc_id_vars vars) >> k r) =
  cchkvars vars >> (cnew T x >>= k).
Proof.
elim: vars k => [|v vars IH] k.
  by rewrite !bindskipf; under eq_bind do rewrite in_nil guardT !bindskipf.
rewrite /cchkvars /= -bindA.
case: v => [v|].
  rewrite cchkE !bindA !bindskipf cget_cchkvarsC -cnewgetC -IH.
  apply: eq_bind => r.
  rewrite bindA cget_cchkvarsC -[in RHS](bindA (guard _)) -guard_and.
  rewrite -[in RHS](bindA (guard _)) [in RHS]guardsC; last exact: bindmfail.
  apply eq_bind => _.
  rewrite bindA.
  apply: eq_bind => y.
  by rewrite assertE bindA bindretf /= andbC in_cons negb_or eq_sym.
by rewrite !bindskipf IH bindA.
Qed.

Lemma cchkvarsD vars : cchkvars vars >> cchkvars vars = cchkvars vars.
Proof.
rewrite /cchkvars.
elim: vars => [|[v|] vars IH] /=.
- by rewrite bindskipf.
- by rewrite cchkE bindA bindskipf bindA -cget_cchkvarsC IH (cgetget _ v).
- by rewrite !bindskipf.
Qed.

Lemma has_varsE r vs :
  has_vars r vs =
  do vars <- cget r;
  guard (all (fun n => nth None vars n) vs && vars_loc_uniq r vars) >>
  cchkvars vars >> cput r vars.
Proof.
rewrite /has_vars -(cgetputk r).
apply: eq_bind => vars.
by rewrite -![LHS]bindA -guardC cput_cchkvarsC bindA.
Qed.

Lemma has_varsD r vs :
  has_vars r vs >> has_vars r vs = has_vars r vs.
Proof.
rewrite has_varsE bindA.
apply: eq_bind => vars.
rewrite !bindA cputget bindA -2![X in _ >> X]bindA -guardC !bindA.
rewrite -[LHS]bindA -guard_and andbb -(bindA (cput _ _)) cput_cchkvarsC.
by rewrite bindA cputput -(bindA (cchkvars _)) cchkvarsD.
Qed.

Lemma cchkvars_set_nth vars v x :
  nth None vars v = None ->
  cchkvars (set_nth None vars v (Some x)) = cchk x >> cchkvars vars.
Proof.
elim: vars v => /= [|v vars IH] n.
  rewrite bindmskip.
  have -> // : cchkvars (set_nth None [::] n (Some x)) = cchk x.
  rewrite /cchkvars /=.
  elim: n => /= [|n IH].
    by rewrite bindmskip.
  rewrite bindskipf; by case: n IH.
rewrite /cchkvars /=.
case: n => //= [->|n]; first by rewrite bindskipf.
case: v => [v|] /= /IH {}IH; rewrite [X in _ >> X]IH ?bindskipf //.
by rewrite -bindA cchkC bindA.
Qed.

Lemma loc_id_vars_set_nth vars v x :
  nth None vars v = None ->
  loc_id_vars (set_nth None vars v (Some x)) =
  loc_id_vars (take v vars) ++ [:: loc_id x] ++ loc_id_vars (drop v vars).
Proof.
rewrite set_nthE => Hnth.
case: ifPn => Hv.
  by rewrite /loc_id_vars pmap_cat (drop_nth None Hv) Hnth.
rewrite -leqNgt in Hv.
rewrite take_oversize // drop_oversize //= /loc_id_vars pmap_cat.
have H n s : loc_id_vars (ncons n None s) = loc_id_vars s by elim: n.
by rewrite [X in _ ++ X](H (v - size vars) [:: Some x]).
Qed.

Lemma mem_loc_id_vars r vars :
  Some r \in vars -> loc_id r \in loc_id_vars vars.
Proof. by rewrite mem_pmap => /(map_f (omap (@loc_id _ _ ml_uvar))). Qed.

Lemma loc_id_vars_cat s1 s2 :
  loc_id_vars (s1 ++ s2) = loc_id_vars s1 ++ loc_id_vars s2.
Proof. exact: pmap_cat. Qed.

Lemma has_vars_add_var A r vs v (k : _ -> M A) :
  has_vars r vs >> (add_var r v >>= k) =
  has_vars r vs >> do l <- add_var r v; has_vars r (rcons vs v) >> k l.
Proof.
rewrite has_varsE 3!bindA.
apply: eq_bind => vars.
rewrite !bindA !cputget.
apply: bind_ext_guard => /andP[Hvs Hu].
case Hnth: nth => [v'|].
  rewrite !bindretf has_varsE bindA cputget Hu all_rcons Hnth Hvs guardT.
  rewrite bindskipf bindA -[in RHS](bindA (cput _ _)) cput_cchkvarsC.
  by rewrite !bindA -[RHS]bindA cchkvarsD -[in RHS](bindA (cput _ _)) cputput.
rewrite -[in LHS]cchkvarsD bindA -[X in _ >> X]bindA -cput_cchkvarsC bindA.
rewrite bindA -cnew_cchkvarsC bindA -cnewchk.
apply: eq_bind => _.
rewrite -2!cnewputC.
apply: eq_bind => x.
rewrite -(bindA (cchk x)) -(cchkvars_set_nth _ Hnth).
apply: bind_ext_guard => rx.
rewrite !bindA !bindretf -(bindA (guard _)) guardC !bindA.
apply: eq_bind => _.
rewrite -[LHS]bindA -cput_cchkvarsC bindA cputget !bindA.
rewrite -[LHS]bindA -[RHS]bindA.
apply: eq_bind => _.
rewrite all_rcons nth_set_nth /= eqxx /=.
case: allP => /=; last first.
  elim => n Hn; move/allP/(_ _ Hn): Hvs.
  by rewrite nth_set_nth /=; case: ifPn.
move=> _; congr (guard _ >> _).
rewrite /vars_loc_uniq loc_id_vars_set_nth //.
rewrite [[:: _]]lock /= uniq_catCA !mem_cat -{1}lock /= mem_seq1.
rewrite (negbTE rx) /= -mem_cat /loc_id_vars -pmap_cat cat_take_drop.
by rewrite -/loc_id_vars -lock /= andbCA [X in _ && X]Hu andbT.
Qed.

Lemma cenv_has_vars A vs (k : _ -> M A) :
  cenv vs >>= k = do r <- cenv vs; has_vars r vs >> k r.
Proof.
elim/last_ind: vs k => [|vs v IH] k.
  rewrite !bindA /=.
  under [RHS]eq_bind do rewrite bindretf bindA.
  rewrite cnewget /=.
  apply: eq_bind => r.
  by rewrite !bindretf.
rewrite -cats1 cenv_cat bindA IH.
rewrite [RHS]bindA [RHS]IH.
apply: eq_bind => r.
rewrite /= add_var_skipE [X in _ >> X]bindA [X in _ = _ >> X]bindA !bindretf.
by rewrite has_vars_add_var cats1.
Qed.

Lemma mem_nth_some (A : eqType) v vars (a : A) :
  nth None vars v = Some a -> Some a \in vars.
Proof.
move=> /[dup] H <-.
rewrite mem_nth // ltnNge.
apply/negP => Hsz.
by rewrite nth_default in H.
Qed.

Lemma add_var_cgetC A r vs v (k : _ -> _ -> M A) :
  v \in vs ->
  has_vars r vs >> (add_var r v >>= (fun l => cget l >>= k l)) =
  has_vars r vs >>
    (add_var r v >>= cget (T:=_) >>= fun u => add_var r v >>= k ^~ u).
Proof.
move=> Hv.
rewrite has_varsE [LHS]bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 4!bindA 2![in RHS]bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
apply: eq_bind => _.
rewrite 2!bindA !cputget.
move/allP/(_ v Hv): Hvars.
case Hnth: nth => [l|] // _.
rewrite !bindretf.
have lr: loc_id r != loc_id l.
  case/andP: Hu => Hr _.
  apply: contra Hr => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite !cputgetC //.
apply: eq_bind => u.
by rewrite bindA cputget Hnth bindretf.
Qed.

Lemma get_varD A r vs v (k : _ -> _ -> _ -> _ -> M A) :
  v \in vs ->
  has_vars r vs >> (do l <- add_var r v;
                    do u <- cget l; k l l u u) =
  has_vars r vs >>
    (do l <- add_var r v; do u <- cget l;
     do l' <- add_var r v; do u' <- cget l'; k l l' u u').
Proof.
move=> Hv.
rewrite has_varsE [LHS]bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 4!bindA 2![in RHS]bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
apply: eq_bind => _.
rewrite bindA !cputget.
move/allP/(_ v Hv): Hvars.
case Hnth: nth => [l|] // _.
rewrite !bindretf -(cgetputk l) -[in RHS](cgetputk l).
have lr: loc_id r != loc_id l.
  case/andP: Hu => Hr _.
  apply: contra Hr => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite !cputgetC //.
apply: eq_bind => u.
by rewrite bindA cputgetC 1?eq_sym // cputget Hnth bindretf cputget.
Qed.

Lemma cenv_add_var_get A vs v (k : _ -> _ -> _ -> M A) :
  do r <- cenv vs; add_var r v >>= (fun l => cget l >>= k r l) =
  do r <- cenv vs; add_var r v >>= k r ^~ (uVar v).
Proof.
have := cenv_cat vs [:: v].
rewrite /add_vars /=.
under eq_bind do rewrite add_var_skipE.
move => Hv.
under eq_bind => r.
  rewrite -(add_varD _ _ (fun _ l => _ >>= _)).
  rewrite -[X in _ >> X](bindretf r (fun r => _ >>= _)) -bindA; over.
rewrite -bindA -Hv.
transitivity (do r <- cenv (vs ++ [::v]) ; add_var r v >>= cget (T:=_) >>= fun u => add_var r v >>= k r ^~ u).
  rewrite [LHS]cenv_has_vars [RHS]cenv_has_vars.
  apply: eq_bind => r.
  by rewrite add_var_cgetC // mem_cat inE eqxx orbT.
rewrite cenv_var; last by rewrite mem_cat inE eqxx orbT.
rewrite cenv_cat bindA.
apply: eq_bind => r.
by rewrite /= bindA bindretf add_var_skipE add_varD.
Qed.

Lemma nth_none_ltn A (s : seq (option A)) i a :
  nth None s i = Some a -> i < size s.
Proof. by case/boolP: (i < _) => // H; rewrite nth_default // leqNgt. Qed.

Lemma uniq_loc_vars_some (vars : seq (option (loc ml_uvar))) i j v v' :
  uniq (loc_id_vars vars) ->
  nth None vars i = Some v ->
  nth None vars j = Some v' ->
  i != j -> loc_id v != loc_id v'.
Proof.
move=> Hu.
wlog: i j v v' / i < j.
  move=> H Hi Hj.
  rewrite neq_ltn => /orP[] ltij.
    by rewrite (H i j) // neq_ltn ltij.
  by rewrite eq_sym (H j i) // neq_ltn ltij.
elim: vars Hu i j => [|a vars IH] /=.
  by move=> _ i j _; rewrite nth_default.
move=> Hu [|i] [|j] //.
  rewrite nth0 /= => [] <- Hi Hj.
  move: Hu; rewrite Hi /= => /andP[] Ha Hu _.
  apply: contra Ha => /eqP ->.
  have Hv' : Some v' \in vars by rewrite -Hj mem_nth // (nth_none_ltn Hj).
  rewrite (mem_pmap (omap(loc_id (locT:=nat)))).
  exact: (map_f (omap(loc_id (locT:=nat))) Hv').
rewrite ltnS /= eqSS; apply: IH.
by case: a Hu => //= a /andP[].
Qed.

Lemma has_vars_repr_btreeC A r vs t (k : _ -> M A) :
  has_vars r vs >> (repr_btree r t >>= k) =
  has_vars r vs >>
    (repr_btree r t >>= fun u => has_vars r (vs ++ free_vars t) >> k u).
Proof.
elim: t vs k => [u|n|t1 IH1 t2 IH2] /= vs k.
- rewrite bindA has_vars_add_var bindA.
  apply: eq_bind => _.
  apply: eq_bind => l.
  by rewrite !bindretf cats1.
- by rewrite !bindretf cats0 -[RHS]bindA has_varsD.
- rewrite bindA IH1 [in RHS]bindA [in RHS]IH1.
  apply: eq_bind => _.
  apply: eq_bind => u1.
  rewrite bindA IH2 bindA.
  apply: eq_bind => _.
  apply: eq_bind => u2.
  by rewrite !bindretf -catA.
Qed.

Lemma has_vars_subset r vs vs' :
  {subset vs' <= vs} ->
  has_vars r (vs ++ vs') = has_vars r vs.
Proof.
elim: vs' vs => [|v vs' IH] vs Hvs'.
  by rewrite cats0.
have -> : vs ++ v :: vs' = rcons vs v ++ vs' by rewrite -cats1 -catA.
rewrite IH; last first.
  move=> x Hx.
  have /Hvs' : x \in v :: vs' by rewrite in_cons Hx orbT.
  by rewrite mem_rcons in_cons orbC => ->.
rewrite !has_varsE.
apply: eq_bind => vars.
rewrite all_rcons.
case Hnth: nth => [l|] //=.
case: allP => H //.
have : v \in vs by apply: Hvs'; rewrite in_cons eqxx.
by move/H; rewrite Hnth.
Qed.

Lemma has_vars_csubstC r vs v t :
  {subset v :: free_vars t <= vs} ->
  has_vars r vs >> csubst r v t =
  has_vars r vs >> (csubst r v t >> has_vars r vs).
Proof.
rewrite /csubst /= => Hfv.
rewrite has_vars_repr_btreeC.
rewrite [in RHS]bindA [in RHS]has_vars_repr_btreeC.
apply: eq_bind => _.
apply: eq_bind => u.
rewrite has_vars_subset; last first.
   by move=> x Hx; apply: Hfv; rewrite in_cons Hx orbT.
rewrite has_vars_add_var bindA {1 2}has_varsE bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite !bindA !cputget.
apply: bind_ext_guard => /andP[Hvars Huniq].
have Hvvs : v \in vs by apply: Hfv; rewrite !inE eqxx.
move/allP/(_ _ Hvvs): (Hvars).
case Hnth: nth => [l|] // _.
rewrite !bindretf.
have rl : loc_id r != loc_id l.
  move/andP: Huniq => [] /[swap] _.
  apply: contra => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite -(bindA _ (fun=> cput l _)) cputC; try (exact nat || by left).
rewrite bindA [in RHS]bindA !cputget.
rewrite -(bindA (cput l _)) -cputC; try (exact nat || by left).
rewrite 2!bindA -(bindA (cput l _)) cput_cchkvarsC bindA -guardC.
by rewrite all_rcons Hnth.
Qed.

Definition free_vars_subst (s : substType) :=
  unzip1 s ++ flatten (map free_vars (unzip2 s)).

Lemma has_vars_csubst_listC r vs (s : substType) :
  {subset free_vars_subst s <= vs} ->
  has_vars r vs >> csubst_list r s =
  has_vars r vs >> (csubst_list r s >> has_vars r vs).
Proof.
elim: s => [|[v t] s IH] /= Hvs.
  by rewrite bindmskip bindskipf has_varsD.
have Hvt: {subset v :: free_vars t <= vs}.
  move=> x Hx; rewrite Hvs // /free_vars_subst /=.
  move: Hx; rewrite inE => /orP[/eqP -> | Hx].
    by rewrite in_cons eqxx.
  by rewrite in_cons !mem_cat Hx !orbT.
rewrite /csubst_list /= -bindA has_vars_csubstC //.
rewrite 3!bindA IH //; last first.
  move=> x Hx; rewrite Hvs // /free_vars_subst.
  move: Hx; rewrite mem_cat => /orP[] Hx.
    by rewrite /= in_cons mem_cat Hx orbT.
  by rewrite /= in_cons !mem_cat Hx !orbT.
by rewrite -2!bindA [X in X >> _]bindA -has_vars_csubstC // bindA.
Qed.

Lemma cchkvars_nth vars v l :
  nth None vars v = Some l -> cchkvars vars = cchk l >> cchkvars vars.
Proof.
rewrite /cchkvars.
elim: vars v => [|[u|] vars IH] [|v] //= H.
- case: H => ->.
  by rewrite -[RHS]bindA cchkdup.
- by rewrite (IH _ H) -[RHS]bindA cchkC bindA -(bindA (cchk l)) cchkdup.
- by rewrite bindskipf (IH _ H) -[RHS]bindA cchkdup.
Qed.

Section add_varC.
Variable (A : UU0) (m : M A).
Variable (r : @loc _ nat (ml_list (ml_option (ml_ref ml_uvar)))).
Hypothesis m_add_varC : forall B (vs : seq nat) v (k : _ -> _ -> M B),
    v \in vs ->
    has_vars r vs >> (do x <- m; add_var r v >>= k x) =
    has_vars r vs >> (do l <- add_var r v; m >>= k ^~ l).

Lemma m_repr_btreeC B vs t (k : _ -> _ -> M B) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (m >>= fun s => repr_btree r t >>= k s) =
  has_vars r vs >> (repr_btree r t >>= fun u => m >>= k ^~ u).
Proof.
elim: t k => [v|n|t1 IH1 t2 IH2] k /= Hvs.
- rewrite bindA.
  under [in LHS](eq_bind m) do
      (rewrite bindA; under eq_bind do rewrite bindretf).
  rewrite m_add_varC; last exact/Hvs/mem_head.
  by under [X in _ = _ >> X]eq_bind do rewrite bindretf.
- under (eq_bind m) do rewrite bindretf.
  by rewrite bindretf.
- rewrite bindA.
  under (eq_bind m) do rewrite bindA.
  have Ht1: {subset free_vars t1 <= vs}.
    by move=> x Hx; rewrite Hvs // mem_cat Hx.
  rewrite IH1 // has_vars_repr_btreeC has_vars_subset //.
  under (eq_bind (repr_btree r t1)) => u1.
    under (eq_bind m) do
      (rewrite bindA; under eq_bind do rewrite bindretf).
    rewrite IH2; first over.
    by move=> x Hx; rewrite Hvs // mem_cat Hx orbT.
  under [X in _ = _ >> X]eq_bind => u1 do
    (rewrite bindA; under eq_bind => u do rewrite bindretf).
  by rewrite [RHS]has_vars_repr_btreeC has_vars_subset.
Qed.
End add_varC.

Lemma cget_add_varC T A r (vs : seq nat) (r' : loc T) v (k : _ -> _ -> M A) :
  v \in vs ->
  has_vars r vs >> (do x <- cget r'; add_var r v >>= k x) =
  has_vars r vs >> (do l <- add_var r v; cget r' >>= k ^~ l).
Proof.
move=> Hv.
under (eq_bind (cget r')) do rewrite bindA.
rewrite cgetC has_varsE bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 6!bindA !cputget.
apply: bind_ext_guard => /andP[Hvars Hu].
move/allP/(_ _ Hv): Hvars.
case Hnth: nth => [l|] // _.
rewrite bindretf.
by under [in LHS](eq_bind (cget r')) do rewrite bindretf.
Qed.

Lemma cget_repr_btreeC T A r vs (r' : loc T) t (k : _ -> _ -> M A) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (cget r' >>= fun s => repr_btree r t >>= k s) =
  has_vars r vs >> (repr_btree r t >>= fun u => cget r' >>= k ^~ u).
Proof. by apply: m_repr_btreeC => ???; apply: cget_add_varC. Qed.

Lemma has_vars_add_var_skip r vs v :
  v \in vs -> has_vars r vs >> add_var_skip r v = has_vars r vs.
Proof.
rewrite has_varsE bindA => Hv.
apply: eq_bind => vars.
rewrite 3!bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
rewrite cputget.
move/allP/(_ _ Hv): Hvars => ->.
by rewrite bindmskip.
Qed.

Lemma has_add_varC A r (vs : seq nat) v v' (k : _ -> _ -> M A) :
  v \in vs ->
  has_vars r vs >> (do l' <- add_var r v'; add_var r v >>= k l') =
  has_vars r vs >> (do l <- add_var r v; add_var r v' >>= k ^~ l).
Proof.
move=> Hv.
rewrite (add_varC r v' v).
symmetry.
by rewrite -add_var_skipE -bindA has_vars_add_var_skip.
Qed.

Lemma add_var_repr_btreeC A r vs v t (k : _ -> _ -> M A) :
  v \in vs \/ {subset free_vars t <= vs} ->
  has_vars r vs >> (add_var r v >>= fun l => repr_btree r t >>= k l) =
  has_vars r vs >> (repr_btree r t >>= fun u => add_var r v >>= k ^~ u).
Proof.
case; last by apply: m_repr_btreeC => *; exact: has_add_varC.
move=> Hv.
elim: t vs Hv k => [v'|n|t1 IH1 t2 IH2] vs Hv k /=.
- rewrite bindA; under (eq_bind (add_var r v)) do rewrite bindA.
  rewrite -has_add_varC // -bindA -[RHS]bindA.
  apply: eq_bind => l'.
  under eq_bind do rewrite bindretf.
  by rewrite bindretf.
- under (eq_bind (add_var r v)) do rewrite bindretf.
  by rewrite bindretf.
- rewrite bindA; under (eq_bind (add_var r v)) do rewrite bindA.
  rewrite IH1 // has_vars_repr_btreeC.
  under (eq_bind (repr_btree _ _)) => u1.
    under (eq_bind (add_var r v)) do
      (rewrite bindA; under eq_bind do rewrite bindretf).
    rewrite IH2 //; first over.
    by rewrite mem_cat Hv.
  rewrite -has_vars_repr_btreeC.
  by under [X in _ = _ >> X]eq_bind do
    (rewrite bindA; under eq_bind do rewrite bindretf).
Qed.

Lemma sub_trans T : Relation_Definitions.transitive _ (@sub_mem T).
Proof. by move=> X Y Z xy yz x /xy /yz. Qed.

Lemma repr_btreeC A r vs t1 t2 (k : _ -> _ -> M A) :
  {subset free_vars t2 <= vs} ->
  has_vars r vs >> (do u1 <- repr_btree r t1; repr_btree r t2 >>= k u1) =
  has_vars r vs >> (do u2 <- repr_btree r t2; repr_btree r t1 >>= k ^~ u2).
Proof. by apply: m_repr_btreeC => *; rewrite add_var_repr_btreeC //; left. Qed.

Lemma repr_btree_repr_btree_listC A r vs t tl (k : _ -> _ -> M A) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (do u <- repr_btree r t; repr_btree_list r tl >>= k u) =
  has_vars r vs >> (do ul <- repr_btree_list r tl; repr_btree r t >>= k ^~ ul).
Proof.
elim: tl vs k => [|t1 tl IH] vs k /= Hvs.
  under (eq_bind (repr_btree r t)) do rewrite bindretf.
  by rewrite bindretf.
rewrite bindA.
under (eq_bind (repr_btree r t)) do rewrite bindA.
rewrite -repr_btreeC //.
rewrite has_vars_repr_btreeC [RHS]has_vars_repr_btreeC -bindA -[RHS]bindA.
apply: eq_bind => u1.
under (eq_bind (repr_btree r t)) do rewrite bindA.
rewrite IH; last by move=> x /Hvs; rewrite mem_cat => ->.
rewrite bindA -bindA -[RHS]bindA.
apply: eq_bind => u2.
rewrite bindretf.
by under eq_bind do rewrite bindretf.
Qed.

Definition free_vars_list tl := foldr cat nil (map free_vars tl).
Definition free_vars_pairs (l : seq (_ * _)) :=
  free_vars_list (unzip1 l) ++ free_vars_list (unzip2 l).

Lemma repr_btree_listC A r vs tl1 tl2 (k : _ -> _ -> M A) :
  {subset free_vars_list tl2 <= vs} ->
  has_vars r vs >>
    (do ul <- repr_btree_list r tl1; repr_btree_list r tl2 >>= k ul) =
  has_vars r vs >>
    (do ul <- repr_btree_list r tl2; repr_btree_list r tl1 >>= k ^~ ul).
Proof.
elim: tl2 vs k => [|t2 tl2 IH] vs k /= Hvs.
  under (eq_bind (repr_btree_list r tl1)) do rewrite bindretf.
  by rewrite bindretf.
rewrite bindA.
under (eq_bind (repr_btree_list r tl1)) do rewrite bindA.
rewrite -repr_btree_repr_btree_listC //; last first.
  by apply: sub_trans Hvs => x Hx; rewrite mem_cat Hx.
rewrite has_vars_repr_btreeC [RHS]has_vars_repr_btreeC -bindA -[RHS]bindA.
apply: eq_bind => u2.
under (eq_bind (repr_btree_list r tl1)) do rewrite bindA.
rewrite IH; last by move=> x Hx; rewrite mem_cat Hvs // mem_cat Hx orbT.
rewrite bindA -bindA -[RHS]bindA.
apply: eq_bind => ul2.
rewrite bindretf.
by under eq_bind do rewrite bindretf.
Qed.

Lemma repr_btreeD A r vs t (k : _ -> _ -> M A) :
  has_vars r vs >> (do u <- repr_btree r t; repr_btree r t >>= k u) =
  has_vars r vs >> (do u <- repr_btree r t; k u u).
Proof.
elim: t k vs => [v|n|t1 IH1 t2 IH2] k vs /=.
- rewrite bindA [in RHS]bindA.
  under [X in _ >> X]eq_bind do rewrite bindretf bindA.
  rewrite add_varD.
  apply: eq_bind => _.
  by apply: eq_bind => u; rewrite !bindretf.
- by rewrite !bindretf.
- rewrite 2!bindA.
  under [X in _ >> X]eq_bind => u1.
    rewrite bindA.
    under eq_bind do rewrite bindretf bindA.
    under eq_bind do under eq_bind do rewrite bindA.
    over.
  rewrite has_vars_repr_btreeC.
  under [X in _ >> X]eq_bind => u1.
    rewrite repr_btreeC; first over.
    by move=> x; rewrite mem_cat orbC => ->.
  rewrite -has_vars_repr_btreeC IH1 has_vars_repr_btreeC.
  under [X in _ >> X]eq_bind do rewrite IH2.
  rewrite -has_vars_repr_btreeC.
  apply: eq_bind => _.
  apply: eq_bind => u1.
  rewrite bindA.
  apply: eq_bind => u2.
  by rewrite !bindretf.
Qed.

Lemma put_var_add_varC A r vs v s v' (k : _ -> _ -> M A) :
  v \in vs ->
 has_vars r vs >> (do l <- add_var r v; cput l s >> (add_var r v' >>= k l)) =
 has_vars r vs >>
 (do l' <- add_var r v'; do l <- add_var r v; cput l s >> k l l').
Proof.
move=> Hv.
rewrite has_add_varC //.
rewrite has_varsE bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 3!bindA 2![in RHS]bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
rewrite bindA [in RHS]bindA !cputget.
move/allP/(_ _ Hv): (Hvars).
case Hnth: nth => [l|] // _.
have rl : loc_id r != loc_id l.
  move/andP: Hu => [] /[swap] _.
  apply: contra => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite !bindretf -(bindA (cput _ _)) cputC //; last by left.
rewrite !bindA !cputget.
case Hnth': nth => [l'|].
  rewrite -(bindA (cput _ _)) -cputC //; last by left.
  by rewrite !bindretf bindA.
rewrite -(bindA (cput l _)) -cputC //; last by left.
rewrite 3!bindA -cchknewput.
rewrite -bindA -cchkputC bindA -[LHS]bindA.
rewrite -cchk_cchkvarsC -(cchkvars_nth Hnth) -[LHS]bindA -[RHS]bindA.
apply: eq_bind => _.
apply: eq_bind => l'.
rewrite !bindA !bindretf -bindA -cputC //; last by left.
by rewrite bindA.
Qed.

Lemma csubst_add_varC A r vs v t v' (k : _ -> M A) :
  {subset v :: free_vars t <= vs} ->
  has_vars r vs >> (csubst r v t >> (add_var r v' >>= k)) =
  has_vars r vs >> (add_var r v' >>= fun u => csubst r v t >> k u).
Proof.
move=> Hfv.
rewrite /csubst bindA.
under [in RHS](eq_bind (add_var r v')) do rewrite bindA.
rewrite add_var_repr_btreeC; last first.
  by right; move=> x Hx; rewrite Hfv // in_cons Hx orbT.
rewrite has_vars_repr_btreeC [RHS]has_vars_repr_btreeC.
apply: eq_bind => _.
apply: eq_bind => u.
rewrite bindA put_var_add_varC; last by rewrite mem_cat Hfv // inE eqxx.
by under [in RHS](eq_bind (add_var r v')) do rewrite bindA.
Qed.

Lemma free_vars_subst_subset (s1 s2 : substType) :
  {subset s1 <= s2} -> {subset free_vars_subst s1 <= free_vars_subst s2}.
Proof.
rewrite /free_vars_subst.
elim: s1 => //= -[v t] s1 IH /= Hs2 x.
rewrite !inE !mem_cat => /orP[/eqP ->|].
  by move: (Hs2 _ (mem_head _ _)) => /(map_f fst) /= ->.
case/orP.
  case/mapP => y Hy ->.
  by move: (Hs2 y (mem_tail _ Hy)) => /(map_f fst) ->.
case/orP => Hx.
  apply/orP; right.
  apply/flattenP.
  exists (free_vars t) => //.
  exact/map_f/(map_f snd (x:=(v,t)))/Hs2/mem_head.
rewrite -mem_cat.
apply: IH.
  by move=> y Hy; rewrite Hs2 // inE Hy orbT.
by rewrite mem_cat Hx orbT.
Qed.

Lemma csubst_list_add_varC A r vs s v (k : _ -> M A) :
  {subset free_vars_subst s <= vs} ->
  has_vars r vs >> (csubst_list r s >> (add_var r v >>= k)) =
  has_vars r vs >> (add_var r v >>= fun u => csubst_list r s >> k u).
Proof.
elim: s k => [|[v' t] s IH] k Hvs.
  rewrite bindskipf.
  by under [X in _ = _ >> X]eq_bind do rewrite bindretf.
rewrite /csubst_list /= -/(csubst_list r s).
have Hsub': {subset v' :: free_vars t <= vs}.
  apply: sub_trans Hvs => x; rewrite /free_vars_subst /= !inE !mem_cat.
  by case/orP => -> //; rewrite !orbT.
rewrite bindA -(bindA (has_vars _ _)) has_vars_csubstC //.
rewrite 2!bindA IH; last first.
  apply: sub_trans Hvs => x; rewrite /free_vars_subst /= !inE !mem_cat.
  by case/orP => ->; rewrite ?orbT.
rewrite -2!bindA (bindA (has_vars _ _)) -has_vars_csubstC //.
rewrite bindA csubst_add_varC //.
by under [X in _ = _ >> X]eq_bind do rewrite bindA.
Qed.

Lemma get_var_csubstC A r vs v v' t (k : _ -> _ -> M A) :
  {subset v :: v' :: free_vars t <= vs} ->
  v != v' ->
  has_vars r vs >> (do l <- add_var r v; do x <- cget l; csubst r v' t >> k l x)
  = has_vars r vs >> (csubst r v' t >> do l <- add_var r v; cget l >>= k l).
Proof.
move=> Hvs vv'.
have Hfv: {subset free_vars t <= vs}.
  by move=> x Hx; rewrite Hvs // !inE Hx !orbT.
rewrite csubst_add_varC; last first.
  by move=> x Hx; rewrite Hvs // inE Hx orbT.
rewrite has_vars_add_var.
under (eq_bind (add_var r v)) => l.
  under (eq_bind (cget l)) do rewrite bindA.
  rewrite cget_repr_btreeC; first over.
  by move=> x Hx; rewrite mem_rcons inE Hfv // orbT.
rewrite -has_vars_add_var.
rewrite add_var_repr_btreeC; last by right.
under (eq_bind (add_var r v)) => l do rewrite bindA.
rewrite add_var_repr_btreeC; last by right.
rewrite has_vars_repr_btreeC [RHS]has_vars_repr_btreeC.
apply: eq_bind => _.
apply: eq_bind => u.
rewrite has_vars_subset //.
rewrite has_varsE bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 3!bindA 2![in RHS]bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
rewrite bindA [in RHS]bindA !cputget.
have Hvvs : v \in vs by apply: Hvs; rewrite !inE eqxx.
move/allP/(_ _ Hvvs): (Hvars).
case Hnth: nth => [l|] // _.
have rl: loc_id r != loc_id l.
  case/andP: Hu => Hr _.
  apply: contra Hr => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite !bindretf cputgetC //.
under [in LHS](eq_bind (cget l)) do rewrite 2!bindA cputget.
rewrite 2![in RHS]bindA cputget.
have Hv'vs : v' \in vs by apply: Hvs; rewrite !inE eqxx orbT.
move/allP/(_ _ Hv'vs): (Hvars).
case Hnth': nth => [l'|] // _.
rewrite bindretf.
under (eq_bind (cget l)) do rewrite bindretf.
rewrite -cputgetC // -cputgetC // eq_sym.
apply: (uniq_loc_vars_some _ Hnth Hnth') => //.
by case/andP: Hu.
Qed.

Lemma get_var_csubst_listC A r vs v (s : substType) (k : _ -> _ -> M A) :
  {subset v :: free_vars_subst s <= vs} ->
  v \notin unzip1 s ->
  has_vars r vs >>
  (do l <- add_var r v; do x <- cget l; csubst_list r s >> k l x) =
  has_vars r vs >> (csubst_list r s >> do l <- add_var r v; cget l >>= k l).
Proof.
elim: s k => [|[v' t] s IH] k Hsub Hv.
  under [X in _ >> X]eq_bind do under eq_bind do rewrite bindskipf.
  by rewrite bindskipf.
rewrite /csubst_list /= -/(csubst_list r s).
symmetry.
have Hsub': {subset v' :: free_vars t <= vs}.
  move=> x Hx; rewrite Hsub // /free_vars_subst /= !inE !mem_cat.
  rewrite (orbCA (x \in unzip1 s)) (orbA (x == v')) -in_cons.
  by rewrite Hx orbT.
rewrite bindA -[LHS]bindA has_vars_csubstC // 2!bindA -IH; first last.
- by apply: contra Hv; rewrite /= inE orbC => ->.
- move=> x Hx; apply: Hsub.
  move: Hx; rewrite 2!inE => /orP[-> // | Hx].
  apply/orP; right; apply/(free_vars_subst_subset _ Hx).
  by move=> y; rewrite inE orbC => ->.
rewrite -2!bindA (bindA (has_vars _ _)) -has_vars_csubstC //.
rewrite bindA -get_var_csubstC.
- by under [X in _ = _ >> X]eq_bind do under eq_bind do rewrite bindA.
- move=> x; rewrite inE => /orP[] Hx.
    by rewrite Hsub // inE Hx.
  exact: Hsub'.
- apply: contra Hv => /eqP <- /=.
  by rewrite inE eqxx.
Qed.

Definition vars_subst '(v, t) := rcons (free_vars t) v.
Definition vars_subst_list (s : substType) :=
  foldr cat nil (map vars_subst s).

Lemma csubst_repr_btreeC A r vs v t bt (k : _ -> M A) :
  {subset v :: free_vars t <= vs} ->
  has_vars r vs >> (csubst r v t >> (repr_btree r bt >>= k)) =
  has_vars r vs >> (repr_btree r bt >>= fun u => csubst r v t >> k u).
Proof.
move=> Hvs.
elim: bt k vs Hvs => [v'|n|t1 IH1 t2 IH2] k vs Hvs /=.
- rewrite bindA [in RHS]bindA csubst_add_varC //.
  under (eq_bind (add_var r v')) => l do rewrite bindretf.
  by under [in RHS](eq_bind (add_var r v')) => l do rewrite bindretf.
- by rewrite !bindretf.
- rewrite bindA.
  under (eq_bind (repr_btree r t1)) do
    (rewrite bindA; under eq_bind do rewrite bindretf).
  rewrite IH1 // has_vars_repr_btreeC.
  under (eq_bind (repr_btree r t1)) => u1.
    rewrite IH2; first over.
    by move=> ? ?; rewrite mem_cat Hvs.
  rewrite -has_vars_repr_btreeC.
  rewrite bindA.
  by under [in RHS](eq_bind (repr_btree r t1)) => u1 do
    (rewrite bindA; under eq_bind do rewrite bindretf).
Qed.

Lemma csubst_get_var A r vs v t (k : _ -> _ -> M A) :
  {subset v :: free_vars t <= vs} ->
  has_vars r vs >> (csubst r v t >> do l <- add_var r v; cget l >>= k l) =
  has_vars r vs >>
  (csubst r v t >> do l <- add_var r v; do u <- repr_btree r t; k l (uTerm u)).
Proof.
move=> Hvs.
have Hfvt: {subset free_vars t <= vs}.
  by apply: sub_trans Hvs => x; rewrite inE orbC => ->.
rewrite csubst_add_varC // [in RHS]csubst_add_varC //.
rewrite [RHS]has_vars_add_var.
under [X in _ = _ >> X]eq_bind => u.
  rewrite csubst_repr_btreeC; last first.
    by apply: (sub_trans Hvs) => x; rewrite mem_rcons inE orbC => ->.
  under (eq_bind (repr_btree r t)) do rewrite bindA.
  rewrite repr_btreeD.
  over.
rewrite -has_vars_add_var add_var_repr_btreeC; last by right.
under [X in _ >> X]eq_bind do rewrite bindA.
rewrite add_var_repr_btreeC; last by right.
apply: eq_bind => _.
apply: eq_bind => u.
under eq_bind do rewrite bindA.
under [RHS]eq_bind do rewrite bindA.
rewrite !add_varD.
apply: eq_bind => l.
by rewrite cputget.
Qed.

Lemma csubst_list_repr_btreeC A r vs s bt (k : _ -> M A) :
  {subset free_vars_subst s <= vs} ->
  has_vars r vs >> (csubst_list r s >> (repr_btree r bt >>= k)) =
  has_vars r vs >> (repr_btree r bt >>= fun u => csubst_list r s >> k u).
Proof.
elim: s k => [|[v t] s IH] /= k Hvs.
  rewrite bindskipf.
  by under [X in _ = _ >> X]eq_bind do rewrite bindskipf.
rewrite /csubst_list /=.
under [X in _ = _ >> X]eq_bind do rewrite bindA.
have Hvt : {subset v :: free_vars t <= vs}.
  move=> x Hx; apply: Hvs.
  rewrite /free_vars_subst /= in_cons !mem_cat.
  move: Hx; rewrite in_cons => /orP[] -> //.
  by rewrite !orbT.
rewrite -csubst_repr_btreeC //.
rewrite -[RHS]bindA has_vars_csubstC // 3!bindA -IH //; first last.
  move=> x Hx; rewrite Hvs // /free_vars_subst /= in_cons !mem_cat.
  by move: Hx; rewrite mem_cat => /orP[] ->; rewrite !orbT.
by rewrite -2![RHS]bindA [X in _ = X >> _]bindA -has_vars_csubstC // bindA.
Qed.

Lemma has_vars_cgetC A T r vs (r' : loc T) (k : _ -> M A) :
  has_vars r vs >> (cget r' >>= k) =
  has_vars r vs >> do x <- cget r'; has_vars r vs >> k x.
Proof.
rewrite {1 2}has_varsE !bindA.
apply: eq_bind => vars.
rewrite !bindA.
apply: bind_ext_guard => Hg.
symmetry.
under (eq_bind (cget r')) do rewrite !bindA.
rewrite cgetC cputget Hg guardT bindmskip cget_cchkvarsC.
rewrite -(bindA (cput r _)) cput_cchkvarsC bindA.
by rewrite -[LHS]bindA cchkvarsD.
Qed.

Definition not_uLink u := if u is uLink _ then false else true.

Lemma expand_head_not_uLink he u : not_uLink u -> expand_head he u = Ret u.
Proof. by case: u => // *; case: he. Qed.

Lemma repr_btree_expand_headC A r vs t he u (k : _ -> _ -> M A) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (do u1 <- repr_btree r t; expand_head he u >>= k u1) =
  has_vars r vs >> (do u2 <- expand_head he u; repr_btree r t >>= k ^~ u2).
Proof.
move=> Ht.
elim: he u => [|he IH] u.
  rewrite /= bindretf.
  by under (eq_bind (repr_btree r t)) do rewrite bindretf.
case/boolP: (not_uLink u) => Hu.
  rewrite expand_head_not_uLink // bindretf.
  by under (eq_bind (repr_btree r t)) do rewrite bindretf.
case Hu: u Hu => [l||] //= _.
under (eq_bind (repr_btree r t)) do rewrite bindA.
rewrite -(cget_repr_btreeC r l) // bindA.
rewrite has_vars_cgetC.
rewrite [in RHS](has_vars_cgetC r vs l).
apply: eq_bind => _.
apply: eq_bind => -[n|u'] //.
rewrite bindretf.
by under (eq_bind (repr_btree r t)) do rewrite bindretf.
Qed.

Lemma repr_btree_list_expand_headC A r vs tl he u (k : _ -> _ -> M A) :
  {subset free_vars_list tl <= vs} ->
  has_vars r vs >> (do s <- repr_btree_list r tl; expand_head he u >>= k s) =
  has_vars r vs >> (do u' <- expand_head he u; repr_btree_list r tl >>= k^~ u').
Proof.
elim: tl k => [|t tl IH] k /= Hsub.
  rewrite bindretf.
  by under [in RHS](eq_bind (expand_head _ _)) do rewrite bindretf.
symmetry.
rewrite bindA.
under (eq_bind (expand_head _ _)) do rewrite bindA.
have Hfvt: {subset free_vars t <= vs}.
  by apply: sub_trans Hsub => x Hx; rewrite mem_cat Hx.
rewrite -repr_btree_expand_headC //.
rewrite has_vars_repr_btreeC has_vars_subset //.
under (eq_bind (repr_btree _ _)) => u1.
  under (eq_bind (expand_head _ _)) do
    (rewrite bindA; under eq_bind do rewrite bindretf).
  rewrite -IH; first over.
  by apply: sub_trans Hsub => x Hx; rewrite mem_cat Hx orbT.
rewrite -{2}(has_vars_subset r Hfvt) -has_vars_repr_btreeC.
by under [X in _ = _ >> X]eq_bind do
  (rewrite bindA; under eq_bind do rewrite bindretf).
Qed.

Lemma has_vars_repr_btree_listC A r vs tl (k : _ -> M A) :
  has_vars r vs >> (repr_btree_list r tl >>= k) =
  has_vars r vs >>
  do ul <- repr_btree_list r tl; has_vars r (vs ++ free_vars_list tl) >> k ul.
Proof.
elim: tl vs k => [|t tl IH] vs k //=.
  by rewrite !bindretf cats0 -bindA has_varsD.
rewrite bindA has_vars_repr_btreeC.
under (eq_bind (repr_btree r t)) => u1.
  rewrite bindA; under (eq_bind (repr_btree_list _ _)) do rewrite bindretf.
  rewrite IH -catA; over.
rewrite -has_vars_repr_btreeC bindA.
by under [in RHS](eq_bind (repr_btree r t)) do
  (rewrite bindA; under eq_bind do rewrite bindretf).
Qed.

Lemma has_vars_expand_headC A r vs he u (k : _ -> M A) :
  has_vars r vs >> (expand_head he u >>= k) =
  has_vars r vs >> do u' <- expand_head he u; has_vars r vs >> k u'.
Proof.
elim: he u k => [|he IH] u k.
  by rewrite !bindretf -bindA has_varsD.
case/boolP: (not_uLink u).
  move/expand_head_not_uLink => ->.
  by rewrite !bindretf -bindA has_varsD.
case Hu: u => [l||] //= _.
rewrite 2!bindA.
rewrite (has_vars_cgetC r vs l) [RHS](has_vars_cgetC r vs l).
apply: eq_bind => _.
apply: eq_bind => -[n|u'] //.
by rewrite !bindretf -bindA has_varsD.
Qed.

Definition push_subst : substType -> substType :=
  foldl (fun s '(v,t) => rcons s (v, subst_list s t)) nil.

Lemma size_push_subst s : size (push_subst s) = size s.
Proof.
rewrite /push_subst; set h := nil; pose t := s; rewrite -{1}/t.
have <- : size h + size t = size s by [].
elim: t h => /= [|[x y] t IH] h.
  by rewrite addn0.
by rewrite IH /= size_rcons addnS.
Qed.

Fixpoint push_subst' (s1 s2 : substType) :=
  match s2 with
  | nil => nil
  | (x, t) :: s2' =>
      let p := (x, subst_list s1 t) in
      p :: push_subst' (rcons s1 p) s2'
  end.

Lemma push_subst'_cat s0 s1 s2 :
  push_subst' s0 (s1++s2) =
  push_subst' s0 s1 ++ push_subst' (s0 ++ push_subst' s0 s1) s2.
Proof.
elim/last_ind: s1 s2 => [|s1 [x t] IH] s2 //=.
  by rewrite cats0.
by rewrite -cats1 -catA IH IH /= -!(catA,cats1).
Qed.

Lemma push_substE s :
  push_subst s = push_subst' nil s.
Proof.
elim/last_ind: s => [|s [x t] IH] //=.
by rewrite /push_subst foldl_rcons /= -!cats1 push_subst'_cat /= -IH.
Qed.

Lemma push_subst_cat s1 s2 :
  push_subst (s1 ++ s2) = push_subst s1 ++ push_subst' (push_subst s1) s2.
Proof. by rewrite !push_substE push_subst'_cat. Qed.

Lemma free_varsE t : free_vars t =i vars t.
Proof.
elim: t => //= t1 IH1 t2 IH2.
by move=> x; rewrite mem_cat IH1 IH2 in_union_or.
Qed.

Lemma ltnm0 (n m : nat) : m < n -> 0 < n.
Proof. exact: leq_ltn_trans. Qed.

Fixpoint bt_expand_head s t : btree :=
  if t is btVar v then
    match s with
    | nil => t
    | (v', t') :: s' => bt_expand_head s' (if v == v' then t' else t)
    end
  else t.

Definition not_btVar t := if t is btVar _ then false else true.

Lemma bt_expand_head_not_btVar s t : not_btVar t -> bt_expand_head s t = t.
Proof. by case: t => // *; case: s. Qed.

Lemma bt_expand_head_cat s1 s2 t :
  bt_expand_head (s1 ++ s2) t = bt_expand_head s2 (bt_expand_head s1 t).
Proof.
by elim: s1 t => [|[v' t'] s1 IH] [v|n|t1 t2] //=;
   rewrite !bt_expand_head_not_btVar.
Qed.

Lemma bt_expand_notin v (s : substType) :
  v \notin unzip1 s ->
  bt_expand_head s (btVar v) = btVar v.
Proof.
elim: s => // [[v' t] l] IH.
case /boolP : (v == v') => [/eqP <-|Hneq] /=.
  by rewrite mem_head.
have -> //: v == v' = false by apply: (@contra_neqF _ _ v v') => [/eqP|] //.
move => H; apply: IH; move: H.
by rewrite /in_mem negb_or Hneq.
Qed.

Lemma bt_expand_head_in s u :
  bt_expand_head s u \in u :: unzip2 s.
Proof.
elim: s u => [|[v t] s IH] [n|n|t1 t2] => //; rewrite inE ?eqxx //=.
case: ifPn => nv.
  by rewrite IH orbT.
by rewrite inE orbCA -in_cons IH orbT.
Qed.

Lemma repr_btree_not_btVar A r t (k : _ -> M A) :
  not_btVar t ->
  repr_btree r t >>= k =
  repr_btree r t >>= fun u => guard (not_uLink u) >> k u.
Proof.
case: t => //= *.
  by rewrite !bindretf.
rewrite !bindA; apply: eq_bind => u1.
rewrite !bindA; apply: eq_bind => u2.
by rewrite !bindretf.
Qed.

Definition dominates (s : substType) (x y : var) :=
  has (fun '(z, t) => (z == x) && (y \in free_vars t)) s.

Definition acyclic_subst s := forall x p, ~~ cycle (dominates s) (x :: p).

Fixpoint sorted_subst (s : substType) : bool :=
  match s with
  | nil => true
  | (v, t) :: s' =>
    (v \notin unzip1 s') &&
    (btVar v \notin unzip2 s) &&
    sorted_subst s'
  end.

Lemma sorted_subst_catr (s1 s2 : substType) :
  sorted_subst (s1 ++ s2) -> sorted_subst s2.
Proof. by elim: s1 => // -[v t] s1 IH /= /andP[_]. Qed.

Lemma sorted_subst_catl (s1 s2 : substType) :
  sorted_subst (s1 ++ s2) -> sorted_subst s1.
Proof.
elim: s1 => // -[v t] s1 IH /= /andP[].
rewrite [unzip1 _]map_cat mem_cat negb_or => /andP[] /andP[-> _].
by rewrite 2!inE [unzip2 _]map_cat mem_cat 3!negb_or => /andP[->] /andP[->].
Qed.

Lemma free_vars_dominates y t s :
  y \notin free_vars t ->
  y \in free_vars (subst_list s t) ->
  exists z p, z \in free_vars t /\ path (dominates s) z (rcons p y).
Proof.
elim: s t => /= [|[v t'] s IH] t /=.
  by move/[swap] ->.
move=> yt.
elim: t yt => [v'|n|t1 IH1 t2 IH2] /=.
- rewrite inE => yv'.
  case: ifPn => vv' Hy.
    rewrite (eqP vv').
    exists v'; rewrite inE eqxx.
    case/boolP: (y \in free_vars t') => yt'.
      exists nil; split => //=.
      by rewrite eqxx yt'.
    case: (IH _ yt' Hy) => z [p [Hz Hp]].
    exists (z::p); split => //=.
    rewrite eqxx Hz /=.
    apply: sub_path Hp => a b /= ->.
    by rewrite orbT.
  have Hfv : y \notin free_vars (btVar v') by rewrite inE.
  case: (IH _ Hfv Hy) => z [p [Hz Hp]].
  exists z, p.
  split => //.
  apply: sub_path Hp => a b /= ->.
  by rewrite orbT.
- by rewrite subst_btInt.
- rewrite subst_btNode /= mem_cat negb_or => /andP[Hy1 Hy2].
  rewrite mem_cat => /orP[] Hys.
    case: (IH1 Hy1 Hys) => z [p [Hz Hp]].
    by exists z, p; rewrite mem_cat Hz.
  case: (IH2 Hy2 Hys) => z [p [Hz Hp]].
  by exists z, p; rewrite mem_cat Hz orbT.
Qed.

Lemma map_path_single (A : eqType) (r1 r2 : rel A) :
  (forall x y, r1 x y -> exists p, path r2 x (rcons p y)) ->
  (forall x p y, path r1 x (rcons p y) -> exists p', path r2 x (rcons p' y)).
Proof.
move=> r1r2 x p.
elim: p x => [|z p IH] x y /=.
  rewrite andbT => xy.
  exact: r1r2.
case/andP => xz zy.
case: (r1r2 _ _ xz) => p1 Hp1.
case: (IH _ _ zy) => p2 Hp2.
exists (rcons p1 z ++ p2) => /=.
by rewrite rcons_cat /= cat_path last_rcons Hp1 Hp2.
Qed.

Lemma free_vars_dominates' x y s0 s t :
  y \in free_vars (subst_list s0 t) ->
  exists p, path (dominates (s0 ++ (x, t) :: s)) x (rcons p y).
Proof.
move=> Hy.
case/boolP: (y \in free_vars t) => yt.
  exists nil => /=.
  by rewrite /dominates has_cat /= eqxx yt !orbT.
case: (free_vars_dominates yt Hy) => z [p] [Hz Hp].
exists (z :: p) => /=.
rewrite (sub_path _ Hp) ?andbT; last first.
  by move => a b; rewrite /dominates has_cat => ->.
by apply/hasP; exists (x,t); rewrite ?eqxx //= mem_cat inE eqxx orbT.
Qed.

Lemma dominates_subst_list s0 s v t x y :
  dominates (s0 ++ (v, subst_list s0 t) :: s) x y ->
  exists p : seq nat, path (dominates (s0 ++ (v, t) :: s)) x (rcons p y).
Proof.
case/hasP => /= -[z t'].
rewrite mem_cat orbC inE /= -orbA -mem_cat =>
  /orP[/eqP[] -> -> | Hz] /andP[/eqP <-] Hy.
  exact: free_vars_dominates'.
exists nil => /=.
rewrite andbT.
apply/hasP; exists (z,t').
  by rewrite mem_cat inE orbC -orbA -mem_cat Hz orbT.
by rewrite eqxx.
Qed.

Lemma dominates_push_subst' s0 s x y :
  dominates (push_subst' s0 s) x y ->
  exists p, path (dominates (s0 ++ s)) x (rcons p y).
Proof.
elim: s s0 x y => [|[v t] s IH] s0 x y //.
rewrite -cat1s push_subst'_cat [dominates _ _ _]has_cat /= orbF.
rewrite -/(dominates _ _ _).
case/boolP: (_ && _).
  case/andP => /eqP -> Hy _.
  exact: free_vars_dominates'.
rewrite negb_and /= => Hv Dxy.
case: (IH (s0 ++ [:: (v, subst_list s0 t)]) x y) => /=.
  by rewrite Dxy.
move=> p' Hp'.
apply: map_path_single Hp' => /= ? ?.
rewrite -catA /=.
exact: dominates_subst_list.
Qed.

Lemma dominates_push_subst s x y :
  dominates (push_subst s) x y ->
  exists p, path (dominates s) x (rcons p y).
Proof. by rewrite push_substE => /dominates_push_subst'. Qed.

Lemma acyclic_subst_sub (s1 s2 : substType) :
  {subset s1 <= s2} -> acyclic_subst s2 -> acyclic_subst s1.
Proof.
move=> Hsub Hac x p.
apply: contra (Hac x p) => /=.
apply: sub_path => a b /hasP /= [[v t]] Hs1 Ha.
apply/hasP; exists (v,t) => //.
by apply: Hsub Hs1.
Qed.

Lemma push_subst_acyclic s :
  acyclic_subst s -> acyclic_subst (push_subst s).
Proof.
move=> Hac x p.
apply/negP => /(map_path_single (@dominates_push_subst s)) /=.
case=> p' Hp'.
move: (Hac x p') => /=.
by rewrite Hp'.
Qed.

Lemma dom_push_subst' (s0 s : substType) :
  unzip1 (push_subst' s0 s) = unzip1 s.
Proof. by elim: s s0 => // -[x t] s IH s0 /=; rewrite IH. Qed.

Lemma subst_list_same (s : substType) t :
  all (fun x => x \notin free_vars t) (unzip1 s) ->
  subst_list s t = t.
Proof.
elim: s => //= -[v t'] s IH /= /andP[Hv] Hall.
by rewrite subst_same ?IH // -free_varsE.
Qed.

Lemma all_notinE (A : eqType) (s1 s2 : seq A) :
  all (fun x => x \notin s1) s2 = all (fun x => x \notin s2) s1.
Proof.
elim: s1 => [|a s1 IH] /=.
  by rewrite all_predT.
rewrite -IH.
case/boolP: (a \in s2) => as2 /=.
  apply/allP => /(_ _ as2).
  by rewrite inE eqxx.
apply eq_in_all => x Hx.
rewrite inE negb_or.
case/boolP: (x == a) => //= /eqP xa.
by rewrite -xa Hx in as2.
Qed.
 
Lemma free_vars_keep s v t :
  v \notin unzip1 s ->
  v \in free_vars t ->
  v \in free_vars (subst_list s t).
Proof.
elim: t => [n|n|t1 IH1 t2 IH2] //= Hu.
  rewrite inE => /eqP <- /=.
  rewrite subst_list_same /=.
    by rewrite inE.
  by rewrite all_notinE /= Hu.
rewrite mem_cat subst_btNode /= mem_cat => /orP[] Hv.
  by rewrite IH1.
by rewrite IH2 // orbT.
Qed.

Definition idempotent_subst' (s : substType) :=
  all (fun x => all (fun t => x \notin free_vars t) (unzip2 s)) (unzip1 s).

Definition idempotent_subst (s : substType) :=
  all (fun x =>
    all (fun y => y \notin free_vars (subst_list s (btVar x))) (unzip1 s))
    (unzip1 s).

Lemma idempotent_substP s :
  reflect
    (forall t,
        all (fun y => y \notin free_vars (subst_list s t)) (unzip1 s))
    (idempotent_subst s).
Proof.
case/boolP: (idempotent_subst s); constructor; last first.
  move=> Ht; elim (negP i).
  apply/allP => x Hx.
  exact: Ht.
elim => [x|n|t1 IH1 t2 IH2] /=.
- case/boolP: (x \in unzip1 s) => Hx.
    by move/allP/(_ _ Hx): p.
  apply/allP => y Hy.
  rewrite subst_list_same /=.
    rewrite inE; apply/negP => /eqP yx.
    by rewrite -yx Hy in Hx.
  by rewrite all_notinE /= andbT.
- apply/allP => y Hy.
  by rewrite subst_btInt.
- by rewrite subst_btNode /= all_notinE all_cat all_notinE IH1 all_notinE IH2.
Qed.

Lemma idempotent_subst'P s :
  idempotent_subst' s -> idempotent_subst s.
Proof.
move=> Hid.
apply/allP => /= x Hx.
apply/allP => /= y Hy.
set s0 := s in Hid Hy.
have : {subset s <= s0} by [].
clearbody s0.
elim: s Hx => // -[x' t'] s /= IH.
rewrite inE eq_sym.
case: (_ == _) => /= [_ | Hx] Hsub; last first.
  apply: IH => //.
  by apply: sub_trans Hsub => u; rewrite inE orbC => ->.
have /(map_f snd) /= Ht' := Hsub (x',t') (mem_head _ _).
have {}Hsub : {subset s <= s0}.
  by apply: sub_trans Hsub => u; rewrite inE orbC => ->.
elim: s Hsub {IH} => [|[x1 t2] s IH] /= Hsub.
  by move/allP/(_ y Hy)/allP/(_ t' Ht'): Hid.
rewrite subst_same.
  apply: IH.
  by apply: sub_trans Hsub => u; rewrite inE orbC => ->.
have /(map_f fst) /= Hx1 := Hsub (x1,t2) (mem_head _ _).
move/allP/(_ x1 Hx1)/allP/(_ t' Ht'): Hid.
by rewrite free_varsE.
Qed.

Lemma idempotent_subst_nil : idempotent_subst nil.
Proof. by apply/allP. Qed.

Lemma acyclic_idempotent_push_subst' s0 s :
  idempotent_subst s0 ->
  acyclic_subst (s0 ++ s) -> idempotent_subst (s0 ++ push_subst' s0 s).
Proof.
elim: s s0 => [|[v t] s IH] s0 Hs0 Hac /=.
  by rewrite cats0.
have Hs0' : idempotent_subst (rcons s0 (v, subst_list s0 t)).
  apply/allP => /= x.
  rewrite /unzip1 map_rcons mem_rcons inE /=.
  case/boolP: (x == v) => [/eqP-> _ | xv /= Hx].
    apply/allP => /= y.
    rewrite mem_rcons inE => /orP[/eqP-> |].
      rewrite /subst_list foldl_rcons /= -!/(subst_list _ _).
      case/boolP: (v \in unzip1 s0) => Hv.
        rewrite subst_same -?free_varsE;
        by move/allP/(_ v Hv)/allP/(_ v Hv): Hs0.
      rewrite [X in subst _ _ X]subst_list_same /=; last first.
        apply/allP => v'; rewrite inE; case/boolP: (v' == v) => // /eqP vv'.
        by rewrite vv' (negbTE Hv).
      rewrite eqxx.
      move: (Hac v nil) => /=.
      rewrite /dominates has_cat /= -!/(dominates _ _ _).
      rewrite eqxx /= andbT !negb_or => /andP[] _ /andP[] Hvt _.
      apply/negP => Hvs.
      move: (free_vars_dominates Hvt Hvs) => /= [z] [p] [Hz Hp].
      move: (Hac v (z :: p)) => /=.
      rewrite /dominates has_cat /= -!/(dominates _ _ _).
      rewrite eqxx Hz /= orbT /=.
      move/negP; elim.
      apply: sub_path Hp => a b /hasP /= [[c t']] Hs0' Hc.
      apply/hasP; exists (c,t') => //.
      by rewrite mem_cat Hs0'.
    move=> Hy.
    rewrite /subst_list foldl_rcons /= -!/(subst_list _ _).
    case/boolP: (v \in unzip1 s0) => Hv.
      rewrite subst_same -?free_varsE.
        by move/allP/(_ v Hv)/allP/(_ y Hy): Hs0.
      by move/allP/(_ v Hv)/allP/(_ v Hv): Hs0.
    rewrite [X in subst _ _ X]subst_list_same /=; last first.
      apply/allP => v'; rewrite inE; case/boolP: (v' == v) => // /eqP vv'.
      by rewrite vv' (negbTE Hv).
    rewrite eqxx.
    by move/idempotent_substP/(_ t)/allP/(_ _ Hy): Hs0.
  apply/allP => y.
  rewrite /subst_list foldl_rcons /= -!/(subst_list _ _).
  rewrite mem_rcons inE => /orP[/eqP-> | Hy].
    case/boolP: (v \in free_vars (subst_list s0 (btVar x))) => Hv; last first.
      by rewrite subst_same -?free_varsE.
    case: (free_vars_dominates _ Hv).
      by rewrite inE eq_sym.
    move=> /= z [p] [].
    rewrite inE => /eqP -> Hp.
    case/boolP: (v \in free_vars t) => Hvt.
      move: (Hac v nil) => /=.
      rewrite andbT => /negP; elim.
      apply/hasP; exists (v,t).
        by rewrite mem_cat inE eqxx orbT.
      by rewrite eqxx Hvt.
    case/boolP: (v \in free_vars (subst_list s0 t)) => Hvt'; last first.
      by rewrite free_varsE subst_del // -free_varsE.
    case: (free_vars_dominates Hvt Hvt') => {}z [p'] [Hz Hp'].
    move: (Hac v (z :: p')) => /= /negP; elim.
    apply/andP; split.
      apply/hasP; exists (v,t).
        by rewrite mem_cat inE eqxx orbT.
      by rewrite eqxx Hz.
    apply: sub_path Hp' => a b.
    by rewrite /dominates has_cat => ->.
  rewrite free_varsE.
  apply/negP => /subst_sub.
  move/idempotent_substP in Hs0.
  rewrite in_union_or -!free_varsE => /orP[].
    by move/allP/(_ _ Hy)/negbTE: (Hs0 t) => ->.
  by move/allP/(_ _ Hy)/negbTE: (Hs0 (btVar x)) => ->.
rewrite -cat1s catA cats1 IH // -cats1 -catA /=.
move=> x p /=.
apply/negP => Hp.
suff : exists p',  path (dominates (s0 ++ (v, t) :: s)) x (rcons p' x).
  case => p' Hp'.
  move: (Hac x p').
  by rewrite /= Hp'.
move: Hp.
apply: map_path_single.
exact: dominates_subst_list.
Qed.

Lemma acyclic_idempotent_push_subst s :
  acyclic_subst s -> idempotent_subst (push_subst s).
Proof.
have := idempotent_subst_nil.
rewrite -(cat0s s) push_subst_cat.
exact: acyclic_idempotent_push_subst'.
Qed.

Lemma bt_expand_head_idem s t :
  sorted_subst s -> bt_expand_head s (bt_expand_head s t) = bt_expand_head s t.
Proof.
elim: s t => [|[v' t'] s IH] [v|n|t1 t2] //=.
case: ifPn => vv' /andP[] /andP[] Hfv Hv2 Hs.
  move/eqP in vv'; subst v'.
  case Ht': bt_expand_head => [x|n|t1 t2] //.
  case: ifPn => // xv.
  by rewrite -Ht' IH.
case Hv: bt_expand_head => [x|n|t1 t2] //.
rewrite -Hv.
case: ifPn => xv'; last exact: IH.
rewrite (eqP xv') in Hv.
move: (bt_expand_head_in s (btVar v)).
move: Hv2; rewrite inE negb_or => /andP[Hv't' Hv2].
rewrite Hv inE (negbTE Hv2) orbF => /eqP [] /esym /eqP.
by rewrite (negbTE vv').
Qed.

Lemma sorted_subst_shrink (s1 s2 : substType) vt :
  sorted_subst (s1 ++ vt :: s2) -> sorted_subst (s1 ++ s2).
Proof.
case: vt => v t.
elim: s1 => /= [|[v' t'] s1 IH] /andP[] // /andP[].
rewrite /unzip1 /unzip2 /= inE !map_cat !mem_cat 4!negb_or => /andP[] -> /=.
rewrite 3!inE mem_cat 4!negb_or => /andP[vv'] Hv1 /= /andP[->] /andP[->].
move=> /andP[v't] Hv2 /= Hs.
by rewrite Hv1 Hv2 IH // bt_expand_head_cat.
Qed.

Lemma subst_list_cat s1 s2 t :
  subst_list (s1 ++ s2) t = subst_list s2 (subst_list s1 t).
Proof. exact: foldl_cat. Qed.

Fixpoint subst_par (s : substType) t :=
  match t with
  | btVar v => head t [seq x.2 | x <- s & x.1 == v]
  | btInt n => t
  | btNode t1 t2 => btNode (subst_par s t1) (subst_par s t2)
  end.

Lemma subst_par_nil t : subst_par nil t = t.
Proof. by elim: t => //= ? -> ? ->. Qed.

Lemma idempotent_subst_cat s1 s2 :
  uniq (unzip1 (s1 ++ s2)) ->
  idempotent_subst (s1 ++ s2) ->
  idempotent_subst s1 /\ idempotent_subst s2.
Proof.
move=> Hu Hid.
split.
- apply/allP => /= x Hx.
  apply/allP => /= y Hy.
  move/allP/(_ x): Hid.
  rewrite /unzip1 map_cat mem_cat Hx => /(_ isT) /allP/(_ y).
  rewrite /unzip1 mem_cat Hy /= => /(_ isT).
  rewrite subst_list_cat.
  apply: contra.
  set t := subst_list s1 _.
  apply: free_vars_keep.
  move: Hu.
  rewrite /unzip1 map_cat cat_uniq => /andP[_] /andP[] Hhas _.
  apply: contra Hhas => Hy'.
  by apply/hasP; exists y.
- apply/allP => /= x Hx.
  apply/allP => /= y Hy.
  move/allP/(_ x): Hid.
  rewrite /unzip1 map_cat mem_cat Hx orbT => /(_ isT) /allP/(_ y).
  rewrite /unzip1 mem_cat Hy orbT => /(_ isT).
  rewrite subst_list_cat (subst_list_same (t:=btVar x)) //.
  rewrite all_notinE /= andbT.
  move: Hu.
  rewrite /unzip1 map_cat cat_uniq => /andP[_] /andP[] Hhas _.
  apply: contra Hhas => Hx'.
  by apply/hasP; exists x.
Qed.

Lemma idempotent_subst_free_vars s v t0 t :
  idempotent_subst ((v,t0) :: s) ->
  t \in t0 :: unzip2 s ->
  uniq (v :: unzip1 s) ->
  v \notin free_vars t.
Proof.
move=> Hid.
rewrite inE => /orP[/eqP -> | Ht].
  move=> /= /andP[Hv] _.
  move/allP/(_ v): Hid.
  rewrite inE /= !eqxx => /(_ isT) /andP[] /[swap] _.
  apply: contra.
  exact: free_vars_keep.
pose n := find (fun x => x.2 == t) s.
move: Ht (Ht) Hid.
rewrite -{1}has_pred1 has_map => Ht.
case: (split_find Ht) => x s1 s2 Hx Hpre {}Ht Hid Hu.
move: Hid.
rewrite -cat1s catA => /idempotent_subst_cat.
rewrite -catA Hu => /(_ isT) [].
move/allP/(_ x.1).
rewrite -cats1 /unzip1 !map_cat !mem_cat mem_seq1 inE eqxx !orbT => /(_ isT).
case/andP => /[swap] _.
rewrite catA subst_list_cat (subst_list_same (t:=btVar _)).
  by rewrite /= eqxx (eqP Hx).
rewrite all_notinE /=.
move: Hu; rewrite -cat1s /unzip1 map_cat catA cat_uniq => /andP[].
by rewrite map_rcons -cats1 catA cats1 rcons_uniq => /andP[] ->.
Qed.

Lemma filter_unzip1 (s : substType) v :
  v \notin unzip1 s ->
  [seq x <- s | x.1 == v] = [::].
Proof.
move=> Hv.
apply/eqP/negP => /negP.
rewrite -has_filter => /hasP[/= [v' t']] /= /[swap] /eqP -> /(map_f fst) H.
by rewrite H in Hv.
Qed.

Lemma subst_par_out (s : substType) t :
  all (fun x => x \notin free_vars t) (unzip1 s) ->
  subst_par s t = t.
Proof.
elim: t => // [v | t1 IH1 t2 IH2] /=.
  rewrite all_notinE /= andbT => Hv.
  by rewrite filter_unzip1.
rewrite all_notinE all_cat /= => /andP[Ht1 Ht2].
by rewrite IH1 (all_notinE,IH2) // all_notinE.
Qed.

Lemma subst_par_cat (s1 s2 : substType) t :
  all (fun x => all (fun t => x \notin free_vars t) (unzip2 s1)) (unzip1 s2) ->
  subst_par (s1 ++ s2) t = subst_par s2 (subst_par s1 t).
Proof.
move=> /= Hall.
elim: t => // [v | t1 IH1 t2 IH2] /=; last by rewrite IH1 IH2.
elim: s1 Hall => // -[v' t'] s1 IH /= Hall.
case: ifPn => [/eqP -> /= | vv'].
  rewrite subst_par_out //.
  by apply: sub_all Hall => w /andP[].
apply: IH.
by apply: sub_all Hall => w /andP[].
Qed.

Lemma subst_par_catC (s1 s2 : substType) t :
  uniq (unzip1 (s1 ++ s2)) ->
  subst_par (s1 ++ s2) t = subst_par (s2 ++ s1) t.
Proof.
move=> Hu.
elim: t => // [v | t1 IH1 t2 IH2] /=; last by rewrite IH1 IH2.
elim: s1 Hu => [|[v' t'] s1 IH] /=.
  by rewrite cats0.
case: ifPn => [/eqP -> /= | vv'] /andP[Hv' Hu].
  rewrite filter_cat filter_unzip1 /= ?eqxx //.
  by move: Hv'; rewrite [unzip1 _]map_cat mem_cat negb_or => /andP[].
by rewrite IH // 2!filter_cat /= (negbTE vv').
Qed.

Lemma subst_par1 v t t' : subst_par [:: (v, t)] t' = subst v t t'.
Proof. elim: t' => //[?|? IH1 ? IH2]/=; by [case: ifP | rewrite IH1 IH2]. Qed.

Fixpoint pull_subst (s : substType) :=
  match s with
  | nil => nil
  | (v,t) :: s' => let s'' := pull_subst s' in (v, subst_par s'' t) :: s''
  end.

Lemma dom_pull_subst s : unzip1 (pull_subst s) = unzip1 s.
Proof. by elim: s => // -[v t] s /= ->. Qed.

Lemma subst_par_pull_subst (s : substType) t :
  acyclic_subst s ->
  idempotent_subst s ->
  uniq (unzip1 s) ->
  subst_par (pull_subst s) t = subst_list s t.
Proof.
elim: s t => [|[v' t'] s IH] t Hac Hid Hu /=.
  by rewrite subst_par_nil.
have Hac' : acyclic_subst s.
  apply: acyclic_subst_sub Hac => x.
  by rewrite inE orbC => ->.
have Hid' : idempotent_subst s.
  rewrite -cat1s in Hid Hu.
  by case: (idempotent_subst_cat Hu Hid).
have Hu' : uniq (unzip1 s) by case/andP: Hu.
elim: t => [v|n|t1 IH1 t2 IH2] /=.
- case: ifPn => [/eqP -> | vv'] /=; by rewrite -IH.
- by rewrite subst_btInt.
- by rewrite subst_btNode IH1 IH2.
Qed.

Lemma all_swap (A B : eqType) (r : A -> B -> bool) (s1 : seq A) (s2 : seq B) :
  all (fun x => all (fun y => r x y) s2) s1 =
  all (fun y => all (fun x => r x y) s1) s2.
Proof.
case/boolP: (all _ s2) => H.
  apply/allP => x Hx.
  apply/allP => y Hy.
  by move/allP/(_ _ Hy)/allP/(_ _ Hx): H.
apply: contraNF H => H.
apply/allP => y Hy.
apply/allP => x Hx.
by move/allP/(_ _ Hx)/allP/(_ _ Hy): H.
Qed.

Lemma idempotent_pull_subst s :
  acyclic_subst s ->
  idempotent_subst s ->
  uniq (unzip1 s) ->
  idempotent_subst' (pull_subst s).
Proof.
elim: s => [|[v t] s IH] // Hac Hid Hu.
have Hac' : acyclic_subst s.
  apply: acyclic_subst_sub Hac => x.
  by rewrite inE orbC => ->.
have Hid' : idempotent_subst s.
  rewrite -cat1s in Hid Hu.
  by case: (idempotent_subst_cat Hu Hid).
have Hu' : uniq (unzip1 s) by case/andP: Hu.
apply/allP => /= x.
move: (Hid).
rewrite /idempotent_subst all_swap => /allP/(_ v).
rewrite /= !inE eqxx => /(_ isT) /andP[].
case/boolP: (x == v) => [/eqP -> | xv Hv] /=.
  rewrite subst_par_pull_subst // => -> {}Hid /= _.
  move: Hu => /= /andP[].
  elim: s {Hac Hu' IH} Hac' Hid' Hid => // -[v' t'] s IH Hac' Hid' Hfv Hv Hu'.
  have Hac : acyclic_subst s.
    apply: acyclic_subst_sub Hac' => ?.
    by rewrite inE orbC => ->.
  have Hid : idempotent_subst s.
    rewrite -cat1s in Hid' Hu'.
    by case: (idempotent_subst_cat Hu' Hid').
  have Hu : uniq (unzip1 s) by case/andP: Hu'.
  move: Hv Hfv => /=.
  rewrite inE negb_or => /andP[] /negbTE -> Hv /andP[] /=.
  rewrite eqxx.
  rewrite /= subst_par_pull_subst // => -> /= Hfv.
  apply: IH => //.
  apply/allP => y Hy.
  case: ifPn => vy.
    by rewrite (eqP vy) Hy in Hv.
  move/allP/(_ _ Hy): Hfv.
  rewrite (negbTE vy) /=.
  case: ifPn => // /eqP v'y.
  by rewrite /= v'y Hy in Hu'.
rewrite dom_pull_subst => Hfv Hx.
move: (Hid).
rewrite /idempotent_subst all_swap => /allP/(_ x).
rewrite /= inE eqxx (negbTE xv) Hx => /(_ isT) /andP[].
rewrite subst_par_pull_subst // => -> /= Hfv'.
move/allP/(_ x): (IH Hac' Hid' Hu') => -> //.
by rewrite dom_pull_subst.
Qed.

Lemma acyclic_subst_listC s1 s2 t :
  acyclic_subst (s1 ++ s2) ->
  uniq (unzip1 (s1 ++ s2)) ->
  subst_list (push_subst (s1 ++ s2)) t =
  subst_list (push_subst (s2 ++ s1)) t.
Proof.
rewrite !push_subst_cat !subst_list_cat.
Abort.

Lemma subst_list_bt_expand_head s t :
  acyclic_subst s ->
  subst_list (push_subst s) t = subst_list (push_subst s) (bt_expand_head s t).
Proof.
rewrite push_substE.
rewrite -{1}(cat0s s).
rewrite -(cat0s (push_subst' _ _)).
move: idempotent_subst_nil.
set s0 := nil.
elim: s s0 t => [|[v t'] s IH] s0 [n|n|t1 t2] //= Hid Hac.
rewrite eq_sym -cat1s catA cats1.
have [-> | nv] := eqVneq n v; last first.
  apply: IH.
  - rewrite -cats1 -/(push_subst' s0 [:: (v, t')]).
    rewrite acyclic_idempotent_push_subst' //.
    apply: acyclic_subst_sub Hac => x Hx.
    by rewrite -cat1s catA mem_cat Hx.
  - admit.
case: t' Hac => [v'|n'|t1 t2] Hac; first last.
- rewrite bt_expand_head_not_btVar //=.
  rewrite -!cats1 !subst_list_cat.
  rewrite subst_list_same; last first.
    rewrite dom_push_subst'.
    
 subst_same //. -free_varsE.
    apply: contra (Hac v nil) => /=.
    by rewrite eqxx /= => ->.
  - by rewrite bt_expand_head_not_btVar.
  
Abort.

Lemma cenv_rcons A vs v (k : _ -> M A) :
  (cenv (rcons vs v) >>= k) = do r <- cenv vs; add_var r v >> k r.
Proof.
rewrite -cats1 cenv_cat bindA.
apply: eq_bind => r /=.
by rewrite add_var_skipE bindA bindretf.
Qed.

Lemma csubst_list_cat r s1 s2 :
  csubst_list r (s1 ++ s2) = csubst_list r s1 >> csubst_list r s2.
Proof. by rewrite /csubst_list map_cat foldr_cat foldr_bindA. Qed.

Lemma csubst_list_seq1 r v t :
  csubst_list r [:: (v,t)] = csubst r v t.
Proof. exact: bindmskip. Qed.

Lemma sorted_subst_notin_unzip1 s v v' :
  sorted_subst (rcons s (v, btVar v')) -> v' \notin rcons (unzip1 s) v.
Proof.
rewrite -cats1; elim: s => //= [|[v1 t1] s IH].
 rewrite andbT; apply: contra.
  by rewrite !inE => /eqP ->; rewrite eqxx.
rewrite (in_cons _ _ v') negb_or (andbC (_ != _)) => /andP[] /= /andP[_] Hv1 /IH -> /=.
apply: contra Hv1 => /eqP <-.
by rewrite inE /unzip2 map_cat /= mem_cat inE eqxx !orbT.
Qed.

Lemma csubst_list_expand_head0 A vs he t s s' (k : _ -> _ -> M A) :
  not_btVar t ->
  (do r <- cenv vs;
   csubst_list r s >>
   do u <- repr_btree r t;
   expand_head he u >>= k r) =
  (do r <- cenv vs;
   csubst_list r s >>
   (repr_btree r (bt_expand_head s' t) >>= k r)).
Proof.
move=> nvar.
apply: eq_bind => r.
apply: eq_bind => _.
rewrite bt_expand_head_not_btVar //.
rewrite repr_btree_not_btVar // [RHS]repr_btree_not_btVar //.
apply: eq_bind => u.
by under bind_ext_guard => Hu do rewrite expand_head_not_uLink // bindretf.
Qed.

Lemma csubst_list_expand_head A vs he t (s : substType) (k : _ -> _ -> M A):
  size s < he ->
  sorted_subst s ->
  {subset free_vars_subst s <= vs} ->
  (do r <- cenv vs;
   csubst_list r s >>
   do u <- repr_btree r t;
   expand_head he u >>= k r) =
  (do r <- cenv vs;
   csubst_list r s >>
   (repr_btree r (bt_expand_head s t) >>= k r)).
Proof.
case/boolP: (not_btVar t); first by move=> *; apply: csubst_list_expand_head0.
case Ht: t => [v||] // _.
rewrite -Ht.
pose s0 : substType := [::].
have {-1 6}-> : s = s0 ++ s by [].
have: v \notin unzip1 s0 by [].
elim: s s0 he v t Ht => [|[v' t'] s IH /=] s0 he v t Ht Hnin.
  rewrite cats0 Ht bt_expand_notin => // He Hsorted Hsub /=.
  case: he He => //= he _.
  under eq_bind => r do
    (rewrite bindA; under (eq_bind (add_var r v)) do rewrite bindretf bindA).
  rewrite cenv_has_vars.
  under eq_bind => r do
    rewrite -(add_varD r v (fun l l => _ >>= _)) csubst_list_add_varC //.
  rewrite -cenv_has_vars -cenv_rcons cenv_has_vars.
  under eq_bind => r.
    rewrite -get_var_csubst_listC //; first over.
    move=> x; rewrite inE mem_rcons inE => /orP[-> // | /Hsub ->].
    by rewrite orbT.
  rewrite -cenv_has_vars cenv_add_var_get cenv_rcons cenv_has_vars.
  under eq_bind do rewrite add_varD -csubst_list_add_varC //.
  under [RHS]eq_bind => r do rewrite bindA.
  by rewrite -cenv_has_vars.
move => He Hsort Hsub.
case/boolP: (v == v') => vv'; last first.
  have H1 : v \notin unzip1 (rcons s0 (v', t')).
    by rewrite -cats1 /unzip1 map_cat /= mem_cat inE negb_or Hnin.
  move: (IH (rcons s0 (v', t')) he v t Ht H1 (ltnW He)).
  by rewrite -cats1 -catA Ht (negbTE vv') /= => /(_ Hsort) ->.
move/eqP in vv'; subst v'.
have Hvns : v \notin unzip1 s.
  by move/sorted_subst_catr: Hsort => /= /andP[] /andP[].
have Hfvs0 : {subset free_vars_subst s0 <= vs}.
  apply: sub_trans Hsub; apply: free_vars_subst_subset => x Hx.
  by rewrite mem_cat Hx.
have Hfvt : {subset v :: free_vars t' <= vs}.
  apply: sub_trans Hsub => x Hx.
  rewrite /free_vars_subst mem_cat /unzip1 map_cat /= mem_cat inE.
  rewrite /unzip2 !map_cat /= flatten_cat /= !mem_cat.
  by move: Hx; rewrite inE => /orP[] ->; rewrite !orbT.
have Hfvs : {subset v :: free_vars_subst s <= vs}.
  apply: sub_trans Hsub => x; rewrite inE => /orP[].
    rewrite /free_vars_subst /unzip1 map_cat /= !mem_cat inE => ->.
    by rewrite !orbT.
  by apply: free_vars_subst_subset => y Hy; rewrite mem_cat inE Hy !orbT.
rewrite cenv_has_vars.
case: he He => // he He /=.
rewrite Ht eqxx /=.
under eq_bind => r.
  rewrite -cat1s !csubst_list_cat csubst_list_seq1 2!bindA.
  rewrite -bindA has_vars_csubst_listC //.
  rewrite 2!bindA -[X in _ >> ( _ >> X)]bindA has_vars_csubstC // 3!bindA.
  under (eq_bind (add_var r v)) do rewrite bindretf bindA.
  rewrite -get_var_csubst_listC //.
  rewrite -2![X in _ >> ( _ >> X)]bindA (bindA (has_vars _ _)).
  rewrite -has_vars_csubstC // bindA.
  rewrite csubst_get_var // csubst_add_varC // -add_var_skipE.
  rewrite -[X in _ >> (_ >> X)]bindA has_vars_add_var_skip; last first.
    by rewrite Hfvt // inE eqxx.
  rewrite -[X in _ >> (_ >> X)]bindA.
  rewrite has_vars_csubstC // 2!bindA -csubst_list_repr_btreeC; first last.
    by apply: sub_trans Hfvs => x Hx; rewrite inE Hx orbT.
  rewrite -2![X in _ >> (_ >> X)]bindA (bindA (has_vars r _)).
  rewrite -has_vars_csubstC // bindA.
  rewrite -2!bindA (bindA (has_vars r _)) -has_vars_csubst_listC // bindA.
  rewrite -2![X in _ >> X]bindA.
  rewrite -csubst_list_seq1 -csubst_list_cat cats1 -csubst_list_cat.
  over.
rewrite -cat1s catA cats1 -cenv_has_vars.
case/boolP: (not_btVar t'); first exact: csubst_list_expand_head0.
case Ht': t' => [v'||] // _.
rewrite (IH _ _ v') //; try by rewrite -cats1 -catA /= -Ht'.
rewrite -cats1 [unzip1 _]map_cat /= cats1.
apply/sorted_subst_notin_unzip1/sorted_subst_catl.
rewrite -cats1 -catA -Ht'; exact: Hsort.
Qed.

Lemma unifysubst h h' he vs l (s0 s : substType) :
  h > size (vars_pairs (map (subst_pair (push_subst s0)) l)) ->
  h' > bt_size_pairs (map (subst_pair (push_subst s0 ++ s)) l) ->
  he > size s0 ->
  {subset free_vars_subst s0 <= vs} ->
  {subset free_vars_pairs l <= vs} ->
  bt_unify2 h (map (subst_pair (push_subst s0)) l) = write M' s ->
  exists2 s',
    push_subst s' = s &
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= (unify1 h' he)
    ) = cenv vs >>= csubst_list^~ (s0 ++ s').
Proof.
  elim: h h' he vs l s0 s => // h IHh.
  elim/ltn_ind => h' IHh' he vs [/=|[t1 t2] l] s0 s.
    case: h' IHh' => // h' IHh' _ _ He Hfv _ [].
    rewrite [RHS]cats0 => <-.
    exists nil => //.
    under eq_bind do rewrite /repr_btree_pairs bindA !bindretf /= -foldr_bindA.
    by rewrite cats0.
  move=> Hh Hh' He Hfv Hvp.
  under eq_bind => vars do rewrite bindA repr_btree_cons /=.
  case: h' Hh' IHh' => // h' Hh' IHh' /= Hbt.
  rewrite cenv_has_vars.
  under eq_bind => r.
    rewrite -bindA has_vars_csubst_listC // 2!bindA.
    rewrite has_vars_repr_btreeC.
    under (eq_bind (repr_btree r t1)) => u1.
      rewrite -repr_btree_repr_btree_listC; last admit.
      rewrite has_vars_repr_btreeC.
      under (eq_bind (repr_btree r t2)) => u2.
        rewrite has_vars_repr_btree_listC.
        under (eq_bind (repr_btree_list r _)) => ul1.
          rewrite repr_btree_list_expand_headC; last admit.
          rewrite has_vars_expand_headC.
          under (eq_bind (expand_head _ _)) do
            (rewrite repr_btree_list_expand_headC; last admit).
          rewrite -has_vars_expand_headC.
          over.
        rewrite -has_vars_repr_btree_listC repr_btree_list_expand_headC;
          last admit.
        rewrite has_vars_expand_headC.
        under (eq_bind (expand_head _ _)) do
          (rewrite repr_btree_list_expand_headC; last admit).
        rewrite -has_vars_expand_headC.
        over.
      rewrite -has_vars_repr_btreeC.
      rewrite repr_btree_expand_headC; last admit.
      over.
    rewrite -has_vars_repr_btreeC -2!bindA.
    rewrite (bindA (has_vars _ _)) -has_vars_csubst_listC // bindA.
    over.
  rewrite -cenv_has_vars.
  rewrite csubst_list_expand_head.
  rewrite cenv_has_vars.
  under eq_bind => r.
    rewrite -bindA has_vars_csubst_listC // 2!bindA.
    rewrite repr_btreeC; last admit.
    rewrite has_vars_repr_btreeC.
    under (eq_bind (repr_btree r t2)) do
      (rewrite repr_btree_expand_headC; last admit).
    rewrite -has_vars_repr_btreeC -2!bindA.
    rewrite (bindA (has_vars _ _)) -has_vars_csubst_listC // bindA.
    over.
  rewrite -cenv_has_vars csubst_list_expand_head.
  case Ht1: (bt_expand_head s0 t1) => [n1|n1|t11 t12];
  case Ht2: (bt_expand_head s0 t2) => [n2|n2|t21 t22] /=.
- under eq_bind => r.
    rewrite bindA.
    under (eq_bind (add_var _ _)) do
      (rewrite bindretf bindA; under eq_bind do rewrite bindretf).
    over.
    case/boolP: (n1 == n2) => n1n2.
      rewrite -(eqP n1n2).
      rewrite cenv_has_vars.
      under eq_bind => r.
        rewrite -bindA has_vars_csubst_listC // 2!bindA.
        rewrite add_varD.
        under (eq_bind (add_var r n1)) do rewrite eqxx.
        rewrite -2!bindA (bindA (has_vars _ _)) -has_vars_csubst_listC // bindA.
        rewrite csubst_list_add_varC //.
        rewrite -add_var_skipE -bindA has_vars_add_var_skip; last first.
          move: (bt_expand_head_in s0 t1).
          rewrite Ht1 inE => /orP[] Hn1.
            rewrite Hvp // -(eqP Hn1) /=.
            by rewrite mem_cat inE eqxx.
          rewrite Hfv // mem_cat.
          apply/orP; right; apply/flattenP; exists (free_vars (btVar n1)).
            exact: map_f.
          by rewrite inE.
        rewrite -repr_btree_pairs_zip -(bindA (csubst_list _ _)); over.
      rewrite -cenv_has_vars.
      apply IHh' => //=.
      + move: Hh => /=.
        by apply: leq_trans; rewrite ltnS size_union2.
      + move: Hh' => /=.
        rewrite /bt_size_pairs /= !ltnS.
        apply: leq_trans.
        rewrite -add1n leq_add //.
        by case: subst_list.
      + apply: sub_trans Hvp => x.
        by rewrite /free_vars_pairs /= !mem_cat => /orP[] ->; rewrite !orbT.
      + rewrite -Hbt {3 5}/subst_pair /=.
  admit.
- admit.
- under eq_bind do
    (rewrite bindretf bindA; under (eq_bind (add_var _ _)) do rewrite bindretf).
  admit.
- under eq_bind => r.
    rewrite bindA.
    under (eq_bind (repr_btree _ _)) => u1.
      rewrite bindA.
      under eq_bind do rewrite bindretf bindA.
      under eq_bind do under eq_bind do rewrite bindretf.
      over.
    over.
  admit.
- under eq_bind do
    (rewrite bindA; under (eq_bind (add_var _ _)) do rewrite !bindretf).
  admit.
- under eq_bind do rewrite !bindretf.
  admit.
Abort.
(*
  destruct t1, t2.
(* LinkLink *)
- move => Hu /=.
  under eq_bind => vars.
    rewrite bindA.
    under [X in _ >> X]eq_bind => x.
      rewrite bindretf.
      under eq_bind => l1.
        rewrite bindA.
        under eq_bind => x' do rewrite bindretf.
      over.
    over.
  over.
  have [->|Hneq] := eqVneq v v0.
    admit.
  admit.
  (* LinkInt *)
- move => Hu /=.
  move: (ltnm0 He) => He'.
  under eq_bind => vars.
    rewrite bindA.
    under [X in _ >> X]eq_bind => x.
      rewrite bindretf.
      under eq_bind => l1.
        rewrite bindretf (expand_head_not_uLink _ (u:=uInt n)) => //.
        under eq_bind => l2 do under eq_bind => t1 do rewrite bindretf.
      over.
    over.
  over.
  admit.
  (* LinkNode *)
- move => Hu /=.
  move: (ltnm0 He) => He'.
  under eq_bind => vars.
    rewrite bindA.
    under [X in _ >> X]eq_bind => x.
      rewrite bindretf.
      under eq_bind => l1.
        rewrite bindA.
        under eq_bind => t0.
          rewrite bindA.
          under eq_bind => t1.
            rewrite bindretf (expand_head_not_uLink _ (u:=uNode _ _)) => //.
            under eq_bind => l2 do under eq_bind => t2 do rewrite bindretf.
          over.
        over.
      over.
    over.
  over.
  admit.
  (* IntLink *)
- move => Hu /=.
  move: (ltnm0 He) => He'.
  under eq_bind => vars.
    rewrite bindretf expand_head_not_uLink => //.
    under [X in _ >> X]eq_bind => l1.
      rewrite bindA.
      under eq_bind => x.
        rewrite bindretf.
        under eq_bind => l2 do rewrite bindretf.
      over.
    over.
  over.
  admit.
  (* IntInt *)
- have [-> Hu|eqnn0 /=] := eqVneq n n0;
    last by rewrite /subst_pair !subst_btInt /= (negPf eqnn0).
  have H1: size (vars_pairs [seq subst_pair (push_subst s0) i | i <- l]) < h.+1
    by rewrite /= 2!subst_btInt /vars /= in Hh.
  have H2: bt_size_pairs [seq subst_pair (push_subst s0 ++ s) i | i <- l] < h'.
    rewrite /= /subst_pair 2!subst_btInt /bt_size_pairs /= ltnS add1n add2n in Hh'.
    exact: leq_ltn_trans.
  have H3: bt_unify2 h.+1 [seq subst_pair (push_subst s0) i | i <- l] = write M' s.
    move: Hu => <-.
    rewrite /= /subst_pair !subst_btInt.
    rewrite [bt_unify1]lock /bt_size_pairs /= add1n add2n.
    rewrite -{-1}lock [_.+2]lock !addn1 /= eqxx -!lock.
    exact: unify1_eq.
  have Hm: h' < h'.+1 by [].
  move: (IHh' _ Hm he vs l s0 s H1 H2 He H3) => [s' ? IH].
  exists s' => //.
  rewrite /= in IH.
  rewrite -IH [unify1]lock /=.
  apply: eq_bind => vars.
  rewrite [RHS]bindA.
  apply: eq_bind => _.
  rewrite bindretf [RHS]bindA.
  apply: eq_bind => l1.
  rewrite bindretf [RHS]bindA.
  apply: eq_bind => l2.
  rewrite bindretf -lock /=.
  move: (ltnm0 He) => He'.
  rewrite expand_head_not_uLink => //.
  by rewrite 2!bindretf eqxx.
  (* IntNode *)
- by rewrite /subst_pair /= subst_btInt subst_btNode.
  (* NodeLink *)
- move => Hu /=.
  move: (ltnm0 He) => He'.
  under eq_bind => vars.
    rewrite bindA.
    under [X in _ >> X]eq_bind => t0.
      rewrite bindA.
      under eq_bind => t1.
        rewrite bindretf expand_head_not_uLink => //.
        under eq_bind => l1.
          rewrite bindA.
          under eq_bind => x.
            rewrite bindretf.
            under eq_bind => l2 do rewrite bindretf.
          over.
        over.
      over.
    over.
  over.
  admit.
  (* NodeInt *)
- by rewrite /subst_pair /= subst_btNode subst_btInt.
  (* NodeNode *)
- move => Hu.
  rewrite /= /subst_pair !subst_btNode /= -addnE in Hu.
  have H1:
    size (vars_pairs
      [seq subst_pair (push_subst s0) i
        | i <- [:: (t1_1, t2_1), (t1_2, t2_2) & l]]) < h.+1.
    rewrite /= /subst_pair !subst_btNode in Hh.
    by rewrite -size_vars_pairs_btNode.
  have H2:
    bt_size_pairs
      [seq subst_pair (push_subst s0 ++ s) i
        | i <- [:: (t1_1, t2_1), (t1_2, t2_2) & l]] < h'.
    move: Hh'.
    rewrite /bt_size_pairs /= 2!subst_btNode /= !addnA (addnAC (size_tree _)) !(addn1, add1n) ltnS.
    exact: leq_ltn_trans.
  have H3:
    bt_unify2 h.+1
      [seq subst_pair (push_subst s0) i
        | i <- [:: (t1_1, t2_1), (t1_2, t2_2) & l]] =
    write M' s.
    rewrite -Hu.
    apply: unify1_eq => //=; last first.
      by rewrite addn1.
    by rewrite /bt_size_pairs /= !addnA (addnAC (size_tree _)) !(addn1, add1n).
  have Hm: h' < h'.+1 by [].
  move: (IHh' _ Hm he vs ((t1_1, t2_1) :: (t1_2, t2_2) :: l) s0 s H1  H2 He H3) => [s' ? IH].
  exists s' => //.
  rewrite -IH.
  apply: eq_bind => vars.
  rewrite [unify1]lock.
  rewrite [RHS]bindA !repr_btree_cons /=.
  apply: eq_bind => _.
  rewrite bindA.
  apply: eq_bind => tl1.
  rewrite bindA [RHS]bindA.
  apply: eq_bind => tl2.
  rewrite bindretf [RHS]bindA.
  apply: eq_bind => l1.
  rewrite bindretf bindA.
  apply: eq_bind => tr1.
  rewrite bindA [RHS]bindA.
  apply: eq_bind => tr2.
  rewrite bindretf [RHS]bindA.
  apply: eq_bind => l2.
  rewrite bindretf -lock /=.
  move: (ltnm0 He) => He'.
  rewrite !expand_head_not_uLink => //.
  by rewrite 2!bindretf.
Abort.
*)
End equiv.

End Unification.

End CoqTypeNat.
