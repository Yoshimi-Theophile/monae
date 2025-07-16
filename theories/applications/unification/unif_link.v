(* Require Import ZArith. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib.
Require Import action_monad action_model unification.unif_actionrun.

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

Fixpoint size_uterm (t : uterm) : nat :=
  if t is uNode t1 t2 then 1 + size_uterm t1 + size_uterm t2 else 1.

Definition size_pairs (l : constr_list) :=
  sumn [seq size_uterm p.1 + size_uterm p.2 | p <- l].

Fixpoint free_vars bt :=
  match bt with
  | btVar n => [:: n]
  | btInt _ => [::]
  | btNode bt1 bt2 => free_vars bt1 ++ free_vars bt2
  end.
End Definitions.

Section monad_lemmas.

(* Override a TypedStoreMonad Lemma *)
Lemma cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2)
  (s1 : coq_type N T1) (A : UU0) (k : coq_type N T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> (cget r2 >>= k) =
  cget r2 >>= (fun v : coq_type N T2 => cput r1 s1 >> k v).
Proof. by move=> *; rewrite -bindA cputgetC. Qed.

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

Fixpoint repr_btree_pairs (l : list (btree * btree)) : M (list (uterm * uterm)) :=
  match l with
  | nil => Ret nil
  | (bt1, bt2) :: r =>
    do t1 <- repr_btree bt1;
    do t2 <- repr_btree bt2;
    do r' <- repr_btree_pairs r;
    Ret ((t1, t2) :: r')
  end.

Lemma repr_btree_cons A bt1 bt2 l (f : _ -> M A):
  repr_btree_pairs ((bt1, bt2) :: l) >>= f =
  do t1 <- repr_btree bt1;
  do t2 <- repr_btree bt2;
  do l' <- repr_btree_pairs l;
  f ((t1, t2) :: l').
Proof.
under [RHS]eq_bind => t1.
  under eq_bind => t2.
    under eq_bind => l'.
      rewrite -bindretf.
    over. rewrite -bindA.
  over. rewrite -bindA.
over. by rewrite -bindA.
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
      vars m n (k : _ -> M A) :
  nth None vars n ->
  cput r vars >> (add_var r n >>= fun v => add_var_skip r m >> k v) =
  cput r vars >> (add_var_skip r m >> (add_var r n >>= k)).
Proof.
move=> Hn.
rewrite bindA [in RHS]bindA !cputget.
case Hnth: nth Hn => [v|] // _.
rewrite bindretf 2!bindA cputget.
case Hnth': nth => [v'|] /=.
  by rewrite !bindskipf cputget Hnth bindretf.
apply: eq_bind => _.
rewrite 2!bindA.
apply: eq_bind => v'.
rewrite cputget nth_set_nth /=.
case: ifPn => nm.
  by rewrite (eqP nm) Hnth' in Hnth.
by rewrite Hnth bindretf.
Qed.

Lemma add_varC A (r : loc (ml_list (ml_option (ml_ref ml_uvar))))
      m n (k : _ -> M A) :
  add_var r n >>= (fun v => add_var_skip r m >> k v) =
  add_var r n >> (add_var_skip r m >> (add_var r n >>= k)).
Proof.
rewrite -[LHS](add_varD r n (fun _ _ => _ >>= _)).
rewrite {1 3}/add_var.
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
rewrite bindA add_varC -IH -add_varC.
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
  rewrite -(bindretf r (fun=>skip)) -(bindskipf (Ret r)) -!bindA -/(cchk r).
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
            -!bindA -/(cchk r).
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

Lemma cenv_var vs n k :
  n \in vs ->
  (cenv vs >>= fun r => cget r >>= fun vars => if nth None vars n is Some v then cget v else k r vars) =
  cenv vs >> Ret (uVar n).
Proof.
  move => Hin.
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
    rewrite -cputchk !bindA !bindskipf.
    apply eq_bind => _.
    rewrite -(cnewput ml_uvar (uVar n)).
    rewrite -[in RHS](cnewput ml_uvar (uVar n)).
    apply: cgetnewE => l Hl.
    elim: vs ws {IH Hws} => /= [|b vs IH] ws.
      rewrite !bindretf !cputget nth_set_nth /= eqxx.
      by rewrite -cgetret cputgetC // cputget.
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
      rewrite -(bindskipf (k x)) -bindA add_var_skipE.
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

Lemma repr_btree_ok vs bt : represents (cenv vs >>= repr_btree^~ bt) bt.
Proof.
elim: bt vs => /= [n | n | bt1 IH1 bt2 IH2] vs.
- have Hrun : (crun (cenv vs >>= fun x => add_var x n)).
    rewrite -crunmskip bindA.
    under eq_bind => r.
      rewrite add_var_skipE -[add_var_skip r n]bindmskip -[skip](bindretf r).
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
    rewrite /add_var bindA.
    under eq_bind do (rewrite !bindA; under eq_bind do rewrite bindifsomeret).
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
  else fail.

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

Section unify1.
Variable expand_head : uterm -> M uterm.
Variable occurs_ref : @loc _ nat ml_uvar -> uterm -> M unit.
Variable unify2 : constr_list -> M unit.

Definition unify_link (v : loc ml_uvar) t l : M unit :=
  cput v (uTerm t) >> unify2 l.

Fixpoint unify1 (h : nat) (l : constr_list) : M unit :=
  if h is h.+1 then
    if l is (t1, t2) :: l' then
      do t1 <- expand_head t1;
      do t2 <- expand_head t2;
      match t1, t2 with
      | uInt m, uInt n =>
          if m == n then unify1 h l' else fail
      | uNode tl1 tl2, uNode tr1 tr2 =>
          unify1 h ((tl1, tr1) :: (tl2, tr2) :: l')
      | uLink v1, uLink v2 =>
          if loc_id v1 == loc_id v2 then unify1 h l'
          else unify_link v1 t2 l'
      | uLink v1, _ =>
          do _ <- occurs_ref v1 t2; unify_link v1 t2 l'
      | _, uLink v2 =>
          do _ <- occurs_ref v2 t1; unify_link v2 t1 l'
      | _, _ => fail
      end
    else Ret tt
else fail.
End unify1.

Section unify2.
Variable vars_count : nat.

Fixpoint unify2 h l : M unit :=
  if h is h.+1 then
    unify1
    (expand_head vars_count)
    (occurs_ref vars_count)
    (unify2 h)
    (size_pairs l + 1) l
  else fail.
End unify2.

Definition unify h t1 t2 :=
  let l := [:: (t1, t2)] in
  unify2 h (h.+1) l.

End unify.


Section equiv.

Variable (N' : exceptMonad) (M' : actionRunFailMonad op N').

Local Notation bt_unify2 := (unif_actionrun.unify2 M').
Local Notation bt_unify1 := (unif_actionrun.unify1 M').
Local Notation bt_size_pairs := unif_actionrun.size_pairs.

Lemma expand_same A h t (k : _ -> _ -> M A) :
  do t1 <- expand_head h t;
  do t2 <- expand_head h t;
    k t1 t2 =
  do t' <- expand_head h t;
    k t' t'.
Proof.
  elim: h t => [/=|h IHh t].
    by rewrite 2!bindfailf.
  elim: t IHh => [l|n /=|t1 IH1 t2 IH2 /=] IHh.
  - rewrite bindA [RHS]bindA.
    under eq_bind do under eq_bind do rewrite bindA.
    (*
    rewrite -[LHS](cgetget _ _ _
      (fun (x1 x2 : coq_type _ ml_uvar) =>
        match x1 with | uVar _ => _ | uTerm _ => _ end >> _)).
    rewrite -[RHS](cgetget _ _ _
      (fun (x1 x2 : coq_type _ ml_uvar) =>
        match x1 with | uVar _ => _ | uTerm _ => _ end >> _)).
    apply: eq_bind => -[n|t].
      rewrite !bindretf cgetget.
      apply: eq_bind => -[n'|t'].
        by rewrite !bindretf.
    *)
    admit.
  - by rewrite !bindretf.
  - by rewrite !bindretf.
Admitted.

Lemma size_uterm_pos t:
  size_uterm t > 0.
Proof. by elim: t. Qed.

(* Requires that expand_head doesn't fail *)
(* Also requires that every get in the expand_head is inhabited,
   so this lemma probably isn't self-contained enough for a proof (?) *)
Lemma unify1_same h t l :
  unify1
    (expand_head h)
    (occurs_ref h)
    (unify2 h h)
    (size_pairs ((t, t) :: l)).+1 ((t, t) :: l) =
  unify1
    (expand_head h)
    (occurs_ref h)
    (unify2 h h)
    (size_pairs l).+1 l.
Proof.
rewrite /unify1 expand_same /=.
elim: l => [|a l IHl] /=.
under eq_bind => t'.
  have -> : forall f1 f2 f3,
      match t' with
        | uLink v1 =>
            match t' with
            | uLink v2 =>
                if loc_id v1 == loc_id v2
                then unify1 f1 f2 f3 (size_pairs [:: (t, t)])[::]
                else unify_link (unify2 h h) v1 t' [::]
            | _ => occurs_ref h v1 t' >> unify_link (unify2 h h) v1 t' [::]
            end
        | uInt m =>
            match t' with
            | uLink v2 => occurs_ref h v2 t' >> unify_link (unify2 h h) v2 t' [::]
            | uInt n =>
                if m == n
                then unify1 f1 f2 f3 (size_pairs [:: (t, t)]) [::]
                else fail
            | uNode _ _ => fail
            end
        | uNode tl1 tl2 =>
            match t' with
            | uLink v2 => occurs_ref h v2 t' >> unify_link (unify2 h h) v2 t' [::]
            | uInt _ => fail
            | uNode tr1 tr2 => unify1 f1 f2 f3 (size_pairs [:: (t, t)]) [:: (tl1, tr1); (tl2, tr2)]
            end
        end = Ret tt.
    elim: t' => [l|n|t'] *.
    - rewrite eqxx /size_pairs /=.

Admitted.

Lemma unifysubst h vs l s0 :
  let m := runActionT (bt_unify2 h l) in
  h > size (vars_pairs l) ->
  nofailure m ->
  exists (s : substType),
    always (fun x : unit * substType => x.2 == s) m /\
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]
    ) = cenv vs >>= csubst_list^~ (s0 ++ s).
Proof.
  elim: h l => //= h IHh l IHl.
  move Hh': (bt_size_pairs l + 1) => h'.
  have {Hh'} : h' > bt_size_pairs l.
    by rewrite -Hh' addn1 ltnS.
  elim: h' l IHl => //= h' IH' [*|].
    exists [::]; split.
      by rewrite runActionTret /always /assert bindretf /= bindskipf.
    rewrite /csubst_list /= cats0.
    by under eq_bind do rewrite bindA bindretf /= -foldr_bindA.
  case=> t1 t2 l Hs Hs'.
  destruct t1, t2.
  (* LinkLink *)
- case: ifP => vv0 Hnf.
    move/eqP in vv0; subst v0.
    under boolp.eq_exists => s.
      under [X in _ /\ X = _]eq_bind => vars.
        rewrite bindA repr_btree_cons /= [X in _ >> X]bindA.
        under [X in _ >> X]eq_bind => l1.
          rewrite bindretf bindA.
          under eq_bind => l2 do rewrite bindretf.
        over.
        rewrite add_varD.
        under [X in _ >> X]eq_bind => v0.
          under eq_bind => l' do rewrite addn1 (unify1_same h.+1).
        over.
      over.
    over.
    admit.
  admit.
  (* LinkInt *)
- admit.
  (* LinkNode *)
- admit.
  (* IntLink *)
- admit.
  (* IntInt *)
- elim eq: (n == n0) => Hnf.
    move: eq => /eqP ->.
    under boolp.eq_exists => s.
      under [X in _ /\ X = _]eq_bind => vars.
        rewrite bindA repr_btree_cons /= 2!bindretf.
        
        (*
        under [X in _ >> X]eq_bind => l'.
          rewrite addn1 /unify1 !bindretf eqxx.
        *)
        under [X in _ >> X]eq_bind do rewrite addn1 (unify1_same h.+1) -(addn1 (size_pairs _)).
        rewrite -bindA.
      over.
    over.
    apply: IH'.
    + exact: Hs.
    + move: Hs'.
      rewrite /bt_size_pairs /= [X in (1 + X < _) -> _]add1n add1n ltnS.
      apply/ltn_trans/ltnSn.
    + exact: Hnf.
  (* rewrite /nofailure runActionTfail bindfailf catchfailm in Hnf. *)

  (* Cannot prove that `nofailure fail` leads to contradiction *)

  admit.
  (* IntNode *)
- admit.
  (* NodeLink *)
- admit.
  (* NodeInt *)
- admit.
  (* NodeNode *)
- admit.
Abort.

(*

            (fun l0 : constr_list =>
             unify1
               (fun t : uterm =>
                match t with
                | uLink v =>
                    cget v >>=
                    (fun vt : uvar =>
                     match vt with
                     | uVar _ => Ret t
                     | uTerm t' => expand_head h t'
                     end)
                | _ => Ret t
                end) (fun v : loc ml_uvar => [eta occurs_ref1 (occurs_ref h) v])
               (unify2 h.+1 h) (size_pairs l0 + 1) l0) (size_pairs x + 1) x)) =
        cenv vs >>= csubst_list^~ (s0 ++ s)
*)

(*
       (fun l0 : constr_list =>
        unify1
          (fun t : uterm =>
           match t with
           | uLink v =>
               cget v >>=
               (fun vt : uvar =>
                match vt with
                | uVar _ => Ret t
                | uTerm t' => expand_head h t'
                end)
           | _ => Ret t
           end) (fun v : loc ml_uvar => [eta occurs_ref1 (occurs_ref h) v])
          (unify2 h.+1 h) (size_pairs l0 + 1) l0) (size_pairs x + 1) x)) =
   cenv vs >>= csubst_list^~ (s0 ++ s)

*)


(*
Lemma unifysubst h vs l :
  let m := runActionT (bt_unify2 h l) in
  h > size (vars_pairs l) ->
  nofailure m ->
  exists (s s0 : substType),
    always (fun x : unit * substType => x.2 == s) m /\
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]
    ) = cenv vs >>= csubst_list^~ s.
*)

(*
Lemma unifysubst h vs l s' :
  h > size (vars_pairs l) ->
  bt_unify2 M' h l = write M' s' >> Ret tt ->
  exists s s0,
    write M' s0 >> bt_unify2 M' h l = write M' s >> Ret tt /\
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]
    ) = cenv vs >>= csubst_list^~ s.
Proof.
  elim: h l => //= h IHh l IHl.
  move Hh': (bt_size_pairs l + 1) => h'.
  have {Hh'} : h' > bt_size_pairs l.
    by rewrite -Hh' addn1 ltnS.
  elim: h' l IHl => //= h' IH' [*|] /=.
    exists [::]; exists [::]; split.
      by rewrite write0 bindretf.
    by rewrite /csubst_list /= bindskipf bindretf /=.
  case=> t1 t2 l Hs Hs'.
  destruct t1, t2 => /= Hnofail.
- case: ifP => vv0.
    move/eqP in vv0; subst v0.
    under boolp.eq_exists => s.
      under boolp.eq_exists => s0.
        rewrite !bindA.
        under [X in _ /\ (X = _)]eq_bind => r.
          under eq_bind => vars.
            rewrite -!bindA.
    rewrite !bindA.
    

Abort.
*)

(*
Lemma unifysubst' h vs l s'' :
  h > size (vars_pairs l) ->
  unif.unify2 M' h l = write M' s'' >> Ret tt ->
  exists s s' s0,
    unif.unify2 M' h l = write M' s >> Ret tt /\
    (forall bt, subst_list s bt = subst_list s' bt) /\
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]
    ) = cenv vs >>= csubst_list^~ s'.
*)

(*
Lemma unifysubst' h vs l:
  h > size (vars_pairs l) ->
  (exists s', unif.unify2 M' h l = write M' s' >> Ret tt ->
  exists s,
    (forall bt, subst_list s bt = subst_list s' bt) /\
    cenv vs >>= (fun vars => repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]) =
    cenv vs >>= csubst_list^~ s).
Proof.
Abort.
*)

(*
Lemma unifysubst h vs l:
  h > size (vars_pairs l) ->
  (exists s', unif.unify2 M' h l = write M' s' >> Ret tt) ->
  exists s,
    unif.unify2 M' h l = write M' s >> Ret tt /\
    cenv vs >>= (fun vars => repr_btree_pairs vars l >>= [eta (unify2 h (h.+1))]) =
    cenv vs >>= csubst_list^~ s.
Proof.
  elim: h l => //= h IHh l IHl.
  move Hh': (unif.size_pairs l + 1) => h'.
  have {Hh'} : h' > unif.size_pairs l.
    by rewrite -Hh' addn1 ltnS.
  elim: h' l IHl => //= h' IH' [*|] /=.
    exists [::]; split.
      by rewrite write0 bindretf.
    by rewrite bindretf /csubst_list /=.
  case=> t1 t2 l Hs Hs'.
  destruct t1, t2 => /= Hnofail.
-
Abort.
*)

(*
Lemma unif_empty h :
  h > 0 ->
  unif.unify2 M' h [::] = write M' [::].
Proof.
move => H.
rewrite /unif.unify2 /=.
case:h H => // h H /=.
by rewrite /write action0.
Qed.

Lemma unify2_equiv h bt vs l s :
  h > size (vars_pairs l) ->
  unif.unify2 M' h l = write M' s >> Ret tt ->
  represents (
    do vars <- cenv vs;
    do r <- repr_btree_pairs vars l;
    unify2 h (h.+1) r >> repr_btree vars bt
  ) (subst_list s bt).
Proof.
  elim: h l => //= h IHh l IHl.

  move Hh': (unif.size_pairs l + 1) => h'.
  have {Hh'} : h' > unif.size_pairs l.
    by rewrite -Hh' addn1 ltnS.

  elim: h' l IHl => //= h' IH' [].
    move => ? ? Hs.
    under eq_bind => x do rewrite 2!bindretf /=.
    move: Hs.
    have ->: write M' s = write M' [::] by admit.
    have ->: s = [::] by admit.
    move => *.
    exact: repr_btree_ok.
Abort.

Lemma unif_equiv h bt vs bt1 bt2 s :
  h > size (vars_pairs [:: (bt1, bt2)]) ->
  unif.unify M' bt1 bt2 = write M' s ->
  represents (
    do vars <- cenv vs;
    do t1 <- repr_btree vars bt1;
    do t2 <- repr_btree vars bt2;
    unify h t1 t2 >> repr_btree vars bt
  ) (subst_list s bt).
Proof.
Abort.
*)

End equiv.

End Unification.

End CoqTypeNat.
