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
rewrite bindA -add_var_skipE 2!bindA bindskipf add_varC bindskipf -IH -add_varC.
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
    rewrite -cputchk !bindA !bindskipf.
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
  else fail.

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
  rewrite bindfailf bindA bindskipf.
  by under [RHS]eq_bind do rewrite bindfailf.
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
    by rewrite 2!bindfailf.
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

(*
Lemma csubst_add_varC A r v t v' (k : _ -> M A) :
  has_vars r [:: v] >> (csubst r v t >> (add_var r v' >>= k)) =
  has_vars r [:: v] >> (add_var r v' >>= fun u => csubst r v t >> k u).
Proof.
rewrite bindA [RHS]bindA -cgetputk -[RHS]cgetputk.
apply eq_bind => vars.
rewrite assertE bindA bindretf -[LHS]bindA -guardC bindA.
rewrite [in RHS]bindA bindretf -[RHS]bindA -guardC [RHS]bindA.
apply: bind_ext_guard => Hall.
rewrite bindA.
 bindA -[LHS]bindA -guardC bindA.
rewrite /csubst /add_var.
Search repr_btree.
*)

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
by rewrite -cget_cchkvarsC bindmskip -[X in _ = _ >> X]bindskipf bindA.
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
  rewrite !bindA !bindskipf cget_cchkvarsC -cnewgetC -IH.
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
- by rewrite {1}/cchk bindA bindskipf bindA -cget_cchkvarsC IH (cgetget _ v).
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
rewrite /= -add_var_skipE bindA bindskipf.
rewrite [X in _ >> X]bindA [X in _ = _ >> X]bindA !bindretf.
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

Lemma cenv_add_var_get A vs v (k : _ -> _ -> _ -> M A) :
  do r <- cenv vs; add_var r v >>= (fun l => cget l >>= k r l) =
  do r <- cenv vs; add_var r v >>= k r ^~ (uVar v).
Proof.
have := cenv_cat vs [:: v].
rewrite /add_vars /=.
under eq_bind do rewrite -add_var_skipE bindA bindskipf.
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
by rewrite /= bindA bindretf -add_var_skipE bindA bindskipf add_varD.
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

Lemma csubst_cgetC T A r vs (r' : loc T) t (k : _ -> _ -> M A) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (repr_btree r t >>= fun u => cget r' >>= k u) =
  has_vars r vs >> (cget r' >>= fun s => repr_btree r t >>= k ^~ s).
Proof.
elim: t k => [v|n|t1 IH1 t2 IH2] k /= Hvs.
- rewrite bindA.
  under (eq_bind (add_var r v)) do rewrite bindretf.
  rewrite has_varsE bindA [RHS]bindA.
  apply: eq_bind => vars.
  rewrite 3!bindA 2![in RHS]bindA.
  apply: bind_ext_guard => /andP[Hvars Hu].
  rewrite bindA cputget.
  have Hv: v \in vs by rewrite Hvs // mem_seq1 eqxx.
  move/allP/(_ _ Hv): Hvars.
  case Hnth: nth => [l|] // _.
  rewrite bindretf.

Lemma add_var_repr_btreeC A r vs v t (k : _ -> _ -> M A) :
  {subset free_vars t <= vs} ->
  has_vars r vs >> (repr_btree r t >>= fun u => add_var r v >>= k u) =
  has_vars r vs >> (add_var r v >>= fun l => repr_btree r t >>= k ^~ l).
Proof.
elim: t vs k => [u|n|t1 IH1 t2 IH2] /= vs k Hfv.
- rewrite bindA.
  rewrite has_varsE [LHS]bindA [RHS]bindA.
  apply: eq_bind => vars.
  rewrite !bindA !cputget.
  apply: bind_ext_guard => /andP[Hvars Huniq].
  have Huvs : u \in vs by apply: Hfv; rewrite !inE eqxx.
  move/allP/(_ _ Huvs): (Hvars).
  case Hnthu: nth => [lu|] // _.
  rewrite !bindretf !bindA cputget.
  case Hnth: nth => [l|].
    by rewrite !bindretf bindA cputget bindA Hnthu !bindretf.
  rewrite bindA -cputnewC [in RHS]bindA -cputnewC.
  apply: eq_bind => _.
  apply: eq_bind => _.
  apply: eq_bind => l'.
  rewrite !bindA !bindretf bindA cputget.
  rewrite nth_set_nth /=.
  case: ifPn => uv'.
    by rewrite (eqP uv') Hnth in Hnthu.
  by rewrite Hnthu !bindretf.
- rewrite bindretf.
  by under [X in _ = _ >> X]eq_bind do rewrite bindretf.
- rewrite bindA has_vars_repr_btreeC.
  under (eq_bind (repr_btree r t1)) => u1.
    rewrite bindA.
    under (eq_bind (repr_btree r t2))  do rewrite bindretf.
    rewrite IH2; first over.
    by move=> x Hx; rewrite mem_cat Hfv // mem_cat Hx orbT.
  rewrite -has_vars_repr_btreeC IH1; last first.
    by move=> x Hx; rewrite Hfv // mem_cat Hx.
  apply: eq_bind => _.
  apply: eq_bind => l.
  rewrite bindA.
  apply: eq_bind => u1.
  rewrite bindA.
  by under [RHS]eq_bind do rewrite bindretf.
Qed.

Lemma csubst_add_varC A r vs v t v' (k : _ -> M A) :
  {subset v :: free_vars t <= vs} ->
  has_vars r vs >> (csubst r v t >> (add_var r v' >>= k)) =
  has_vars r vs >> (add_var r v' >>= fun u => csubst r v t >> k u).
Proof.
move=> Hfv.
rewrite /csubst bindA.
under [in RHS](eq_bind (add_var r v')) do rewrite bindA.
rewrite -add_var_repr_btreeC; last first.
  by move=> x Hx; rewrite Hfv // in_cons Hx orbT.
rewrite has_vars_repr_btreeC [RHS]has_vars_repr_btreeC.
apply: eq_bind => _.
apply: eq_bind => u.
rewrite has_vars_subset; last first.
  by move=> x Hx; rewrite Hfv // in_cons Hx orbT.
rewrite bindA.
rewrite has_varsE bindA [RHS]bindA.
apply: eq_bind => vars.
rewrite 3!bindA 2![in RHS]bindA.
apply: bind_ext_guard => /andP[Hvars Hu].
under [in RHS](eq_bind (add_var r v')) do rewrite bindA.
rewrite -add_varC_present; last first.
  move/allP: Hvars; apply; apply: Hfv.
  by rewrite in_cons eqxx.
rewrite bindA [in RHS]bindA !cputget.
have Hvvs : v \in vs by apply: Hfv; rewrite !inE eqxx.
move/allP/(_ _ Hvvs): (Hvars).
case Hnth: nth => [l|] // _.
rewrite !bindretf.
rewrite [in RHS](cchkvars_nth Hnth) cchk_cchkvarsC bindA.
apply: eq_bind => _.
have rl : loc_id r != loc_id l.
  move/andP: Hu => [] /[swap] _.
  apply: contra => /eqP ->.
  by rewrite mem_loc_id_vars // (mem_nth_some Hnth).
rewrite -(bindA (cput r _)) cputC //; last by left.
rewrite 2!bindA [X in _ = _ >> (_ >> X)]bindA !cputget.
case Hnth': nth => [l'|].
  rewrite !bindretf -(bindA (cput r _)) cputC //; last by left.
  by rewrite [X in _ = _ >> X]bindA -[RHS]bindA cchkput.
rewrite -(bindA (cput l _)) -cputC //; last by left.
rewrite 2!bindA -cchknewput.
rewrite -bindA -cchkputC -[RHS]bindA.
apply: eq_bind => _.
rewrite bindA.
apply: eq_bind => l'.
rewrite !bindA !bindretf -bindA cputC //; last by left.
by rewrite bindA.
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

(* Lemma expand_head expand_head (locked h.+1) (uLink _x_ *)

Lemma ltnm0 (n m : nat) : m < n -> 0 < n.
Proof. exact: leq_ltn_trans. Qed.

Lemma expandS_uInt he n : 0 < he -> expand_head he (uInt n) = Ret (uInt n).
Proof. by case: he. Qed.

Lemma expandS_uNode he t1 t2 : 0 < he -> expand_head he (uNode t1 t2) = Ret (uNode t1 t2).
Proof. by case: he. Qed.

Lemma unifysubst h h' he vs l (s0 s : substType) :
  h > size (vars_pairs (map (subst_pair (push_subst s0)) l)) ->
  h' > bt_size_pairs (map (subst_pair (push_subst s0 ++ s)) l) ->
  he > size s0 ->
  bt_unify2 h (map (subst_pair (push_subst s0)) l) = write M' s ->
  exists2 s',
    push_subst s' = s &
    cenv vs >>= (fun vars =>
      csubst_list vars s0 >> repr_btree_pairs vars l >>= (unify1 h' he)
    ) = cenv vs >>= csubst_list^~ (s0 ++ s').
Proof.
  elim: h h' he vs l s0 s => // h IHh.
  elim/ltn_ind => h' IHh' he vs [/=|[t1 t2] l] s0 s.
    case: h' IHh' => // h' IHh' _ _ He [].
    rewrite [RHS]cats0 => <-.
    exists nil => //.
    under eq_bind do rewrite /repr_btree_pairs bindA !bindretf /= -foldr_bindA.
    by rewrite cats0.
  move=> Hh Hh' He.
  under eq_bind => vars do rewrite bindA repr_btree_cons /=.
  rewrite /repr_btree_pairs /=.
  case: h' Hh' IHh' => // h' Hh' IHh'.
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
        rewrite bindretf expandS_uInt => //.
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
            rewrite bindretf expandS_uNode => //.
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
    rewrite bindretf expandS_uInt => //.
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
  rewrite expandS_uInt => //.
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
        rewrite bindretf expandS_uNode => //.
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
  rewrite !expandS_uNode => //.
  by rewrite 2!bindretf.
Abort.

Fixpoint bt_expand_head s v : btree :=
  match s with
  | nil => btVar v
  | (v', t) :: s' =>
    if v == v' then t else bt_expand_head s' v
  end.

Fixpoint sorted_subst (s : substType) : bool :=
  match s with
  | nil => true
  | (v, _) :: s' =>
    (v \notin unzip1 s') &&
    (btVar v \notin unzip2 s) &&
    sorted_subst s'
  end.

Lemma bt_expand_notin v (s : substType) :
  v \notin unzip1 s ->
  bt_expand_head s v = btVar v.
Proof.
elim: s => // [[v' t] l] IH.
case /boolP : (v == v') => [/eqP <-|Hneq] /=.
  by rewrite mem_head.
have ->: v == v' = false by apply: (@contra_neqF _ _ v v') => [/eqP|] //.
move => H; apply: IH; move: H.
by rewrite /in_mem negb_or Hneq.
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

Lemma expand_uLink A vs he v (s : substType) (k : _ -> M A):
  size s < he ->
  sorted_subst s ->
  {subset free_vars_subst s <= vs} ->
  (do r <- cenv vs;
   csubst_list r s >>
   do x <- add_var r v;
   expand_head he (uLink x) >>= k) =
  (do r <- cenv vs;
   csubst_list r s >>
   (repr_btree r (bt_expand_head s v) >>= k)).
Proof.
pose s0 : substType := [::].
have {-1}-> : s = s0 ++ s by [].
have: v \notin unzip1 s0 by [].
elim: s s0 he => [|[v' t] s IH /=] s0 he Hnin.
  rewrite cats0 bt_expand_notin => // He Hsorted Hsub /=.
  case: he He => //= he _.
  elim/last_ind: s0 (expand_head he) Hnin Hsorted Hsub
      => [|s0 [v' t'] IH] /= ke Hnin Hsorted Hsub.
    under eq_bind do (rewrite bindskipf; under eq_bind do rewrite bindA).
    under [RHS]eq_bind do rewrite bindskipf bindA.
    by rewrite cenv_add_var_get.
  rewrite cenv_has_vars.
  under eq_bind => r.
    rewrite /csubst_list map_rcons foldr_rcons foldr_bindA bindmskip bindA /=.
    rewrite -bindA has_vars_csubst_listC //; first last.
      move=> x Hx; apply/Hsub/(free_vars_subst_subset _ Hx) => y Hy.
      by rewrite mem_rcons in_cons Hy orbT.
    rewrite 2!bindA csubst_add_varC; last first.
      have -> : v' :: free_vars t' = free_vars_subst [:: (v',t')].
        by rewrite /free_vars_subst /= cats0.
      move=> x Hx; apply/Hsub/(free_vars_subst_subset _ Hx).
        by move=> y; rewrite mem_seq1 mem_rcons inE => ->.
    rewrite has_vars_add_var.
 (x:=[::(v',t')])).
      move=> x Hx; rewrite Hsub // /free_vars_subst. -cats1 !mem_cat. !mem_map.
      
    Search add_var csubst.
  admit.
case /boolP : (v == v').
  case: he => // he /=.
  rewrite ltnS => /eqP <-.
  admit.
move => Hneq He Hsort.
have H1 : v \notin unzip1 (rcons s0 (v', t)).
  by rewrite -cats1 /unzip1 map_cat /= mem_cat inE negb_or Hnin.
move: (IH (rcons s0 (v', t)) he H1 (ltnW He)).
by rewrite -cats1 -catA /= => /(_ Hsort).
Abort.

Lemma expand_uLink1 A vs he v t (s : substType) (k : _ -> M A):
  0 < he ->
  (v, t) \in s ->
  (do r <- cenv vs;
   csubst_list r s >>
   do x <- add_var r v;
   expand_head he (uLink x) >>= k) =
  (do r <- cenv vs;
   csubst_list r s >>
   do x <- repr_btree r t;
   expand_head he.-1 x >>= k).
Proof.
rewrite /=.
elim: s v => //=.
Abort.

End equiv.

End Unification.

End CoqTypeNat.
