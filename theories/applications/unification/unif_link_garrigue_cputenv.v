(* Require Import ZArith. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From HB Require Import structures.
Require Import preamble hierarchy monad_lib typed_store_lib fail_lib.

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

(*
Definition uget (v : loc ml_uvar) : M uvar := cget v.
Definition uset (v : loc ml_uvar) : uvar -> M unit := cput v.
*)

Definition constr_list : Type := list (uterm * uterm)%type.

End Definitions.

Section unify.

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
End repr.

Definition cenv (vs : list nat) :=
  do vars <- cnew (ml_list (ml_option (ml_ref ml_uvar))) nil;
  foldr (fun n m => add_var_skip vars n >> m) (Ret vars) vs.

Local Notation foldM := (foldr (fun m1 m2 => m1 >> m2)).

Section vars_defs.
Variable vars : list (option (@loc _ nat ml_uvar)).

Definition put_nth_var i : M unit :=
  if nth None vars i is Some v then cput v (uVar i) else skip.

Definition cputvars :=
  foldM skip (mkseq put_nth_var (size vars)).
Definition cchkvars : M unit :=
  foldM skip [seq if o is Some v then cchk v else skip | o <- vars].

Definition loc_id_vars := pmap (omap (@loc_id _ nat ml_uvar)) vars.
Definition vars_loc_uniq (r : loc (ml_list (ml_option (ml_ref ml_uvar)))) :=
  uniq (loc_id r :: loc_id_vars).

Definition cputenv (r : loc (ml_list (ml_option (ml_ref ml_uvar))))
  : M unit :=
  guard (vars_loc_uniq r) >> cput r vars >> cputvars.
End vars_defs.

Lemma cputgetC T1 T2 (r1 : loc T1) (r2 : loc T2) s1
      (A : UU0) (k : coq_type N T2 -> M A) :
  loc_id r1 != loc_id r2 ->
  cput r1 s1 >> (cget r2 >>= k) =
  cget r2 >>= (fun v : coq_type N T2 => cput r1 s1 >> k v).
Proof. by move=> *; rewrite -bindA cputgetC. Qed.

Lemma cputC T1 T2 (r1 : loc T1) (r2 : loc T2) s1 s2 :
  loc_id r1 != loc_id r2 \/ JMeq.JMeq s1 s2 ->
  cput r1 s1 >> cput r2 s2 = cput r2 s2 >> cput r1 s1 :> M _.
Proof. apply: cputC; exact unit. Qed.

Lemma foldr_bindA A B (s : seq (M A)) (m : M B) :
  foldM m s = foldM skip s >> m.
Proof.
elim: s => /= [|m1 s IH].
  by rewrite bindskipf.
by rewrite IH bindA.
Qed.

Lemma mem_loc_id_vars r vars :
  Some r \in vars -> loc_id r \in loc_id_vars vars.
Proof. by rewrite mem_pmap => /(map_f (omap (@loc_id _ _ ml_uvar))). Qed.

Lemma loc_id_vars_cat s1 s2 :
  loc_id_vars (s1 ++ s2) = loc_id_vars s1 ++ loc_id_vars s2.
Proof. exact: pmap_cat. Qed.

Lemma cput_putvarsC T r x vars :
  loc_id r \notin loc_id_vars vars ->
  cput (T:=T) r x >> cputvars vars = cputvars vars >> cput r x.
Proof.
rewrite /cputvars.
set n := size vars.
have Hn : n <= size vars by [].
elim: n Hn => [|n IH] Hn Hne.
  by rewrite bindskipf bindmskip.
rewrite mkseqS foldr_rcons foldr_bindA !bindmskip -!bindA.
rewrite IH //; last by rewrite ltnW.
rewrite !bindA.
apply: eq_bind => _.
rewrite /put_nth_var.
case Hnth: nth => [v|].
  rewrite cputC //; left.
  apply: contra Hne => /eqP ->.
  by rewrite mem_loc_id_vars // -Hnth mem_nth.
by rewrite bindskipf bindmskip.
Qed.

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

Lemma cchk_cchkvarsC (T : ml_type) vars (r : loc T) :
  cchk r >> cchkvars vars = cchkvars vars >> cchk r.
Proof.
elim: vars => [|v vars IH].
  by rewrite bindmskip bindskipf.
rewrite /cchkvars /= -bindA.
case: v => [v|].
  by rewrite -cchkC bindA IH [RHS]bindA.
by rewrite bindmskip bindskipf.
Qed.

Lemma cchknewputvars (T : ml_type) (A : UU0) vars
      (x : coq_type N T) (k : loc T -> M A) :
  (cchkvars vars >> do rx <- cnew T x; cputvars vars >> k rx)
  = cputvars vars >> (cnew T x >>= k).
Proof.
symmetry.
rewrite /cputvars.
rewrite -[foldM _ _]bindmskip.
pose n := size vars.
have {2}-> : skip = cchkvars (drop n vars) by rewrite drop_size.
under [cnew T x >>= _]eq_bind => r.
  rewrite -(bindskipf (k r)).
  have -> : skip = foldM skip (drop n (mkseq (put_nth_var vars) (size vars))).
    by rewrite -map_drop drop_iota subnn.
  over.
rewrite -{1}/n.
have Hn : n <= size vars by [].
elim: n Hn k => [|n IH] Hn k.
  by rewrite /= !drop0 bindmskip bindskipf.
rewrite mkseqS foldr_rcons foldr_bindA bindmskip.
rewrite 2!bindA.
rewrite {2}/put_nth_var -IH // 1?ltnW //.
case Hnth: nth => [v|]; last first.
  rewrite bindskipf -bindA.
  have -> : cchkvars (drop n.+1 vars) = cchkvars (drop n vars).
    by rewrite (drop_nth None Hn) Hnth /cchkvars /= bindskipf.
  apply: eq_bind => _.
  apply: eq_bind => r.
  rewrite -!map_drop (drop_nth 0 (n:=n)); last by rewrite size_iota.
  by rewrite nth_iota // add0n /= /put_nth_var Hnth bindskipf.
rewrite -(bindA (cput _ _)) cput_cchkvarsC 2!bindA -cchknewput.
rewrite -(bindA (cchkvars _)) -cchk_cchkvarsC.
apply eq_bind => _.
rewrite (drop_nth None Hn) {2}/cchkvars /= Hnth.
apply: eq_bind => _.
apply: eq_bind => r.
rewrite -!map_drop (drop_nth 0 (n:=n)) /=; last by rewrite size_iota.
by rewrite {2}/put_nth_var nth_iota // add0n Hnth bindA.
Qed.

Lemma cputvarsnewC (T : ml_type) (A : UU0) vars
      (x : coq_type N T) (k : loc T -> M A) :
  (do rx <- cnew T x;
   guard (loc_id rx \notin loc_id_vars vars) >> cputvars vars >> k rx)
  = cputvars vars >> (cnew T x >>= k).
Proof.
symmetry.
rewrite {1}/cputvars.
pose n := size vars.
rewrite -{1}/n.
under [cnew T x >>= _]eq_bind => r.
  rewrite -(bindskipf (k r)).
  have -> : skip = guard (loc_id r \notin loc_id_vars (drop n vars)) >>
                foldM skip (drop n (mkseq (put_nth_var vars) (size vars))).
    by rewrite drop_size bindskipf -map_drop drop_iota subnn.
  over.
have Hn : n <= size vars by [].
elim: n Hn k => [|n IH] Hn k.
  by rewrite /= !drop0 bindskipf.
rewrite mkseqS foldr_rcons foldr_bindA bindmskip.
rewrite bindA -IH 1?ltnW //.
apply: eq_bind => _.
rewrite {1}/put_nth_var.
case Hnth: nth => [v|]; last first.
  rewrite bindskipf.
  apply: eq_bind => r.
  rewrite -!map_drop (drop_nth 0 (n:=n)); last by rewrite size_iota.
  rewrite nth_iota // add0n /= /put_nth_var Hnth bindskipf.
  by rewrite {2}/loc_id_vars (drop_nth None (n:=n)) // Hnth.
rewrite -cnewputC.
apply: eq_bind => r.
rewrite {2}/loc_id_vars (drop_nth None (n:=n)) // Hnth /= in_cons negb_or.
rewrite eq_sym.
case/boolP: (_ == _) => Heq /=.
  by rewrite guardF !bindfailf.
rewrite guardT bindskipf /loc_id_vars.
case/boolP: (loc_id r \in _) => Hin /=.
  by rewrite guardF !bindfailf bindmfail.
rewrite guardT -!map_drop (drop_nth 0 (n:=n)); last by rewrite size_iota.
by rewrite nth_iota // add0n /= /put_nth_var Hnth !bindskipf !bindA.
Qed.

Lemma guardC b (m : M unit) : guard b >> m = m >> guard b.
Proof.
by case: b; rewrite (guardT,guardF) !(bindskipf,bindmskip,bindfailf,bindmfail).
Qed.

Lemma set_nth_cat A a0 s1 s2 n (a : A) :
  set_nth a0 (s1++s2) n a =
  if n < size s1 then set_nth a0 s1 n a ++ s2
                 else s1 ++ set_nth a0 s2 (n-size s1) a.
Proof. by elim: n s1 => [|n IH] [|b s1] //=; rewrite ltnS IH; case: ifPn. Qed.

Lemma cputvars_rcons vars v :
  cputvars (rcons vars v) =
  cputvars vars >> if v is Some r then cput r (uVar (size vars)) else skip.
Proof.
rewrite /cputvars size_rcons -addn1 /mkseq iotaD /= add0n map_cat /=.
rewrite foldr_cat /= foldr_bindA bindmskip.
rewrite {2}/put_nth_var nth_rcons ltnn eqxx.
congr (foldM _ _ >> _).
apply/eq_in_map => i.
rewrite mem_iota add0n leq0n /put_nth_var /= => Hi.
by rewrite !nth_rcons Hi.
Qed.

Lemma cputvars_add_var vars n (rx : loc ml_uvar) :
  ~~ nth None vars n ->
  loc_id rx \notin loc_id_vars vars ->
  cputvars vars >> cput rx (uVar n) = cputvars (set_nth None vars n (Some rx)).
Proof.
case: (ltnP n (size vars)); last first.
  move=> Hn Hnth Hu.
  rewrite set_nthE ltnNge Hn /= /cputvars.
  have Hsz : size (vars ++ ncons (n - size vars) None [:: Some rx]) = n.+1.
    by rewrite size_cat size_ncons addnA subnKC // addn1.
  rewrite Hsz mkseqS foldr_rcons [in RHS]foldr_bindA.
  rewrite bindmskip {3}/put_nth_var.
  rewrite nth_cat ltnNge Hn /= nth_ncons ltnn subnn /=.
  rewrite -{3}(subnKC Hn) /mkseq iotaD map_cat foldr_cat.
  congr (foldM _ _ >> _).
    rewrite add0n.
    set i := n - size vars.
    rewrite {1}/i.
    have : i <= n - size vars by [].
    elim/ltn_ind: i => -[] // i IH Hi.
    rewrite -addn1 iotaD /= map_cat foldr_cat foldr_bindA /= -IH // 1?ltnW //.
    rewrite /put_nth_var nth_cat ltnNge leq_addr /= addKn.
    by rewrite nth_ncons Hi !bindskipf.
  apply/eq_in_map => i.
  rewrite mem_iota add0n leq0n /put_nth_var /= => Hi.
  by rewrite nth_cat Hi.
elim/last_ind: vars => [|vars v IH] // Hn Hnth Hu.
move: Hn.
rewrite size_rcons ltnS leq_eqVlt => /orP[/eqP|] Hn.
  rewrite {2}Hn set_nth_rcons !cputvars_rcons.
  move: Hnth.
  rewrite Hn !nth_rcons ltnn eqxx.
  destruct v => //.
  by rewrite bindmskip.
rewrite -cats1 set_nth_cat Hn !cats1 !cputvars_rcons.
rewrite -IH //; first last.
- by move: Hu; rewrite /loc_id_vars -cats1 pmap_cat mem_cat negb_or => /andP[].
- by rewrite nth_rcons Hn in Hnth.
destruct v as [r|].
  rewrite !bindA size_set_nth.
  move/maxn_idPr: Hn => ->.
  rewrite cputC //; try exact unit.
  left.
  move: Hu; rewrite /loc_id_vars -cats1 pmap_cat mem_cat negb_or => /andP[] /=.
  by rewrite in_cons orbF eq_sym.
by rewrite !bindmskip.
Qed.

Lemma loc_id_vars_ncons n s : loc_id_vars (ncons n None s) = loc_id_vars s.
Proof. by elim: n. Qed.

Lemma cputenv_cget r vars :
  cputenv vars r >> cget r = cputenv vars r >> Ret vars.
Proof.
rewrite !bindA.
apply: bind_ext_guard.
rewrite /vars_loc_uniq /= => /andP[] Hu _.
rewrite -bindA -[RHS]bindA cput_putvarsC // !bindA.
by rewrite -(bindmret (cget r)) cputget.
Qed.

Lemma cputenv_add_var (A : UU0) (r : loc (ml_list (ml_option (ml_ref ml_uvar))))
      n (k : _ -> M A) :
  do vars <- cget r; (cputenv vars r >> (add_var r n >>= k)) =
  do vars <- cget r;
  do v <- add_var r n; cputenv (set_nth None vars n (Some v)) r >> k v.
Proof.
rewrite /add_var /= bindA.
under eq_bind do rewrite -bindA cputenv_cget bindA bindretf.
under [RHS]eq_bind do rewrite bindA.
rewrite cgetget.
apply: eq_bind => vars.
case Hnth: (nth None vars n) => [v|].
  rewrite !bindretf set_nthE.
  case: ifPn => Hn.
    by rewrite -Hnth // -drop_nth // cat_take_drop.
  by move: Hnth; rewrite nth_default // leqNgt.
rewrite /cputenv.
rewrite !bindA -cputvarsnewC -cnewputC -2!bindA guardsC; last exact: bindmfail.
rewrite !bindA -(cnewput ml_uvar (uVar n)).
apply: eq_bind => rx.
rewrite assertE bindA bindretf.
rewrite -(bindA (guard _)) -guard_and.
rewrite bindA -(bindA (cput r _)) -guardC bindA.
rewrite -(bindA (guard _)) -guard_and -bindA -guardC.
rewrite ![in RHS]bindA bindretf ![in RHS]bindA -[RHS]bindA -guardC.
rewrite !bindA.
set lg := _ && _.
set rg := vars_loc_uniq _ _.
have Hg : lg = rg.
  rewrite /lg /rg /vars_loc_uniq /=.
  rewrite set_nthE.
  case: ifPn => Hn.
    rewrite !loc_id_vars_cat /=.
    rewrite -cat1s catA cats1.
    rewrite
      (_ : uniq (_ ++ _) = uniq ((loc_id rx :: loc_id_vars (take n vars))
                       ++ loc_id_vars (None :: drop n.+1 vars))); last first.
      by apply: perm_uniq; rewrite perm_cat2r perm_rcons.
    rewrite -Hnth -drop_nth // [(_ :: _) ++ _]/=.
    rewrite -loc_id_vars_cat cat_take_drop.
    rewrite mem_cat mem_rcons -mem_cat /=.
    rewrite [in RHS]in_cons negb_or.
    rewrite (_ : _ ++ _ = loc_id_vars vars); last first.
      rewrite -[X in _ = loc_id_vars X](cat_take_drop n) loc_id_vars_cat.
      by rewrite [in RHS](drop_nth None) ?Hnth.
    by rewrite !andbA [RHS]andbC !andbA [X in _ = X && _]andbC !andbA.
  rewrite loc_id_vars_cat loc_id_vars_ncons /= uniq_catC.
  rewrite mem_cat orbC -mem_cat /= in_cons negb_or.
  by rewrite !andbA [RHS]andbC !andbA [X in _ = X && _]andbC !andbA.
rewrite -Hg.
apply: bind_ext_guard => /andP[] /andP[] /andP[] Hr Hvars rrx Hrx.
rewrite -/uniq in Hvars.
rewrite -(bindA (cput r _)) cput_putvarsC //.
rewrite !bindA -(bindA (cput r _)) cputput.
rewrite -[RHS](bindA (cput r _)) cputput.
rewrite -[RHS](bindA (cput r _)) cput_putvarsC.
  rewrite -[LHS]bindA cput_putvarsC // bindretf cputvars_add_var // ?Hnth //.
  by rewrite bindA.
rewrite set_nthE.
case: ifPn => Hn.
  move: Hr; rewrite -{1}(cat_take_drop n vars) !loc_id_vars_cat.
  rewrite (drop_nth None) // Hnth /=.
  apply: contra.
  rewrite mem_cat => /orP[].
    by rewrite mem_cat => ->.
  rewrite in_cons mem_cat => /orP[H|->].
    by rewrite H in rrx.
  by rewrite orbT.
rewrite -leqNgt in Hn.
rewrite loc_id_vars_cat mem_cat negb_or Hr /=.
by rewrite loc_id_vars_ncons mem_seq1.
Qed.

Definition add_vars vs r :=
  foldr (fun n m => add_var_skip r n >> m) (Ret r) vs.

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

Lemma cputvarsD vars :
  uniq (loc_id_vars vars) ->
  cputvars vars >> cputvars vars = cputvars vars.
Proof.
elim/last_ind: vars => [|vars v IH].
  by rewrite bindskipf.
rewrite cputvars_rcons -cats1 loc_id_vars_cat uniq_catC.
case: v => [v|]; last by rewrite !bindmskip.
rewrite /= => /andP[] Hv Hu.
rewrite -{1}cput_putvarsC // !bindA.
rewrite -(bindA (cputvars _)) IH //.
by rewrite -bindA cput_putvarsC // bindA cputput.
Qed.

Lemma cenvputenv vs :
  cenv vs = do r <- cenv vs; do vars <- cget r; cputenv vars r >> Ret r.
Proof.
elim/last_ind: vs => [|vs n IH].
  rewrite !bindA /cenv /=.
  under [RHS]eq_bind do rewrite bindretf.
  rewrite cnewget /cputenv /=.
  under [RHS]eq_bind do rewrite guardT !bindskipf bindA bindskipf.
  by rewrite cnewput.
rewrite -cats1 cenv_cat IH.
rewrite bindA.
under eq_bind => r.
  rewrite bindA.
  under eq_bind do rewrite bindA bindretf /= -add_var_skipE bindA.
  rewrite cputenv_add_var bindskipf.
  over.
symmetry.
rewrite bindA /=.
apply: eq_bind => r.
rewrite bindA.
apply: eq_bind => vars.
rewrite bindA.
apply: eq_bind => v.
rewrite bindA bindretf /cputenv 5!bindA.
under bind_ext_guard => /andP[] Hr.
  rewrite -/uniq => Hu.
  rewrite -bindA cput_putvarsC //.
  rewrite bindA cputget.
  rewrite !bindA -(bindA (cput _ _)) -guardC !bindA.
  rewrite -(bindA (cput _ _)) cputput.
  rewrite -(bindA (cputvars _)) -guardC !bindA.
  rewrite -(bindA (cputvars _)) -cput_putvarsC //.
  rewrite !bindA -(bindA (cputvars _)).
  rewrite cputvarsD //.
  over.
by rewrite -(bindA (guard _)) -guard_and andbb.
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

Inductive represents : M uterm -> btree -> Prop :=
| RVar (m : M uterm) v (n : nat) :
  (*crun (do u <- m; if u is uLink v then cget v else fail) = Some (uVar n) ->*)
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

  (*
  crun m = Some (uLink v) ->
  crun (m >> uget v) = Some (uVar n) ->
  *)

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

Fixpoint free_vars bt :=
  match bt with
  | btVar n => [:: n]
  | btInt _ => [::]
  | btNode bt1 bt2 => free_vars bt1 ++ free_vars bt2
  end.

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

Lemma rcons_rightapp A (l : list A) (a : A) :
  rcons l a = l ++ [:: a].
Proof. by elim: l => //= a' l ->. Qed.

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

Lemma repr_btree_delay vs1 vs2 bt :
  (cenv vs1 >>= fun r => repr_btree r bt >>= fun u => add_vars vs2 r >> Ret u)
  = cenv (vs1 ++ free_vars bt ++ vs2) >>= repr_btree ^~ bt.
Proof.
elim: bt vs1 vs2 => [n|n|bt1 IH1 bt2 IH2] vs1 vs2 /=.
Admitted.

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
(*
    rewrite -repr_btree_delay.
    rewrite 2![in RHS]bindA.
    under [in RHS]eq_bind => r.
      rewrite bindA.
      under eq_bind do rewrite bindA.
      under eq_bind do under eq_bind do rewrite (bindretf (uNode _ _)).
      over.
    rewrite -[in RHS]bindA.
    rewrite 2!cenv_repr_k -!catA.    
*)
    rewrite 2!bindA [in RHS]bindA.
    rewrite (crunbind _ _ vars_loc) ?eq_crunenv //.
    under [in RHS]eq_bind => r.
      rewrite bindA.
      under eq_bind do rewrite bindA bindretf.
      under eq_bind do under eq_bind do rewrite bindretf.
      over.
    rewrite 2!cenv_repr_k -!catA.   
    admit.
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
Abort.



(*
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
*)

Fixpoint repr_uterm h (t : uterm) : M btree :=
  if h is h.+1 then
    match t with
    | uInt n => Ret (btInt n)
    | uNode t1 t2 =>
        do bt1 <- repr_uterm h t1;
        do bt2 <- repr_uterm h t2;
        Ret (btNode bt1 bt2)
    | uLink r =>
        do v <- cget r;
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
      rewrite bindA bindretf.
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
      rewrite bindA bindretf.
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
      do vt <- (cget v : M uvar);
      if vt is uTerm t' then expand_head h t' else Ret t
    else Ret t
  else fail.

Fixpoint occurs_ref h (v : loc ml_uvar) t :=
  if h is h.+1 then
    match t with
    | uLink w =>
        if loc_id v == loc_id w then fail else
        do wt <- (cget w : M uvar);
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
          else cput v1 (uTerm t2) >> unify h l'
      | uLink v1, _ =>
          do _ <- occurs_ref h v1 t2;
          cput v1 (uTerm t2) >> unify h l'
      | _, uLink v2 =>
          do _ <- occurs_ref h v2 t1;
          cput v2 (uTerm t1) >> unify h l'
      | _, _ => fail
      end
    else Ret tt
else fail.

End unify.
End Unification.

End CoqTypeNat.
