From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From mathcomp Require Import finmap.

Require Import preamble hierarchy monad_lib fail_lib state_lib.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

HB.mixin Record isMonadAction (S : UU0) (S0 : S) (op : Monoid.law S0)
  (M : UU0 -> UU0) of Monad M := {
  action : forall {A : UU0}, S -> M A -> M A;
  action0 : forall (A : UU0), @action A S0 = id;
  actionA : forall (A : UU0) (x y : S) (m : M A),
    action x (action y m) = action (op x y) m;
  actionBind : forall (A B : UU0) (s : S) (m : M A) (f : A -> M B),
    action s (m >>= f) =
    action s m >>= f;
}.

#[short(type=actionMonad)]
HB.structure Definition MonadAction (S : UU0) (S0 : S) (op : Monoid.law S0) :=
  { M of isMonadAction S S0 op M & }.

Arguments action {_ _ _ _ _}.

HB.mixin Record isMonadActionRun (S : UU0) (S0 : S) (op : Monoid.law S0)
  (N : monad) (M : UU0 -> UU0) of @MonadAction S S0 op M := {
  runActionT : forall A : UU0, M A -> N (A * S)%type;
  runActionTret : forall (A : UU0) (a : A),
    @runActionT _ (Ret a) = Ret (a, S0) ;
  runActionTbind : forall (A B : UU0) (m : M A) (f : A -> M B),
    @runActionT _ (m >>= f) =
    @runActionT _ m >>=
      fun x => @runActionT _ (f x.1) >>=
      fun y => Ret (y.1, op x.2 y.2) ;
  runActionTaction : forall (A : UU0) (s : S) (m : M A),
    @runActionT _ (action s m) = 
    @runActionT _ m >>= fun x => Ret (x.1, op s x.2);
}.

#[short(type=actionRunMonad)]
HB.structure Definition MonadActionRun S S0 op N:=
  {M of isMonadActionRun S S0 op N M}.

HB.mixin Record isMonadActionRunFail (S : UU0) (S0 : S) (op : Monoid.law S0)
  (N : failMonad) (M : UU0 -> UU0) of @MonadActionRun S S0 op N M & MonadFail M := {
  runActionTfail : forall (A : UU0),
    runActionT _ (@fail M A) = @fail N _;
}.

#[short(type=actionRunFailMonad)]
HB.structure Definition MonadActionRunFail S S0 op N:=
  {M of isMonadActionRunFail S S0 op N M}.

Arguments runActionT {_ _ _ _ _ _}.

Module ActionMonad.
Section actionMonad.

Import Monoid.Theory.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (N : monad).

Definition acto : UU0 -> UU0 :=
  let op := op in fun A => N (A * S)%type.
Local Notation M := acto.

Let ret : idfun ~~> M := fun A (a : A) => Ret (a, S0).
Let bind A B (m : M A) (f : A -> M B) : M B :=
    m >>= fun '(a, s1) => f a >>= fun '(b, s2) => (Ret (b, op s1 s2)).

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B /= m f.
rewrite /bind /ret bindretf -[RHS]bindmret.
apply: eq_bind => -[b s2].
by rewrite mul1m.
Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A m /=.
rewrite /bind /ret -[RHS]bindmret.
apply: eq_bind => -[a s1].
by rewrite bindretf mulm1.
Qed.

Let associative : BindLaws.associative bind.
Proof.
move=> A B C m f g.
rewrite /bind bindA.
apply: eq_bind => -[a s1].
rewrite !bindA.
apply: eq_bind => -[b s2].
rewrite bindretf bindA.
apply: eq_bind => -[c s3].
by rewrite bindretf mulmA.
Qed.

Let action {A : UU0} s2 (m : M A) : M A :=
  m >>= (fun '(a, s1) => Ret (a, op s2 s1)).

Let runActionT (A : UU0) (m : M A) : N (A * S)%type := m.

Let action0 A : @action A S0 = id.
Proof.
apply: boolp.funext.
rewrite /action => x.
rewrite -[RHS]bindmret.
apply: eq_bind => -[a s1].
by rewrite mul1m.
Qed.

Let actionA A (x y : S) (m : M A) :
  action x (action y m) = action (op x y) m.
Proof.
rewrite /action bindA.
apply: eq_bind => -[a s1].
by rewrite bindretf mulmA.
Qed.

HB.instance Definition _ :=
  isMonad_ret_bind.Build acto left_neutral right_neutral associative.

Let actionBind A B (s : S) (m : M A) (f : A -> M B) :
  action s (bind m f) = bind (action s m) f :> M B.
Proof.
rewrite /action bindA [RHS]bindA /acto.
apply eq_bind => -[a s1].
rewrite bindretf bindA.
apply eq_bind => -[b s2].
by rewrite bindretf mulmA.
Qed.

Let runActionTret (A : UU0) (a : A) :
  runActionT (ret a) = Ret (a, S0).
Proof. by rewrite /runActionT /ret. Qed.

Let runActionTbind (A B : UU0) (m : M A) (f : A -> M B) :
  runActionT (bind m f) =
  runActionT m >>=
    fun x => runActionT (f x.1) >>=
    fun y => Ret (y.1, op x.2 y.2).
Proof.
rewrite /runActionT /acto.
apply eq_bind => -[a s1] /=.
apply eq_bind => -[b s2] //=.
Qed.

Let runActionTaction (A : UU0) (s : S) (m : M A) :
    runActionT (action s m) = 
    runActionT m >>= fun x => Ret (x.1, op s x.2).
Proof.
rewrite /runActionT /action.
apply eq_bind => -[a s1] //=.
Qed.

HB.instance Definition _ :=
  isMonadAction.Build S S0 op acto action0 actionA actionBind.

HB.instance Definition _ :=
  isMonadActionRun.Build S S0 op N acto runActionTret runActionTbind runActionTaction.

End actionMonad.
End ActionMonad.
HB.export ActionMonad.

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

Section WriterMonad.

Import Monoid.Theory.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (N : failMonad)
          (M : @actionRunMonad S S0 op N).

Definition write (s : S) : M unit := action s (Ret tt).

Lemma writeA a b :
  (write a) >> (write b) = write (op a b).
Proof. by rewrite /write -actionBind bindretf actionA. Qed.

Lemma runActionTwrite (s : S) :
  runActionT (write s) = Ret (tt, s).
Proof. by rewrite /write runActionTaction runActionTret bindretf /= mulm1. Qed.

End WriterMonad.

Section Definitions.

Definition var : Type := nat.

Inductive btree : Type :=
| btVar : var -> btree
| btInt : nat -> btree
| btNode : btree -> btree -> btree.

Scheme Equality for btree.

Lemma btree_eq_boolP : Equality.axiom btree_eq_dec.
Proof. move=> x y. case: btree_eq_dec => //= H; by constructor. Qed.
HB.instance Definition _ := hasDecEq.Build _ btree_eq_boolP.

Definition substType : UU0 := list (var * btree).

Definition subst0 : substType := [::].
Definition subst_comp := (@List.app (var * btree)%type).

(* t[x\u] *)
Fixpoint subst x u t : btree :=
match t with
| btVar v => if (x == v) then u else t
| btInt _ => t
| btNode t1 t2 => btNode (subst x u t1) (subst x u t2)
end.

Definition subst_list (s : substType) t : btree :=
  foldl (fun t (p : var * btree)  => subst p.1 p.2 t) t s.

Definition constr := (btree * btree)%type.
Definition constr_list := list constr.

Definition subst_pair s (p : constr) := (subst_list s p.1, subst_list s p.2).

Fixpoint union (vl1 vl2 : list var) :=
  if vl1 is v :: vl then
    if v \in vl2 then union vl vl2 else union vl (v :: vl2)
  else vl2.

Fixpoint vars (t : btree) : list var :=
  match t with
  | btVar x => [:: x]
  | btInt _ => nil
  | btNode t1 t2 => union (vars t1) (vars t2)
  end.

Definition unifiesb s t1 t2 := subst_list s t1 == subst_list s t2.
Definition unifiesb_pairs (s : substType) := all (fun p => unifiesb s p.1 p.2).

Fixpoint size_tree (t : btree) : nat :=
  if t is btNode t1 t2 then 1 + size_tree t1 + size_tree t2 else 1.

Definition size_pairs (l : constr_list) :=
  sumn [seq size_tree p.1 + size_tree p.2 | p <- l].

Fixpoint vars_pairs (l : constr_list) : list var :=
  match l with
  | nil => nil
  | (t1, t2) :: r =>
    union (union (vars t1) (vars t2)) (vars_pairs r)
  end.

End Definitions.

Section op.
Lemma sconsA : associative subst_comp.
Proof. exact: List.app_assoc. Qed.

Lemma scons0s : left_id subst0 subst_comp.
Proof. done. Qed.

Lemma sconss0 : right_id subst0 subst_comp.
Proof. exact: List.app_nil_r. Qed.

HB.instance Definition substIsLaw :=
  Monoid.isLaw.Build substType subst0 subst_comp sconsA scons0s sconss0.

Definition op := HB.pack_for (Monoid.law subst0) subst_comp substIsLaw.
End op.

Section Lemmas.

Lemma mem_tail {A : eqType} x a {l : seq.seq A} : x \in l -> x \in a::l.
Proof. rewrite inE => ->; exact/orbT. Qed.
Hint Resolve mem_head mem_tail : core.

Lemma in_union_or v vl1 vl2 :
  v \in union vl1 vl2 = (v \in vl1) || (v \in vl2).
Proof.
  elim: vl1 vl2 => //= x vl IH vl2.
  case: ifP => Hx.
  - rewrite inE IH.
    case/boolP: (v == x) => // /eqP ->.
    by rewrite Hx orbT.
  - by rewrite IH !inE orbA (orbC (v == x)).
Qed.

Lemma uniq_union vl1 vl2 : uniq vl2 -> uniq (union vl1 vl2).
Proof.
  elim: vl1 vl2 => //= v vl IH vl2 H.
  case: ifP => Hv; by rewrite IH //= Hv.
Qed.

Lemma uniq_vars_pairs l : uniq (vars_pairs l).
Proof. elim: l => //= -[t1 t2] l IH. exact: uniq_union. Qed.

Lemma size_union2 l1 l2 : size (union l1 l2) >= size l2.
Proof.
  elim: l1 l2 => //= v l1 IH l2.
  case: ifP => Hv //.
  refine (leq_trans _ (IH _)); exact: ltnW.
Qed.

Lemma eq_btNode t1_1 t1_2 t2_1 t2_2 :
  btNode t1_1 t1_2 = btNode t2_1 t2_2 <->
  (t1_1 = t2_1) /\ (t1_2 = t2_2).
Proof. by split; case => // -> ->. Qed.

Lemma eqb_btNode t1_1 t1_2 t2_1 t2_2 :
  btNode t1_1 t1_2 == btNode t2_1 t2_2 =
  (t1_1 == t2_1) && (t1_2 == t2_2).
Proof.
case: andP.
- by case => /eqP -> /eqP ->; apply: eqxx.
- by apply: contra_notF => /eqP [] -> ->; rewrite !eqxx.
Qed.

Lemma subst_btInt s b : subst_list s (btInt b) = btInt b.
Proof. by elim:s. Qed.

Lemma subst_btNode s t1 t2:
  subst_list s (btNode t1 t2) = btNode (subst_list s t1) (subst_list s t2).
Proof.
move: t1 t2.
elim:s => // a l IH *.
exact: IH.
Qed.

Lemma subst_zero t : subst_list subst0 t = t.
Proof. done. Qed.

Lemma subst_same v t' t : v \notin (vars t) -> subst v t' t = t.
Proof.
  elim: t => //= [x | t1 IH1 t2 IH2].
  - by rewrite inE eq_sym => /negbTE ->.
  - by rewrite in_union_or negb_or => /andP[] /IH1 -> /IH2 ->.
Qed.

(*
Lemma substD : {morph subst: s1 s2 / subst_comp s1 s2 >-> s2 \o s1}.
Proof. by move=> s1 s2; apply: boolp.funext; elim => //= t1 -> t2 ->. Qed.
*)

Lemma unifiesb_same sm t : unifiesb sm t t.
Proof. by rewrite /unifiesb. Qed.

Lemma unifiesb_pairs_same sm t l :
  unifiesb_pairs sm l -> unifiesb_pairs sm ((t,t) :: l).
Proof.
  move=> H; apply /andP; split => //.
  exact: unifiesb_same.
Qed.

Lemma unifiesb_swap sm t1 t2 :
  unifiesb sm t1 t2 = unifiesb sm t2 t1.
Proof. by rewrite /unifiesb eq_sym. Qed.

Lemma unifiesb_pairs_swap sm t1 t2 l :
  unifiesb_pairs sm ((t1, t2) :: l) = unifiesb_pairs sm ((t2, t1) :: l).
Proof. elim: l => /= [ | a l IH ]; by rewrite unifiesb_swap. Qed.

Definition unifies (s : substType) t1 t2 := subst_list s t1 = subst_list s t2.
Definition unifies_pairs (s : substType) (l : constr_list) :=
  forall t1 t2, (t1,t2) \in l -> unifies s t1 t2.

Lemma unif_pairs sm l : reflect (unifies_pairs sm l) (unifiesb_pairs sm l).
Proof.
apply/(iffP allP) => /= H.
- by move=> t1 t2 Ht; apply/eqP/(H (t1,t2)).
- by case=> t1 t2 Ht; apply/eqP/(H t1 t2).
Qed.

End Lemmas.

Section Unify.

Variables (N : exceptMonad) (M : actionRunFailMonad op N).
Let write := write M.

Section Unify1.

Variable unify2 : constr_list -> M unit.

Definition unify_subst x t r : M unit :=
  if x \in vars t then fail
  else (fun f => write f >> unify2 (map (subst_pair f) r)) [:: (x, t)].

Fixpoint unify1 (h : nat) (l : constr_list) : M unit :=
if h is h.+1 then
  match l with
  | nil => Ret tt
  | (btVar x, btVar y) :: r =>
    if x == y then unify1 h r
    else unify_subst x (btVar y) r
  | (btVar x, t) :: r =>
    unify_subst x t r
  | (t, btVar x) :: r =>
    unify_subst x t r
  | (btInt x, btInt y) :: r =>
    if x == y then unify1 h r else fail
  | (btNode t1 t2, btNode t1' t2') :: r =>
    unify1 h ((t1, t1') :: (t2, t2') :: r)
  | _ => fail
  end
else
  fail.

End Unify1.

Section Unify2.

Fixpoint unify2 (h : nat) l : M unit :=
  if h is h.+1 then unify1 (unify2 h) (size_pairs l + 1) l else fail.

End Unify2.

Definition unify t1 t2 : N (unit * substType)%type :=
  let l := [:: (t1,t2)] in
  runActionT (unify2 (size (vars_pairs l) + 1) l).

Section Soundness.

Lemma unifiesb_subst s v t :
  v \notin vars t -> unifiesb (subst_comp [:: (v, t)] s) (btVar v) t.
Proof. by move => *; rewrite /unifiesb /= eqxx subst_same. Qed.

Lemma unifiesb_pairs_subst s v t l :
  v \notin vars t ->
  unifiesb (subst_comp [:: (v, t)] s) (btVar v) t &&
  unifiesb_pairs (subst_comp [:: (v, t)] s) l =
  unifiesb_pairs s ([seq subst_pair [:: (v, t)] i | i <- l]).
Proof.
move => nin; elim: l => /= [| a l IHl].
- by rewrite unifiesb_subst.
- by rewrite -IHl [RHS]andbCA.
Qed.

Lemma unify_subst_sound h v t l :
  (forall l,
    runActionT (unify2 h l) >>=
    assert (fun x => unifiesb_pairs x.2 l) =
    runActionT (unify2 h l)
  ) ->
  runActionT (unify_subst (unify2 h) v t l) >>= 
    assert (fun x => unifiesb_pairs x.2 ((btVar v, t) :: l)) =
  runActionT (unify_subst (unify2 h) v t l).
Proof.
rewrite /unify_subst.
case/boolP: (v \in _) => Hocc // IH.
  by rewrite runActionTfail bindfailf.
rewrite runActionTbind runActionTwrite !bindretf !bindA /= -[in RHS]IH.
under eq_bind do rewrite bindretf /=.
under eq_bind do rewrite assertE unifiesb_pairs_subst //.
rewrite bindA.
by under [in RHS]eq_bind do rewrite assertE bindA bindretf.
Qed.

Theorem unify2_sound h l :
  runActionT (unify2 h l) >>= assert (fun x => unifiesb_pairs x.2 l) =
  runActionT (unify2 h l).
Proof.
elim: h l => /= [l | h IH l].
- by rewrite runActionTfail bindfailf.
move: (size_pairs l + 1) => h'.
elim: h' l => //= [l | h' IH' [| [t1 t2] l] /=].
- by rewrite runActionTfail bindfailf.
- under eq_bind do rewrite assertE guardT bindskipf.
  by rewrite bindmret.
destruct t1, t2; try by rewrite runActionTfail bindfailf.
- case: ifPn; move=> /eqP eq.
  + rewrite eq -[RHS]IH'.
    by under eq_bind do rewrite assertE unifiesb_same //=.
  + exact/unify_subst_sound.
- exact/unify_subst_sound.
- exact/unify_subst_sound.
- under eq_bind do rewrite assertE unifiesb_swap.
  exact/unify_subst_sound.
- have []:= eqVneq n n0 => /= H; try by rewrite runActionTfail bindfailf.
  by under eq_bind do rewrite assertE H unifiesb_same /=.
- under eq_bind do rewrite assertE unifiesb_swap.
  exact/unify_subst_sound.
- by under eq_bind do rewrite assertE /unifiesb !subst_btNode eqb_btNode -andbA.
Qed.

Corollary soundness t1 t2:
  unify t1 t2 >>= assert (fun x => unifiesb x.2 t1 t2) = unify t1 t2.
Proof.
rewrite /unify /=.
have Huup: forall s t1 t2, unifiesb s t1 t2 = unifiesb_pairs s [:: (t1, t2)]
by move => *; rewrite /= andbT.
under eq_bind do rewrite assertE Huup.
exact: unify2_sound.
Qed.

End Soundness.

Section Completeness.

Lemma not_unifiesb_occur v t s :
  btVar v != t -> v \in vars t -> ~unifiesb s (btVar v) t.
Proof.
move=> vt Ht /eqP Hun.
have Hs: size_tree (subst_list s (btVar v)) >= size_tree (subst_list s t) by rewrite Hun.
elim: t {Hun} vt Ht Hs => //= [v' | t1 IH1 t2 IH2] vt.
- rewrite inE => /eqP Hv.
  by rewrite Hv eq_refl in vt.
- rewrite in_union_or.
  move: IH1 IH2.
  wlog : t1 t2 / (v \in vars t1).
    move=> IH IH1 IH2 /orP[] Hv Hs.
    - by apply: (IH t1 t2) => //; rewrite Hv.
    - apply: (IH t2 t1) => //=.
      by rewrite Hv.
      by move: Hs; rewrite !subst_btNode /= addnAC => ->.
  move=> Hv IH1 _ _.
  case vt1: (btVar v == t1) IH1 => IH1.
    by rewrite -(eqP vt1) subst_btNode /= -addnA add1n ltnNge leq_addr.
  move/(_ isT Hv) in IH1.
  move=> Hsz; apply IH1.
  apply/leq_trans/Hsz.
  by rewrite subst_btNode /= addnAC leq_addl.
Qed.

Lemma unifiesb_extend s v t t' :
  unifiesb s (btVar v) t -> unifiesb s (subst v t t') t'.
Proof.
  rewrite /unifiesb.
  elim: t' => //= [v' | t1 IH1 t2 IH2].
  - rewrite /subst_list => /eqP Heq.
    case: ifP => // /eqP <-.
    by rewrite Heq.
  - move => Heq.
    have: subst_list s (subst v t t1) == subst_list s t1 by exact/IH1/Heq.
    have: subst_list s (subst v t t2) == subst_list s t2 by exact/IH2/Heq.
    by rewrite !subst_btNode => /eqP -> /eqP ->.
Qed.

Lemma unifiesb_pairs_extend s v t l :
  unifiesb_pairs s ((btVar v, t) :: l) ->
  unifiesb_pairs s (map (subst_pair [:: (v, t)]) l).
Proof.
  move => /= /andP [h1 h2].
  apply /unif_pairs.
  move => t1 t2 /mapP /= [] [t3 t4] Hl [-> ->].
  have Hv : unifiesb s (btVar v) t by apply h1.
  apply/eqP.
  have: unifiesb s (subst v t t3) t3 by apply:unifiesb_extend.
  have: unifiesb s (subst v t t4) t4 by apply:unifiesb_extend.
  rewrite /unifiesb => /eqP -> /eqP ->.
  move/unif_pairs in h2.
  exact /eqP/h2/Hl.
Qed.

Lemma unifiesb_pairs_btNode s tl1 tl2 tr1 tr2 l :
  unifiesb s (btNode tl1 tl2) (btNode tr1 tr2) ->
  unifiesb_pairs s l ->
  unifiesb_pairs s ((tl1,tr1)::(tl2,tr2)::l).
Proof.
  rewrite /unifiesb !subst_btNode => /eqP /eq_btNode -[H1 H2] Hs.
  apply/unif_pairs => t3 t4.
  rewrite !inE.
  case/orP => [/eqP[-> ->] // |].
  case/orP => [/eqP[-> ->] // |].
  by apply/unif_pairs.
Qed.

Definition moregen s s' :=
  exists s2, forall t, subst_list s' t = subst_list s2 (subst_list s t).

Lemma moregen_extend s v t s1 :
  unifiesb s (btVar v) t ->
  moregen s1 s ->
  moregen (subst_comp [:: (v, t)] s1) s.
Proof.
  move=> Hs [s2 Hs2].
  exists s2 => t' /=.
  rewrite -Hs2.
  exact/esym/eqP/unifiesb_extend.
Qed.

Lemma subst_del x t t' :
  x \notin vars t ->
  x \notin vars (subst x t t').
Proof.
  move=> Hv.
  elim: t' => //= [v | t1 IH1 t2 IH2].
  - case: ifP => //=.
    by rewrite inE eq_sym => ->.
  - by rewrite in_union_or negb_or IH1 IH2.
Qed.

Lemma subst_pairs_del x t l :
  x \notin vars t ->
  x \notin (vars_pairs (map (subst_pair [:: (x, t)]) l)).
Proof.
  move=> Hv.
  elim: l => //= -[t1 t2] l IH.
  by rewrite !in_union_or !negb_or /= IH !subst_del.
Qed.

Lemma subst_sub x t t' :
  {subset vars (subst x t t') <=
  union (vars t) (vars t')}.
Proof.
  elim: t' => //= [v | t1 IH1 t2 IH2] y.
  - rewrite in_union_or.
    case: ifP => [/eqP <- | _] -> //=.
    by rewrite orbT.
  - rewrite !in_union_or => /orP[/IH1 | /IH2];
    rewrite in_union_or => /orP[] -> //;
    by rewrite !orbT.
Qed.

Lemma subst_pairs_sub x t l :
  {subset vars_pairs (map (subst_pair [:: (x, t)]) l) <=
  union (vars t) (vars_pairs l)}.
Proof.
  elim: l => //= -[t1 t2] l IH /= y.
  rewrite !in_union_or => /orP[/orP[] /subst_sub| /IH];
  rewrite in_union_or => /orP[] -> //;
  by rewrite !orbT.
Qed.

Lemma vars_pairs_decrease x t l :
  x \notin (vars t) ->
  size (vars_pairs (map (subst_pair [:: (x, t)]) l)) <
  size (vars_pairs ((btVar x, t) :: l)).
Proof.
  move=> Hx.
  apply (@leq_trans (size (x :: vars_pairs (map (subst_pair [:: (x, t)]) l)))) => //.
  apply uniq_leq_size.
    by rewrite /= uniq_vars_pairs subst_pairs_del.
  move=> /= y.
  rewrite (negbTE Hx) inE => /orP[/eqP ->|].
    by rewrite in_union_or inE eqxx.
  move/subst_pairs_sub.
  rewrite !in_union_or !inE => /orP[] ->; by rewrite orbT.
Qed.

Lemma size_vars_pairs_swap t1 t2 l :
  size (vars_pairs ((t1,t2) :: l)) =
  size (vars_pairs ((t2,t1) :: l)).
Proof.
  apply/eqP; rewrite eqn_leq /=.
  apply/andP; split; apply uniq_leq_size;
  rewrite ?(uniq_union, uniq_vars_pairs) //= => y;
  rewrite !in_union_or => /orP[/orP[]|] -> //;
  by rewrite orbT.
Qed.

Lemma size_vars_pairs_btNode t1 t2 t'1 t'2 l :
  size (vars_pairs ((btNode t1 t2, btNode t'1 t'2) :: l)) =
  size (vars_pairs ((t1, t'1) :: (t2, t'2) :: l)).
Proof.
  apply/eqP; rewrite eqn_leq /=.
  apply/andP; split; apply uniq_leq_size;
  rewrite ?(uniq_union, uniq_vars_pairs) //= => y;
  rewrite !in_union_or; do !case/orP; move ->;
  by rewrite ?orbT.
Qed.

Lemma unify_subst_complete s h v t l :
  (forall l,
    h > size (vars_pairs l) -> unifiesb_pairs s l ->
    exists s1,
    (forall t' (f : substType -> substType),
    catch (
      runActionT (unify2 h l) >>=
      assert (fun x => subst_list x.2 t' == subst_list s1 t') >>=
      fun x => Ret (Some (f x.2))
    ) (Ret None) =
    runActionT (unify2 h l) >>= fun x => Ret (Some (f x.2)))
    /\ moregen s1 s) ->
  h.+1 > size (vars_pairs ((btVar v, t) :: l)) ->
  unifiesb_pairs s ((btVar v, t) :: l) ->
  btVar v != t ->
  exists s1,
  (forall t' (f : substType -> substType),
  catch (
    runActionT (unify_subst (unify2 h) v t l) >>=
    assert (fun x => subst_list x.2 t' == subst_list s1 t') >>=
    fun x => Ret (Some (f x.2))
  ) (Ret None) =
  runActionT (unify_subst (unify2 h) v t l) >>= fun x => Ret (Some (f x.2)))
  /\ moregen s1 s.
Proof.
  move=> IHh Hh Hs Hv.
  rewrite /unify_subst.
  case: ifPn => vt.
    move: Hs => /= /andP [Hs1 ?].
    elim: (@not_unifiesb_occur v t s) => //.
  case: (IHh (map (subst_pair [:: (v, t)]) l)) => //.
      have Hhv := @vars_pairs_decrease v t l vt.
      apply (leq_trans Hhv).
      by rewrite -ltnS.
    by apply: unifiesb_pairs_extend.
  move=> s1 [Hun Hmg].
  exists (subst_comp [:: (v, t)] s1); split => [t' f|].
  rewrite runActionTbind runActionTwrite bindretf /= !bindA.
  under [RHS]eq_bind do rewrite bindretf => /=.
  under eq_bind do rewrite bindretf.
  have Hcomp: forall x : unit * substType,
    f (subst_comp [:: (v, t)] x.2) =
    (f \o (subst_comp [:: (v, t)])) x.2 by done.
  under [RHS]eq_bind do rewrite Hcomp.
  rewrite -(Hun(subst v t t')) /assert /guard !bindA.
  have HA: forall m (x : unit * substType),
    (m >> Ret x) >>=
      (fun x : unit * substType => Ret (Some ((f \o subst_comp [:: (v, t)]) x.2))) =
    (m >> Ret (x.1, subst_comp [:: (v, t)] x.2)) >>=
      (fun x : unit * substType => Ret (Some (f x.2)))
  by move => *; rewrite !bindA !bindretf.
  by under eq_bind do rewrite -HA.
  apply: moregen_extend => //.
  by move: Hs => /andP [-> ?].
Qed.

Theorem unify2_complete s h l :
  h > size (vars_pairs l) ->
  unifiesb_pairs s l ->
  exists s1,
  (forall t (f : substType -> substType),
  catch (
    runActionT (unify2 h l) >>=
    assert (fun x => subst_list x.2 t == subst_list s1 t) >>=
    fun x => Ret (Some (f x.2))
  ) (Ret None) =
  runActionT (unify2 h l) >>= fun x => Ret (Some (f x.2)))
  /\ moregen s1 s.
Proof.
  elim: h l => //= h IH l Hh.
  move Hh': (size_pairs l + 1) => h'.
  have {Hh'} : h' > size_pairs l.
    by rewrite -Hh' addn1 ltnS.
  elim: h' l Hh => //= h' IH' [] //=.
    move => *; exists subst0; split => // [t f|].
    by rewrite runActionTret !bindretf /assert eqxx bindskipf bindretf catchret.
    exists s => t; by rewrite subst_zero.
  case=> t1 t2 l Hh Hh' Hs.
  destruct t1, t2 => /=.
  (* VarVar *)
- case: ifP => vv0.
    move/eqP in vv0; subst v0.
    apply IH'.
    + apply/leq_trans: Hh.
      rewrite ltnS.
      exact: size_union2.
    + rewrite /size_pairs /= -!addnA !add1n ltnS in Hh'.
      exact: ltnW.
    + move: Hs => /andP [? Hs]; apply Hs; by auto.
  have Hvar : btVar v != btVar v0.
    apply/negP => /eqP[] /eqP.
    by rewrite vv0.
  exact: unify_subst_complete.
  (* VarSym *)
- exact: unify_subst_complete.
  (* VarFork *)
- exact: unify_subst_complete.
  (* SymVar *)
- apply unify_subst_complete => //.
  by rewrite unifiesb_pairs_swap.
  (* SymSym *)
- move: Hs => /= /andP [Hs1 Hs2].
  elim eq: (n == n0).
    apply IH' => //.
      rewrite /size_pairs /= -!addnA !add1n ltnS in Hh'.
      exact: ltnW.
  have: unifiesb s (btInt n) (btInt n0) by apply Hs1.
  rewrite /unifiesb !subst_btInt => /eqP -[].
  by move: eq => /eqP.
  (* SymFork *)
- move: Hs => /= /andP Hs.
  have : unifiesb s (btInt n) (btNode t2_1 t2_2) by apply Hs.
  by rewrite /unifiesb subst_btInt subst_btNode.
  (* ForkVar *)
- apply unify_subst_complete => //.
    by rewrite size_vars_pairs_swap.
  by rewrite unifiesb_pairs_swap.
  (* ForkSym *)
- move: Hs => /= /andP Hs.
  have : unifiesb s (btNode t1_1 t1_2) (btInt n) by apply Hs.
  by rewrite /unifiesb subst_btInt subst_btNode.
  (* ForkFork *)
- apply: IH'.
      by rewrite -size_vars_pairs_btNode.
    rewrite /size_pairs /= in Hh' *.
    rewrite !add1n !(addnS,addSn) in Hh'.
    rewrite !addnA in Hh' *.
    rewrite (addnAC (size_tree t1_1)) in Hh'.
    exact: ltnW.
  move: Hs => /andP [*].
  exact: unifiesb_pairs_btNode.
Qed.

Corollary unify_complete s t1 t2 :
  unifiesb s t1 t2 ->
  exists s1,
  (forall t,
  catch (
    unify t1 t2 >>=
    assert (fun x => subst_list x.2 t == subst_list s1 t) >>=
    fun x => Ret (Some x.2)
  ) (Ret None) =
  unify t1 t2 >>= fun x => Ret (Some x.2))
  /\ moregen s1 s.
Proof.
move => Hs.
have [s' [Hf Hmg]]: exists s1 : substType, (forall t (f : substType -> substType),
  catch ((unify t1 t2 >>= assert (fun x => subst_list x.2 t == subst_list s1 t)) >>=
         (fun x => Ret (Some (f x.2)))) (Ret None) =
  unify t1 t2 >>= (fun x => Ret (Some (f x.2)))) /\ 
  moregen s1 s.
apply unify2_complete.
by rewrite addnC.
by rewrite /unifiesb_pairs /all Hs.
exists s'; split => [t|//].
exact: Hf(id).
Qed.

End Completeness.

End Unify.
