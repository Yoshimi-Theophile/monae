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

Definition substType : UU0 := var -> btree.

Definition subst0 : substType := btVar.

Definition subst1 (x : var) (t : btree) (v : var) : btree :=
  if v == x then t else btVar v.

(* t[x\u] *)
Fixpoint subst (s : var -> btree) t : btree :=
match t with
| btVar v => s v
| btInt _ => t
| btNode t1 t2 => btNode (subst s t1) (subst s t2)
end.

Definition subst_comp (s1 s2 : var -> btree) (v : var) : btree :=
  subst s2 (s1 v).

Definition subst_rul := (var * btree)%type.
Definition constr := (btree * btree)%type.
Definition constr_list := list constr.

Definition subst_pair s (p : constr) := (subst s p.1, subst s p.2).

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

Definition unifies (sm : substType) t1 t2 := subst sm t1 == subst sm t2.
Definition unifies_pairs (sm : substType) := all (fun p => unifies sm p.1 p.2).

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
Proof.
  move => x ? ?; rewrite /subst_comp.
  apply: boolp.funext => v /=.
  by elim: (x v) => //= t1 -> t2 ->.
Qed.

Lemma scons0s : left_id subst0 subst_comp.
Proof.
  move => x; apply: boolp.funext => v.
  rewrite /subst_comp //=.
Qed.

Lemma sconss0 : right_id subst0 subst_comp.
Proof.
  move => x; apply: boolp.funext => v.
  rewrite /subst_comp.
  by elim: (x v) => //= t1 -> t2 ->.
Qed.

HB.instance Definition substIsLaw :=
  Monoid.isLaw.Build substType subst0 subst_comp sconsA scons0s sconss0.

Definition op := HB.pack_for (Monoid.law subst0) subst_comp substIsLaw.
End op.

Section Lemmas.

Lemma mem_tail {A:eqType} x a {l : seq A} : x \in l -> x \in a::l.
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
Proof.
split => [h | [-> -> //]]; split.
by injection h => ? ->.
by injection h => -> ?.
Qed.

Lemma eqb_btNode t1_1 t1_2 t2_1 t2_2 :
  btNode t1_1 t1_2 == btNode t2_1 t2_2 =
  (t1_1 == t2_1) && (t1_2 == t2_2).
Proof.
case_eq ((t1_1 == t2_1) && (t1_2 == t2_2)) => [/andP | ].
- move => [/eqP -> /eqP ->].
  exact/eqP.
- have: ~~((t1_1 == t2_1) && (t1_2 == t2_2)) ->
        ~~(btNode t1_1 t1_2 == btNode t2_1 t2_2).
  apply: contraNneq => h.
  apply eq_btNode in h; destruct h; generalize H H0.
  by move => -> ->; rewrite !eq_refl.
  move => h h1.
  apply: eqP.
  rewrite eqbF_neg.
  apply: h.
  rewrite -eqbF_neg.
  apply /eqP.
  exact/h1.
Qed.

Lemma subst_btInt s b : subst s (btInt b) = btInt b.
Proof. by rewrite /subst //=. Qed.

Lemma subst_btNode s t1 t2:
  subst s (btNode t1 t2) = btNode (subst s t1) (subst s t2).
Proof. by rewrite /subst. Qed.

Lemma subst_same v t' t : v \notin (vars t) -> subst (subst1 v t') t = t.
Proof.
  elim: t => //= [x | t1 IH1 t2 IH2].
  - by rewrite /subst1 inE eq_sym => /negbTE ->.
  - by rewrite /subst1 in_union_or negb_or => /andP[] /IH1 -> /IH2 ->.
Qed.

Lemma subst_through s v t t':
  subst (fun v0 : var => subst s (subst1 v t' v0)) t =
  subst s (subst (subst1 v t') t).
Proof. elim: t => //= ? -> ? -> //. Qed.

Lemma unifies_same sm t : unifies sm t t.
Proof. by rewrite /unifies. Qed.

Lemma unifies_pairs_same sm t l :
  unifies_pairs sm l -> unifies_pairs sm ((t,t) :: l).
Proof.
  move=> H; apply /andP; split => //.
  exact: unifies_same.
Qed.

Lemma unifies_swap sm t1 t2 :
  unifies sm t1 t2 -> unifies sm t2 t1.
Proof. by rewrite /unifies => /eqP ->. Qed.

Lemma unifies_pairs_swap sm t1 t2 l :
  unifies_pairs sm ((t1, t2) :: l) -> unifies_pairs sm ((t2, t1) :: l).
Proof.
  move=> /= /andP h.
  elim: h => [hl hr].
  apply /andP; split => //.
  exact/unifies_swap.
Qed.

Definition unifiesP (sm : substType) t1 t2 := subst sm t1 = subst sm t2.
Definition unifiesP_pairs (sm : substType) (l : constr_list) :=
  forall t1 t2, (t1,t2) \in l -> unifiesP sm t1 t2.

Lemma unifP sm t1 t2 : unifiesP sm t1 t2 <-> unifies sm t1 t2.
Proof.
split => h.
- rewrite /unifies h //.
- exact: eqP.
Qed.

Lemma unifP_split sm t1 t2 l :
  unifiesP_pairs sm ((t1, t2) :: l) ->
  unifiesP sm t1 t2 /\ unifiesP_pairs sm l.
Proof.
intro; split.
- exact/H/mem_head.
- rewrite /unifiesP_pairs => tt1 tt2.
  intros; apply H.
  rewrite in_cons.
  apply /orP; by right.
Qed.

Lemma unifP_merge sm t1 t2 l :
  unifiesP sm t1 t2 /\ unifiesP_pairs sm l ->
  unifiesP_pairs sm ((t1, t2) :: l).
Proof.
intro h_; case h_ => hl hr.
rewrite /unifiesP_pairs => tt1 tt2 H.
rewrite in_cons in H; generalize H.
move => /orP [/eqP h|h].
- apply pair_equal_spec in h.
  by case h => -> ->.
- exact/hr/h.
Qed.

Lemma unifP_pairs sm l : unifiesP_pairs sm l <-> unifies_pairs sm l.
Proof.
split => h; induction l => //=;
case_eq a => t1 t2 eq /=;
rewrite eq in h.
- apply /andP.
  have: unifiesP sm t1 t2 /\ unifiesP_pairs sm l
    by exact/unifP_split/h.
  move => [h1 h2]; split.
  + exact/unifP/h1.
  + exact/IHl/h2.
- apply unifP_merge.
  generalize h.
  move => /andP [h1 h2]; split.
  + exact/unifP/h1.
  + exact/IHl/h2.
Qed.

End Lemmas.

Section Unify.

Variables (N : failMonad) (M : actionRunFailMonad op N).
Let write := write M.

Section Unify1.

Variable unify2 : constr_list -> M unit.

Definition unify_subst x t r : M unit :=
  if x \in vars t then fail
  else (fun f => write f >> unify2 (map (subst_pair f) r)) (subst1 x t).

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

Lemma unify_fail A B (x y : (A * substType) -> N B) :
  runActionT (fail : M A) >>= x = runActionT (fail : M A) >>= y.
Proof. by rewrite runActionTfail !bindfailf. Qed.
Hint Resolve unify_fail : core.

Lemma unifies_subst s v t :
  (v \in vars t) = false -> 
  unifies (subst_comp (subst1 v t) s) (btVar v) t.
Proof.
move => /eqP Hnin /=; rewrite /unifies /subst_comp /=.
change (subst1 v t v) with (if v == v then t else btVar v).
have: v == v by exact/eq_refl.
move => ->.
rewrite eqbF_neg in Hnin.
rewrite subst_through // subst_same //.
Qed.

Lemma unifies_pairs_subst s v t l :
  (v \in vars t) = false ->
  unifies (subst_comp (subst1 v t) s) (btVar v) t &&
  unifies_pairs (subst_comp (subst1 v t) s) l =
  unifies_pairs s ([seq subst_pair (subst1 v t) i | i <- l]).
Proof.
move => nin.
elim: l => /= [| a l IHl].
- have: unifies (subst_comp (subst1 v t) s) (btVar v) t.
  exact/unifies_subst/nin.
  by move => ->.
- rewrite -IHl [RHS]andbCA !andbA.
  have: unifies (subst_comp (subst1 v t) s) a.1 a.2 =
        unifies s (subst (subst1 v t) a.1) (subst (subst1 v t) a.2).
  rewrite /subst_comp /unifies /=.
  rewrite !subst_through => //.
  by move => ->.
Qed.

Lemma unify_subst_sound h v t l :
  (forall l,
    runActionT (unify2 h l) >>=
    (fun x => assert (fun _ => unifies_pairs x.2 l) tt) =
    runActionT (unify2 h l) >> Ret tt
  ) ->
  runActionT (unify_subst (unify2 h) v t l) >>= 
    (fun x => assert (fun _ => unifies_pairs x.2 ((btVar v, t) :: l)) tt) =
  runActionT (unify_subst (unify2 h) v t l) >> Ret tt.
Proof.
rewrite /unify_subst.
case Hocc: (v \in _) => // IH.
rewrite runActionTbind runActionTwrite !bindretf !bindA /=.
have: forall x : unit * substType,
      (fun x => Ret (x.1, subst_comp (subst1 v t) x.2) >>=
        (fun x0 => assert (fun=> unifies x0.2 (btVar v) t && unifies_pairs x0.2 l) tt)) x =
      (fun x => @assert N unit (fun=> unifies (subst_comp (subst1 v t) x.2) (btVar v) t &&
        unifies_pairs (subst_comp (subst1 v t) x.2) l) tt) x
by move => x; rewrite bindretf /=.
have: forall x : unit * substType,
      (fun x => Ret (x.1, subst_comp (subst1 v t) x.2) >> Ret tt) x =
      (fun x => Ret tt : N unit) x
by move => x; rewrite bindretf.
move => /boolp.funext -> /boolp.funext ->.
have: forall x : unit * substType,
      assert (fun=> unifies (subst_comp (subst1 v t) x.2) (btVar v) t &&
                        unifies_pairs (subst_comp (subst1 v t) x.2) l) tt=
      @assert N unit (fun=> unifies_pairs x.2 ([seq subst_pair (subst1 v t) i | i <- l])) tt.
move => x; rewrite unifies_pairs_subst => //=.
by move => /boolp.funext ->.
Qed.

Lemma unify2_sound h l :
  runActionT (unify2 h l) >>= (fun x => assert (fun _ => unifies_pairs x.2 l) tt) =
  runActionT (unify2 h l) >> Ret tt.
Proof.
elim: h l => /= [l | h IH l].
- by exact/unify_fail.
move: (size_pairs l + 1) => h'.
elim: h' l => //= [l | h' IH' [| [t1 t2] l] /=].
- by exact/unify_fail.
- by rewrite assertE guardT bindskipf.
destruct t1, t2; try by exact/unify_fail.
- case: ifP; move=> /eqP eq.
  + rewrite eq -IH'.
    have: forall x : unit * substType,
          (fun x => assert (fun=> unifies x.2 (btVar v0) (btVar v0) && unifies_pairs x.2 l) tt) x = 
          (fun x => @assert N unit (fun=> unifies_pairs x.2 l) tt) x
    by (intro x; rewrite unifies_same //=).
    by move => /boolp.funext ->.
  + exact/unify_subst_sound.
- exact/unify_subst_sound.
- exact/unify_subst_sound.
- have: forall x : unit * substType,
        (fun x => @assert N unit (fun=> unifies_pairs x.2 ((btVar v, btInt n) :: l)) tt) x = 
        (fun x => @assert N unit (fun=> unifies_pairs x.2 ((btInt n, btVar v) :: l)) tt) x
  by move => x /=; case Hswap: (unifies x.2 (btVar v) (btInt n)) => /=;
    rewrite /unifies eq_sym in Hswap; by rewrite /unifies Hswap.
  move => /boolp.funext /= <-; exact/unify_subst_sound.
- case_eq (n == n0) => /eqP /= H; try by exact/unify_fail.
  have: forall x : unit * substType,
        (fun x => assert (fun=> (unifies x.2 (btInt n) (btInt n0)) && unifies_pairs x.2 l) tt) x = 
        (fun x => @assert N unit (fun=> unifies_pairs x.2 l) tt) x
  by move => x /=; rewrite H unifies_same //.
  move => /boolp.funext ->. exact/IH'.
- have: forall x : unit * substType,
        (fun x => @assert N unit (fun=> unifies_pairs x.2 ((btVar v, (btNode t1_1 t1_2)) :: l)) tt) x = 
        (fun x => @assert N unit (fun=> unifies_pairs x.2 (((btNode t1_1 t1_2), btVar v) :: l)) tt) x
  by move => x /=; case Hswap: (unifies x.2 (btVar v) (btNode t1_1 t1_2)) => /=;
    rewrite /unifies eq_sym in Hswap; by rewrite /unifies Hswap.
  move => /boolp.funext /= <-; exact/unify_subst_sound.
- have: forall x : unit * substType,
        (fun x => @assert N unit
          (fun => (unifies x.2 (btNode t1_1 t1_2) (btNode t2_1 t2_2)) && unifies_pairs x.2 l) tt) x = 
        (fun x => @assert N unit (fun => unifies_pairs x.2 [:: (t1_1, t2_1), (t1_2, t2_2) & l]) tt) x.
  move => x; rewrite /unifies !subst_btNode eqb_btNode /unify.
  change (unifies_pairs x.2 [:: (t1_1, t2_1), (t1_2, t2_2) & l])
    with (unifies x.2 t1_1 t2_1 && unifies_pairs x.2 [:: (t1_2, t2_2) & l]).
  change (unifies_pairs x.2 [:: (t1_2, t2_2) & l])
    with (unifies x.2 t1_2 t2_2 && unifies_pairs x.2 l).
  by rewrite /unifies andbA.
  move => /boolp.funext ->.
  exact: IH'.
Qed.

Theorem soundness t1 t2:
  unify t1 t2 >>= (fun x => assert (fun _ => unifies x.2 t1 t2) tt) =
  unify t1 t2 >> Ret tt.
Proof.
rewrite /unify /=.
have: forall x : unit * substType,
      (fun x => assert (fun=> unifies x.2 t1 t2) tt) x =
      (fun x => @assert N unit (fun=> unifies_pairs x.2 [:: (t1, t2)]) tt) x.
have: forall x, unifies x t1 t2 = unifies_pairs x [:: (t1, t2)]
by move => ?; rewrite /= Bool.andb_true_r //.
by move => h ?; rewrite h.
move => /boolp.funext ->.
exact/unify2_sound.
Qed.

End Soundness.

Section Completeness.

(* ??? *)
Lemma not_unifies_occur v t s :
  btVar v != t -> v \in vars t -> ~unifies s (btVar v) t.
Proof.
rewrite /unifies.
move=> vt Ht /eqP Hun.
have Hs: size_tree (subst s (btVar v)) >= size_tree (subst s t) by rewrite Hun.
elim: t {Hun} vt Ht Hs => //= [v' | t1 IH1 t2 IH2] vt.
- rewrite inE => /eqP Hv.
  by rewrite Hv eq_refl in vt.
- rewrite in_union_or.
  move: IH1 IH2.
  wlog : t1 t2 / (v \in vars t1).
    move=> IH IH1 IH2 /orP[] Hv Hs.
    - by apply: (IH t1 t2) => //; rewrite Hv.
    - by apply: (IH t2 t1) => //; rewrite (Hv,addnAC).
  move=> Hv IH1 _ _.
  case vt1: (btVar v == t1) IH1 => IH1.
    by rewrite -(eqP vt1) -addnA add1n ltnNge leq_addr.
  move/(_ isT Hv) in IH1.
  move=> Hsz; apply IH1.
  apply/leq_trans/Hsz.
  by rewrite addnAC leq_addl.
Qed.

Lemma unifies_extend s v t t' :
  unifies s (btVar v) t -> unifies s (subst (subst1 v t) t') t'.
Proof.
  rewrite /unifies.
  elim: t' => //= [v' | t1 IH1 t2 IH2].
  - rewrite /subst1 => /eqP Heq.
    case: ifP => // /eqP ->.
    by rewrite Heq.
  - move => Heq.
    have: subst s (subst (subst1 v t) t1) == subst s t1 by exact/IH1/Heq.
    have: subst s (subst (subst1 v t) t2) == subst s t2 by exact/IH2/Heq.
    move => /eqP -> /eqP -> //.
Qed.

Lemma unifies_pairs_extend s v t l :
  unifies_pairs s ((btVar v, t) :: l) ->
  unifies_pairs s (map (subst_pair (subst1 v t)) l).
Proof.
  move => /= /andP [h1 h2].
  apply /unifP_pairs.
  move => t1 t2 /mapP /= [] [t3 t4] Hl [-> ->].
  have Hv : unifies s (btVar v) t by apply h1.
  apply unifP.
  have: unifies s (subst (subst1 v t) t3) t3 by apply:unifies_extend.
  have: unifies s (subst (subst1 v t) t4) t4 by apply:unifies_extend.
  rewrite /unifies => /eqP -> /eqP ->.
  apply unifP_pairs in h2.
  exact /eqP/h2/Hl.
Qed.

Lemma unifies_pairs_btNode s tl1 tl2 tr1 tr2 l :
  unifies s (btNode tl1 tl2) (btNode tr1 tr2) ->
  unifies_pairs s l ->
  unifies_pairs s ((tl1,tr1)::(tl2,tr2)::l).
Proof.
  rewrite /unifies !subst_btNode => /eqP /eq_btNode -[H1 H2] Hs.
  apply unifP_pairs => t3 t4.
  rewrite !inE.
  case/orP => [/eqP[-> ->] // |].
  case/orP => [/eqP[-> ->] // |].
  by apply unifP_pairs.
Qed.

Definition moregen s s' :=
  exists s2, forall t, subst s' t = subst s2 (subst s t).

(* 一般性を保ちながら拡張 *)
Lemma moregen_extend s v t s1 :
  unifies s (btVar v) t ->
  moregen s1 s ->
  moregen (subst_comp (subst1 v t) s1) s.
Proof.
  move=> Hs [s2 Hs2].
  exists s2 => t' /=.
  rewrite /subst_comp subst_through -Hs2.
  exact/esym/eqP/unifies_extend.
Qed.

Lemma subst_del x t t' : x \notin vars t -> x \notin vars (subst (subst1 x t) t').
Proof.
  move=> Hv.
  elim: t' => //= [v | t1 IH1 t2 IH2].
  - rewrite /subst1. case: ifP => //=.
    by rewrite inE eq_sym => ->.
  - by rewrite in_union_or negb_or IH1 IH2.
Qed.

Lemma subst_pairs_del x t l :
  x \notin vars t -> x \notin (vars_pairs (map (subst_pair (subst1 x t)) l)).
Proof.
  move=> Hv.
  elim: l => //= -[t1 t2] l IH.
  by rewrite !in_union_or !negb_or /= IH !subst_del.
Qed.

Lemma subst_sub x t t' : {subset vars (subst (subst1 x t) t') <= union (vars t) (vars t')}.
Proof.
  rewrite /subst1.
  elim: t' => //= [v | t1 IH1 t2 IH2] y.
  - rewrite in_union_or.
    case: ifP => [/eqP -> | _] -> //=.
    by rewrite orbT.
  - rewrite !in_union_or => /orP[/IH1 | /IH2];
    rewrite in_union_or => /orP[] -> //;
    by rewrite !orbT.
Qed.

Lemma subst_pairs_sub x t l :
  {subset vars_pairs (map (subst_pair (subst1 x t)) l) <= union (vars t) (vars_pairs l)}.
Proof.
  elim: l => //= -[t1 t2] l IH /= y.
  rewrite !in_union_or => /orP[/orP[] /subst_sub| /IH];
  rewrite in_union_or => /orP[] -> //;
  by rewrite !orbT.
Qed.

Lemma vars_pairs_decrease x t l :
  x \notin (vars t) ->
  size (vars_pairs (map (subst_pair (subst1 x t)) l))
    < size (vars_pairs ((btVar x, t) :: l)).
Proof.
  move=> Hx.
  apply (@leq_trans (size (x :: vars_pairs (map (subst_pair (subst1 x t)) l)))) => //.
  apply uniq_leq_size.
    by rewrite /= uniq_vars_pairs subst_pairs_del.
  move=> /= y.
  rewrite (negbTE Hx) inE => /orP[/eqP ->|].
    by rewrite in_union_or inE eqxx.
  move/subst_pairs_sub.
  rewrite !in_union_or !inE => /orP[] ->; by rewrite orbT.
Qed.

Lemma size_vars_pairs_swap t1 t2 l :
  size (vars_pairs ((t1,t2) :: l)) = size (vars_pairs ((t2,t1) :: l)).
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

Lemma unify_subs_complete s h v t l :
  (forall l,
    h > size (vars_pairs l) -> unifies_pairs s l ->
    exists s1,
    runActionT (unify2 h l) >>=
      (fun '(_, s1') => Ret s1') = Ret s1 /\
    moregen s1 s) ->
  h.+1 > size (vars_pairs ((btVar v, t) :: l)) ->
  unifies_pairs s ((btVar v, t) :: l) ->
  btVar v != t ->
  exists s1,
  runActionT (unify_subst (unify2 h) v t l) >>=
    (fun '(_, s1') => Ret s1') = Ret s1 /\
  moregen s1 s.
Admitted.

Theorem unify2_complete s h l :
  h > size (vars_pairs l) ->
  unifies_pairs s l ->
  exists s1,
  runActionT (unify2 h l) >>=
    (fun '(_, s1') => Ret s1') = Ret s1 /\
  moregen s1 s.
Admitted.

Theorem unify_complete s t1 t2 :
  unifies s t1 t2 ->
  exists s1,
  unify t1 t2 >>=
    (fun '(_, s1') => Ret s1') = Ret s1 /\
  moregen s1 s.
Admitted.

(*
Lemma unify_subs_complete s h v t l :
  (forall l,
    h > size (vars_pairs l) -> unifies_pairs s l ->
    exists s1, unify2 h l = Some s1 /\ moregen s1 s) ->
  h.+1 > size (vars_pairs ((Var v, t) :: l)) ->
  unifies_pairs s ((Var v, t) :: l) ->
  Var v != t ->
  exists s1, unify_subs  (unify2 h) v t l = Some s1 /\ moregen s1 s.
Proof.
  move=> IHh Hh Hs Hv.
  rewrite /unify_subs.
  case: ifPn => vt.
    elim: (not_unifies_occur v t s) => //.
    exact: Hs.
  case: (IHh (map (subs_pair v t) l)) => //.
      have Hhv := vars_pairs_decrease v t l vt.
      apply (leq_trans Hhv).
      by rewrite -ltnS.
    exact: unifies_pairs_extend.
  move=> s1 [Hun Hmg].
  rewrite Hun /=.
  exists ((v,t) :: s1); split => //.
  apply moregen_extend => //. exact: Hs.
Qed.

(* 完全性 *)
Theorem unify2_complete s h l :
  h > size (vars_pairs l) ->
  unifies_pairs s l ->
  exists s1, unify2 h l = Some s1 /\ moregen s1 s.
Proof.
  elim: h l => //= h IH l Hh.
  move Hh': (size_pairs l + 1) => h'.
  have {Hh'} : h' > size_pairs l.
    by rewrite -Hh' addn1 ltnS.
  elim: h' l Hh => //= h' IH' [] //=.
    move=>*; exists nil; split => //; by exists s.
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
    + move=> t1 t2 Hl; apply Hs; by auto.
  have Hvar : Var v != Var v0.
    apply/negP => /eqP[] /eqP.
    by rewrite vv0.
  exact: unify_subs_complete. 
  (* VarSym *)
- exact: unify_subs_complete.
  (* VarFork *)
- exact: unify_subs_complete.
  (* SymVar *)
- apply unify_subs_complete => //.
  exact: unifies_pairs_swap.
  (* SymSym *)
- destruct symbol_dec.
    subst.
    apply IH' => //.
      rewrite /size_pairs /= -!addnA !add1n ltnS in Hh'.
      exact: ltnW.
    move=> t1 t2 Hl.
    apply Hs; by auto.
  have : unifies s (Sym s0) (Sym s1) by apply Hs.
  by rewrite /unifies !subs_list_Sym => -[].
  (* SymFork *)
  have : unifies s (Sym s0) (Fork t2_1 t2_2) by apply Hs.
  by rewrite /unifies subs_list_Sym subs_list_Fork.
  (* ForkVar *)
  apply unify_subs_complete => //.
    by rewrite size_vars_pairs_swap.
  exact: unifies_pairs_swap.
  (* ForkSym *)
  have : unifies s (Fork t1_1 t1_2) (Sym s0) by apply Hs.
  by rewrite /unifies subs_list_Sym subs_list_Fork.
  (* ForkFork *)
  apply IH'.
      by rewrite -size_vars_pairs_Fork.
    rewrite /size_pairs /= in Hh' *.
    rewrite !add1n !(addnS,addSn) in Hh'.
    rewrite !addnA in Hh' *.
    rewrite (addnAC (size_tree t1_1)) in Hh'.
    exact: ltnW.
  apply unifies_pairs_Fork. exact: Hs.
  move=> t t' Hl. apply Hs; by auto.
Qed.

(* 短い完全性定理 *)
Corollary unify_complete s t1 t2 :
  unifies s t1 t2 ->
  exists s1, unify t1 t2 = Some s1 /\ moregen s1 s.
Proof.
  rewrite /unify addnC => Hs.
  apply unify2_complete => // x y.
  by rewrite inE => /eqP[-> ->].
Qed.
*)

End Completeness.

End Unify.
