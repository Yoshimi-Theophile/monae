From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.

Require Import preamble hierarchy monad_lib fail_lib state_lib.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

HB.mixin Record isMonadAction (S : UU0) (S0 : S) (op : Monoid.law S0)
  (M : UU0 -> UU0) of MonadFailR0 M := {
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
  (N : failMonad) (M : UU0 -> UU0) of @MonadAction S S0 op M & MonadFailR0 M := {
  runActionT : forall A : UU0, M A -> S -> N (A * S)%type;
  runActionTret : forall (A : UU0) (a : A) (s : S),
    @runActionT _ (Ret a) s = Ret (a, s) ;
  runActionTaction : forall (A : UU0) (s s' : S) (m : M A),
    @runActionT _ (action s m) s' = 
    @runActionT _ m S0 >>= fun x => Ret (x.1, op s s');
  runActionTfail : forall (A : UU0) (s : S),
    @runActionT _ (@fail [the failMonad of M] A) s = @fail N _;
  runActionTbind : forall (A B : UU0) (m : M A) (f : A -> M B) (s : S),
    @runActionT _ (m >>= f) s =
    @runActionT _ m s >>= fun x => @runActionT _ (f x.1) x.2 ;
}.

#[short(type=actionRunMonad)]
HB.structure Definition MonadActionRun S S0 op N:=
  {M of isMonadActionRun S S0 op N M & isMonadFailR0 M}.

Arguments runActionT {_ _ _ _ _ _}.

Section WriterMonad.

Variables (S : UU0) (S0 : S) (op : Monoid.law S0) (N : @actionMonad S S0 op).

Definition write (s : S) : N unit := action s (Ret tt).

Lemma writecomp a b :
  (write a) >> (write b) = write (op a b).
Proof. by rewrite /write -actionBind bindretf actionA. Qed.

Variable (M : @actionRunMonad S S0 op N).

(*
Lemma writeRun : forall (s s' : S),
  runActionT (write s) s' = Ret (tt, op s s').
*)

End WriterMonad.

Section Definitions.

Lemma mem_tail {A:eqType} x a {l : seq A} : x \in l -> x \in a::l.
Proof. rewrite inE => ->; exact/orbT. Qed.
Hint Resolve mem_head mem_tail : core.

Definition var : Type := nat.

Inductive btree : Type :=
| btVar : var -> btree
| btInt : nat -> btree
| btNode : btree -> btree -> btree.

Scheme Equality for btree.

Lemma btree_eq_boolP : Equality.axiom btree_eq_dec.
Proof. move=> x y. case: btree_eq_dec => //= H; by constructor. Qed.
HB.instance Definition _ := hasDecEq.Build _ btree_eq_boolP.

Definition subst_var (x : var) (t : btree) (v : var) : btree :=
  if v == x then t else btVar v.

(* t[x\u] *)
Fixpoint subst (s : var -> btree) t : btree :=
match t with
| btVar v => s v
| btInt _ => t
| btNode t1 t2 => btNode (subst s t1) (subst s t2)
end.

Definition subst_comp (s1 s2 : var -> btree) (v : var) : btree :=
  subst s1 (s2 v).

Definition subst_rul := (var * btree)%type.
Definition constr := (btree * btree)%type.
Definition constr_list := list constr.

Definition subst_pair s (p : constr) := (subst s p.1, subst s p.2).

Fixpoint union (vl1 vl2 : list var) :=
  if vl1 is v :: vl then
    if v \in vl2 then union vl vl2 else union vl (v :: vl2)
  else vl2.

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

Fixpoint vars (t : btree) : list var :=
  match t with
  | btVar x => [:: x]
  | btInt _ => nil
  | btNode t1 t2 => union (vars t1) (vars t2)
  end.

Lemma subst_same v t' t : v \notin (vars t) -> subst (subst_var v t') t = t.
Proof.
  elim: t => //= [x | t1 IH1 t2 IH2].
  - by rewrite /subst_var inE eq_sym => /negbTE ->.
  - by rewrite /subst_var in_union_or negb_or => /andP[] /IH1 -> /IH2 ->.
Qed.

(*
Definition unifies s (t1 t2 : btree) := subst_list s t1 = subst_list s t2.
Definition unifies_pairs s (l : constr_list) :=
  forall t1 t2, (t1,t2) \in l -> unifies s t1 t2.
*)

Fixpoint size_tree (t : btree) : nat :=
  if t is btNode t1 t2 then 1 + size_tree t1 + size_tree t2 else 1.

Definition size_pairs (l : constr_list) :=
  sumn [seq size_tree p.1 + size_tree p.2 | p <- l].

Fixpoint vars_pairs (l : constr_list) : list var :=
  match l with
  | nil => nil
  | (t1, t2) :: r => union (union (vars t1) (vars t2)) (vars_pairs r)
  end.

End Definitions.

Definition substMonoid : UU0 := var -> btree.
Definition substComp : substMonoid -> substMonoid -> substMonoid := subst_comp.
Definition substNone : substMonoid := btVar.

Lemma sconsA : associative substComp.
Proof.
  move => x y z.
  rewrite /substComp /subst_comp.
  apply: boolp.funext => v /=.
  by elim: (z v) => //= t1 -> t2 ->.
Qed.

Lemma scons0s : left_id substNone substComp.
Proof.
  move => x.
  apply boolp.funext => v.
  rewrite /substComp /subst_comp.
  by elim: (x v) => //= t1 -> t2 ->.
Qed.

Lemma sconss0 : right_id substNone substComp.
Proof.
  move => x.
  exact: boolp.funext.
Qed.

Definition op :=
  Monoid.isLaw.Build substMonoid substNone substComp sconsA scons0s sconss0.

Definition unifiesP (sm : substMonoid) t1 t2 := subst sm t1 = subst sm t2.
Definition unifiesP_pairs (sm : substMonoid) (l : constr_list) :=
  forall t1 t2, (t1,t2) \in l -> unifiesP sm t1 t2.

Definition unifies (sm : substMonoid) t1 t2 := subst sm t1 == subst sm t2.
Fixpoint unifies_pairs (sm : substMonoid) (l : constr_list) :=
match l with nil => true | (t1, t2) :: l => unifies sm t1 t2 && unifies_pairs sm l end.

Lemma unifP sm t1 t2 : unifiesP sm t1 t2 <-> unifies sm t1 t2.
Proof.
split => h.
- by rewrite /unifies; rewrite h.
- exact: eqP.
Qed.

Lemma in_aux (a : constr) l : a \in a :: l.
Proof.
rewrite in_cons.
apply (Bool.reflect_iff _ _ orP).
by left.
Qed.

Lemma unifP_split sm t1 t2 l :
  unifiesP_pairs sm ((t1, t2) :: l) ->
  unifiesP sm t1 t2 /\ unifiesP_pairs sm l.
Proof.
intro; split.
- exact/H/in_aux.
- rewrite /unifiesP_pairs => tt1 tt2.
  intros; apply H.
  rewrite in_cons.
  apply (Bool.reflect_iff _ _ orP); by right.
Qed.

Lemma unifP_merge sm t1 t2 l :
  unifiesP sm t1 t2 /\ unifiesP_pairs sm l ->
  unifiesP_pairs sm ((t1, t2) :: l).
Proof.
intro h_; case h_ => hl hr.
rewrite /unifiesP_pairs; intros tt1 tt2 H.
rewrite in_cons in H.
apply (Bool.reflect_iff _ _ orP) in H; case H => h.
- apply (Bool.reflect_iff _ _ eqP) in h.
  apply pair_equal_spec in h; case h => eq1 eq2.
  by rewrite eq1 eq2.
- exact/hr/h.
Qed.

Lemma unifP_pairs sm l : unifiesP_pairs sm l <-> unifies_pairs sm l.
Proof.
split => h; induction l => //=; case_eq a => t1 t2 eq; rewrite eq in h.
- apply (Bool.reflect_iff _ (unifies sm t1 t2 && unifies_pairs sm l) andP).
  assert (unifiesP sm t1 t2 /\ unifiesP_pairs sm l) by (exact/unifP_split/h).
  destruct H; split.
  + exact/unifP/H.
  + exact/IHl/H0.
- apply unifP_merge; simpl in h.
  apply (Bool.reflect_iff _ _ andP) in h; case h => hl hr; split.
  + exact/unifP/hl.
  + exact/IHl/hr.
Qed.

(*
Section Unify1.

Variable N : writerMonad subst_rul.
Variable M : writerRunMonad subst_rul substMonoid substAcc N.
Variable unify2 : constr_list -> M unit.

Definition unify_subst x t r : M unit :=
  if x \in vars t then fail
  else write (x, t) >> unify2 (map (subst_pair x t) r).

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
Variable N : writerMonad subst_rul.
Variable M : writerRunMonad subst_rul substMonoid substAcc N.
Fixpoint unify2 (h : nat) l : M unit :=
  if h is h.+1 then unify1 N M (unify2 h) (size_pairs l + 1) l else fail.
End Unify2.

Section Unify.
Variable N : writerMonad subst_rul.
Variable M : writerRunMonad subst_rul substMonoid substAcc N.

Definition unify t1 t2 : N (unit * substMonoid)%type :=
  let l := [:: (t1,t2)] in
  runWriteT
  (unify2 N M (size (vars_pairs l) + 1) l)
  substNone.

Lemma subst_btNode v t t1 t2 :
  subst v t (btNode t1 t2) = btNode (subst v t t1) (subst v t t2).
Proof. by elim: v t t1 t2 => /=. Qed.

Lemma subst_list_btNode s t1 t2 :
  subst_list s (btNode t1 t2) = btNode (subst_list s t1) (subst_list s t2).
Proof. by elim: s t1 t2 => /=. Qed.

Lemma unifies_same sm t : unifies sm t t.
Proof. by rewrite /unifies. Qed.

Lemma unifies_pairs_same sm t l :
  unifies_pairs sm l -> unifies_pairs sm ((t,t) :: l).
Proof.
  move=> H /=.
  apply (Bool.reflect_iff _ (unifies sm t t && unifies_pairs sm l) andP).
  split => //=; (apply unifies_same || apply (Bool.reflect _ _ eqP)).
Qed.

Lemma unifies_swap sm t1 t2 :
  unifies sm t1 t2 -> unifies sm t2 t1.
Proof.
  rewrite /unifies; intro H.
  apply (Bool.reflect_iff _ _ eqP) in H.
  by rewrite H.
Qed.

Lemma unifies_pairs_swap sm t1 t2 l :
  unifies_pairs sm ((t1, t2) :: l) -> unifies_pairs sm ((t2, t1) :: l).
Proof.
  move=> /= H.
  apply (Bool.reflect_iff _ _ andP) in H; case H => hl hr.
  apply (Bool.reflect_iff _ (unifies sm t2 t1 && unifies_pairs sm l) andP).
  split => //=; exact/unifies_swap/hl.
Qed.

(*
Lemma unifies_subst sm v t t1 t2 :
  (v \notin vars t) -> t <> btVar v ->
  unifies sm (btVar v) t ->
  unifies sm t1 t2 ->
  unifies sm (subst v t t1) (subst v t t2).
Proof.
  rewrite /unifies.
  induction t1; induction t2; move=> /= nin neq /eqP Hv /eqP H.
  - case_eq (v0 == v); case_eq (v1 == v) => /eqP eq1 /eqP eq2 //.
    + by rewrite -H eq2 Hv.
    + by rewrite H eq1 Hv.
    + by rewrite H.
  - case_eq (v0 == v) => /eqP eq.
    + by rewrite -Hv -eq H.
    + by rewrite H.
  - case_eq (v0 == v) => /eqP eq.
    + rewrite -Hv -eq H -subst_btNode eq.
       -IHt2_1 -IHt2_2.

Lemma unifies_pairs_subst sm v t l :
  unifies_pairs sm ((btVar v, t) :: l) -> unifies_pairs sm (map (subst_pair v t) l).
Proof.
  move=> /= H.
  induction l => //; destruct a => /=.
*)

(* Soundness *)

(*
Lemma unify_one_rule h v t sm l :
  runWriteT (unify2 N M h l) (substAcc (v, t) sm) >>=
    (fun x => assert (fun _ => unifies_pairs x.2 ((btVar v, t) :: l)) tt) =
  runWriteT (unify2 N M h l) sm >>=
    (fun x => assert (fun _ => unifies_pairs x.2 l) tt).
Admitted.
*)

Lemma unify_subst_sound h v t sm l :
  (forall l,
    runWriteT (unify2 N M h l) sm >>=
    (fun x => assert (fun _ => unifies_pairs x.2 l) tt) =
    runWriteT (unify2 N M h l) sm >> Ret tt
  ) ->
  runWriteT (unify_subst N M (unify2 N M h) v t l) sm >>= 
    (fun x => assert (fun _ => unifies_pairs x.2 ((btVar v, t) :: l)) tt) =
  runWriteT (unify_subst N M (unify2 N M h) v t l) sm >> Ret tt

with unify2_sound h sm l :
  runWriteT (unify2 N M h l) sm >>= (fun x => assert (fun _ => unifies_pairs x.2 l) tt) =
  runWriteT (unify2 N M h l) sm >> Ret tt.
Proof.
-------
  rewrite /unify_subst.
  case Hocc: (v \in _) => // IH; try by rewrite ?runWriteTfail ?bindfailf.
  rewrite ?runWriteTbind ?runWriteTwrite ?bindretf.
  
  admit.
  (*
  assert (forall x,
          unifies_pairs x ((btVar v, t) :: l) =
          unifies_pairs x (map (subst_pair v t) l)).
  rewrite /unifies_pairs /=.

  induction l => sm' //=.
  - rewrite Bool.andb_true_r.
  Check [seq subst_pair v t i | i <- l].
  apply unify2_sound.
  *)
-------
  elim: h l => /= [l | h IH l].
  - by rewrite ?runWriteTfail ?bindfailf.
  move: (size_pairs l + 1) => h'.
  elim: h' l => //= [l | h' IH' [| [t1 t2] l] /=].
  - by rewrite ?runWriteTfail ?bindfailf.
  - by rewrite ?runWriteTret assertE guardT bindskipf.
  destruct t1, t2; try by rewrite ?runWriteTfail ?bindfailf.
  - case: ifP; move=> /eqP eq.
    + rewrite eq -IH'.
      assert (forall x,
               (fun x : unit * substMonoid =>
               assert (fun=> unifies x.2 (btVar v0) (btVar v0) && unifies_pairs x.2 l) tt) x = 
               (fun x : unit * substMonoid => @assert N unit (fun=> unifies_pairs x.2 l) tt) x)
      by (intro x; rewrite unifies_same //=); apply boolp.funext in H.
      by rewrite H.
    + exact/unify_subst_sound.
  - exact/unify_subst_sound.
  - exact/unify_subst_sound.
  - assert (forall x,
             (fun x : unit * substMonoid => 
              @assert N unit (fun=> unifies_pairs x.2 ((btVar v, btInt n) :: l)) tt) x = 
             (fun x : unit * substMonoid => 
              @assert N unit (fun=> unifies_pairs x.2 ((btInt n, btVar v) :: l)) tt) x)
    by (intro x => //=; case_eq (unifies x.2 (btVar v) (btInt n)) => eq /=;
        rewrite /unifies eq_sym in eq; by rewrite /unifies eq); apply boolp.funext in H.
    simpl in H; rewrite <- H; exact/unify_subst_sound.
  - case_eq (n == n0) => eq; rewrite /unifies; try by rewrite ?runWriteTfail ?bindfailf.
    apply (Bool.reflect_iff _ _ eqP) in eq.
    assert (forall x,
             (fun x : unit * substMonoid => 
              assert (fun=> (x.2 (btInt n) == x.2 (btInt n0)) && unifies_pairs x.2 l) tt) x = 
             (fun x : unit * substMonoid => 
              @assert N unit (fun=> unifies_pairs x.2 l) tt) x)
    by (intro x; rewrite eq eq_refl //=); apply boolp.funext in H.
    by rewrite H IH'.
  - assert (forall x,
             (fun x : unit * substMonoid => 
              @assert N unit (fun=> unifies_pairs x.2 ((btVar v, (btNode t1_1 t1_2)) :: l)) tt) x = 
             (fun x : unit * substMonoid => 
              @assert N unit (fun=> unifies_pairs x.2 (((btNode t1_1 t1_2), btVar v) :: l)) tt) x)
    by (intro x => //=; case_eq (unifies x.2 (btVar v) (btNode t1_1 t1_2)) => eq /=;
        rewrite /unifies eq_sym in eq; by rewrite /unifies eq); apply boolp.funext in H.
    simpl in H; rewrite <- H; exact/unify_subst_sound.
  - rewrite /unifies.
    assert (forall sm t1 t2, sm (btNode t1 t2) = btNode (sm t1) (sm t2)) by admit.
    assert (forall x,
             (fun x : unit * substMonoid => 
              @assert N unit (fun => (x.2 (btNode t1_1 t1_2) == x.2 (btNode t2_1 t2_2)) && unifies_pairs x.2 l) tt) x = 
             (fun x : unit * substMonoid => 
              @assert N unit (fun => ((btNode (x.2 t1_1) (x.2 t1_2)) == (btNode (x.2 t2_1) (x.2 t2_2))) && unifies_pairs x.2 l) tt) x)
    by (intro x; rewrite 2!H //); apply boolp.funext in H0.
    rewrite H0 /=.
    admit.
Admitted. 

(*
    assert (forall x,
             (N # fun x : unit * substMonoid =>
             assert (fun=> unifies x.2 (btVar v0) (btVar v0) && unifies_pairs x.2 l) tt) x = 
             (N # fun x : unit * substMonoid => @assert N unit (fun=> unifies_pairs x.2 l) tt) x).
    intro x. congruence. rewrite unifies_same //=.

    rewrite ?bindE.
    rewrite H.

    congruence.


    rewrite unifies_same.

  Check unifies_pairs_same.


  by move=> /eqP <- /IH' /unifies_pairs_same.

  change (guard (xpredT tt) >> Ret tt).


- rewrite ?runWriteTret.
  simpl in IHh. rewrite ?runWriteTret in IHh.
Check xpredT.
*)

(*
  induction h => /=; try by rewrite ?runWriteTfail ?bindfailf.
  move: (size_pairs [seq subst_pair v t i | i <- l] + 1) => h'.
  induction h' => /=; try by rewrite ?runWriteTfail ?bindfailf.
  induction l => //=.
  rewrite ?runWriteTret ?bindretf /= /unifies /substAcc/substNone /= eq_refl.
  assert (subst v t t = t) by (apply subst_same; rewrite /negb Hocc //=).
  by rewrite H eq_refl /= assertE guardT bindskipf.
  destruct a => /=.
  destruct (subst v t b), (subst v t b0) => /=; try by rewrite ?runWriteTfail ?bindfailf.
Admitted.
*)

Theorem soundness t1 t2:
  unify t1 t2 >>= (fun x => assert (fun _ => unifies x.2 t1 t2) tt) =
  unify t1 t2 >> Ret tt.
Proof.
  assert (forall x,
          (fun x : unit * substMonoid => assert (fun=> unifies x.2 t1 t2) tt) x =
          (fun x : unit * substMonoid =>
           @assert N unit (fun=> unifies_pairs x.2 [:: (t1, t2)]) tt) x)
  by (assert (forall x, unifies x t1 t2 = unifies_pairs x [:: (t1, t2)])
      by (intro x; rewrite /= Bool.andb_true_r //);
      intro x; rewrite H //); apply boolp.funext in H.
  by rewrite H; apply unify2_sound.
Qed.

(* Completeness *)

End Unify.


*)



