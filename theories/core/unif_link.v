From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require boolp.
From mathcomp Require Import finmap.

Require Import preamble hierarchy monad_lib fail_lib state_lib.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section Definitions.

Section uterm.
Variable uvar : UU0.
Inductive uterm : UU0 :=
| Link : uvar -> uterm
| Int : nat -> uterm
| Node : uterm -> uterm -> uterm.
End uterm.

Section uvar.
(*
Definition uvar : UU0 :=

Definition var : Type := nat.

Check loc.

Inductive test : Type :=
| Test t : loc test t -> test
| Base : test.

Inductive uvar : Type :=
| Var v : loc nat v -> uvar
| Term t : loc uterm t -> uvar
with uterm : Type :=
| Link : uvar -> uterm
| Int : int -> uterm
| Node : uvar -> uvar -> uterm.


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

Variables (N : exceptMonad) (M : exceptStateRunMonad substType N).

Section Unify1.

Variable unify2 : constr_list -> M unit.

Variable unify_subst : var -> btree -> constr_list -> M unit.

(*
(*
Definition unify_subst x t r : M unit :=
  if x \in vars t then fail
  else (fun f => write f >> unify2 (map (subst_pair f) r)) [:: (x, t)].
*)

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
  runStateT (unify2 (size (vars_pairs l) + 1) l).

End Unify.

*)