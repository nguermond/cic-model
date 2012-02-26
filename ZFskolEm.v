
(* In this file, we show the equivalence between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic.
Require Export ZFdef.
Require Import EnsEm Sublogic.

Module Skolem (L:Sublogic). (*<: IZF_R_sig.*)

Module Z := Ensembles L.
Import L Z.Lthms.

Instance Zsetoid: Equivalence Z.eq_set.
Proof.
split; red; intros; rewrite Z.eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (Z.in_set z0 y); trivial.
Qed.

Instance Zin_morph : Proper (Z.eq_set ==> Z.eq_set ==> iff) Z.in_set.
Proof.
do 3 red; intros.
rewrite Z.eq_set_ax in H0.
split; intros.
 rewrite <- H0.
 apply Z.in_reg with x; trivial.

 rewrite H0.
 symmetry in H.
 apply Z.in_reg with y; trivial.
Qed. 

Definition set :=
  { f : Z.set -> Prop |
    Tr(exists u, f u) /\
    (forall a a', f a -> f a' -> Z.eq_set a a') }.

Lemma set_intro : forall (f:Z.set->Prop) (P:set->Prop),
  Tr(exists u, f u) ->
  (forall a a', f a -> f a' -> Z.eq_set a a') ->
  (forall Hex Huniq, P (exist _ f (conj Hex Huniq))) ->
  sig P.
intros.
exists (exist (fun _ => _ /\ _) f (conj H H0)); trivial. (* regression of unification *)
(*exists (exist _ f (conj H H0)); trivial.*)
Qed.

Inductive in_set_ (x y:set) : Prop :=
 InSet
  (_:Tr(exists2 x', proj1_sig x x' &
     Tr(exists2 y', proj1_sig y y' & Z.in_set x' y'))).

Definition in_set := in_set_.

Lemma inset_isL x y : isL (in_set x y).
red.
constructor.
Telim H; intro.
destruct H; trivial.
Qed.
Global Hint Resolve inset_isL.

Lemma in_set_elim : forall x y, in_set x y <->
  Tr(exists2 x', proj1_sig x x' &
  Tr(exists2 y', proj1_sig y y' & Z.in_set x' y')).
split; intros.
 destruct H; trivial.
 constructor; trivial.
Qed.

Notation "x \in y" := (in_set x y).

Definition eq_set a b := forall x, x \in a <-> x \in b.

Notation "x == y" := (eq_set x y).

Lemma eqset_isL x y : isL (x == y).
red; red; intros.
Telim H; auto.
Qed.
Global Hint Resolve eqset_isL.

Lemma eq_set_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b).
reflexivity.
Qed.

Instance eq_setoid: Equivalence eq_set.
Proof.
split; do 2 red; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 \in y); trivial.
Qed.

Lemma In_intro: forall x y: set,
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> Z.in_set x' y') ->
  x \in y.
intros.
destruct (proj2_sig x).
Tdestruct H0.
destruct (proj2_sig y).
Tdestruct H2.
constructor.
Texists x0; trivial.
Texists x1; auto.
Qed.


Definition Z2set (x:Z.set) : set.
exists (fun a => Z.eq_set a x).
split.
 Texists x; reflexivity.

 intros; transitivity x; trivial.
 symmetry; trivial.
Defined.

Lemma Z2set_surj : forall x, Tr(exists y, x == Z2set y).
intros.
destruct (proj2_sig x).
Tdestruct H.
Texists x0.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 Tdestruct H2.
 constructor.
 Texists x2; trivial.
 Texists x3; trivial.
 simpl; auto.

 rewrite in_set_elim in H1.
 Tdestruct H1.
 Tdestruct H2.
 constructor.
 Texists x2; trivial.
 simpl in H2.
 Texists x0; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma Eq_proj : forall (x:set) x', proj1_sig x x' -> x == Z2set x'.
intros.
destruct (proj2_sig x).
clear H0.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 Tdestruct H2.
 constructor.
 Texists x1; simpl; trivial.
 Texists x2; auto.

 rewrite in_set_elim in H0.
 Tdestruct H0; simpl in *.
 Tdestruct H2.
 constructor.
 Texists x1; simpl; trivial.
 Texists x'; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma inZ_in : forall a b, Z.in_set a b -> Z2set a \in Z2set b.
unfold Z2set, in_set; simpl.
intros.
constructor; simpl.
Texists a; try reflexivity.
Texists b; try reflexivity; trivial.
Qed.

Lemma in_inZ : forall a b, Z2set a \in Z2set b -> Z.in_set a b.
intros.
rewrite in_set_elim in H.
Tdestruct H.
Tdestruct H0.
unfold Z2set in *; simpl in *.
apply Z.in_reg with x; trivial.
rewrite <- H0; auto.
Qed.

Lemma eq_Zeq : forall x y, Z2set x == Z2set y -> Z.eq_set x y.
intros.
rewrite Z.eq_set_ax; split; intros.
 apply in_inZ.
 apply (proj1 (H (Z2set z))).
 apply inZ_in; trivial.

 apply in_inZ.
 apply (proj2 (H (Z2set z))).
 apply inZ_in; trivial.
Qed.

Lemma Zeq_eq : forall x y, Z.eq_set x y -> Z2set x == Z2set y.
intros.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 Tdestruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 Texists x2; trivial.
 simpl.
 transitivity x; trivial.

 rewrite in_set_elim in H0.
 Tdestruct H0.
 Tdestruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 Texists x2; trivial.
 simpl.
 transitivity y; trivial.
 symmetry; trivial.
Qed.

Instance Z2set_morph : Proper (Z.eq_set ==> eq_set) Z2set.
exact Zeq_eq.
Qed.

Lemma in_reg : forall a a' b, a == a' -> a \in b -> a' \in b.
intros.
rewrite in_set_elim in H0.
Tdestruct H0 as (a0,eq_a,h).
Tdestruct h as (b0,eq_b,in_ab).
destruct (proj2_sig a') as (h,_).
Tdestruct h as (a'0, eq_a').
constructor.
Texists a'0; trivial.
Texists b0; trivial.
apply Z.in_reg with a0; trivial.
apply eq_Zeq.
rewrite <- (Eq_proj _ _ eq_a).
rewrite <- (Eq_proj _ _ eq_a').
trivial.
Qed.

Instance in_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
Proof.
unfold eq_set in |- *; split; intros.
 apply in_reg with x; auto.
 elim (H0 x); auto.

 apply in_reg with y; auto.
  symmetry  in |- *; auto.
  elim (H0 y); auto.
Qed.

(* empty set *)

Lemma empty_sig : { empty | forall x, x \in empty -> Tr False }.
apply set_intro with (fun x:Z.set => forall y, Z.in_set y x -> Tr False); intros.
 apply Z.empty_ex.

 rewrite Z.eq_set_ax; split; intros.
  Tabsurd; apply H with z; trivial.
  Tabsurd; apply H0 with z; trivial.

 red; intros.
 rewrite in_set_elim in H.
 Tdestruct H; simpl in *.
 Tdestruct H0.
 apply H0 with x0; trivial.
Qed.

Definition empty := proj1_sig empty_sig.
Lemma empty_ax: forall x, x \in empty -> Tr False.
Proof proj2_sig empty_sig.

(* pair *)

Lemma pair_sig : forall a b,
  { pair | forall x, x \in pair <-> Tr(x == a \/ x == b) }.
intros a b.
apply set_intro with
  (fun x => forall y, y \in Z2set x <-> Tr(y == a \/ y == b)); intros.
 Tdestruct (Z2set_surj a).
 Tdestruct (Z2set_surj b).
 Tdestruct (Z.pair_ex x x0).
 Texists x1; intros.
 Tdestruct (Z2set_surj y).
 rewrite H2.
 transitivity (Z.in_set x2 x1).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 
  apply iff_trans with (1:=H1 x2).
  rewrite H.
  rewrite H0.
  setoid_replace (Z.eq_set x2 x) with (Z2set x2 == Z2set x).
  setoid_replace (Z.eq_set x2 x0) with (Z2set x2 == Z2set x0).
  reflexivity.
  split; intros; first [apply Zeq_eq|apply eq_Zeq]; trivial. 
  split; intros; first [apply Zeq_eq|apply eq_Zeq]; trivial. 

 intros; rewrite Z.eq_set_ax; intros.
 transitivity (Z2set z \in Z2set a0).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 

  transitivity (Tr(Z2set z == a \/ Z2set z == b)); auto.
  symmetry.
  transitivity (Z2set z \in Z2set a'); trivial.
  split; intros; first [apply inZ_in|apply in_inZ]; trivial.

 split; intros.
  rewrite in_set_elim in H.
  Tdestruct H; simpl in *.
  Tdestruct H0.
  apply (proj1 (H0 x)).
  constructor.
  Texists x0; trivial; simpl.
  Texists x1; trivial; reflexivity.

  apply In_intro; simpl; intros.
  apply in_inZ.
  rewrite <- (Eq_proj _ _ H0). 
  apply (proj2 (H1 x)); trivial.
Qed.

Definition pair a b := proj1_sig (pair_sig a b).
Lemma pair_ax: forall a b x, x \in pair a b <-> Tr(x == a \/ x == b).
Proof fun a b => proj2_sig (pair_sig a b).

(* union *)

Lemma union_sig: forall a,
  { union | forall x, x \in union <-> Tr(exists2 y, x \in y & y \in a) }.
intro a.
apply set_intro with
 (fun x => forall z,
  Z.in_set z x <-> Tr(exists2 y, Z.in_set z y & Z2set y \in a)); intros.
 Tdestruct (Z2set_surj a).
 Tdestruct (Z.union_ex x).
 Texists x0.
 intros.
 apply iff_trans with (1:=H0 z).
 split; intros.
  Tdestruct H1.
  Texists x1; trivial.
  rewrite H; apply inZ_in; trivial.

  Tdestruct H1.
  Texists x1; trivial.
  apply in_inZ; rewrite <- H; trivial.

 rewrite Z.eq_set_ax; intros.
 apply iff_trans with (1:=H z).
 symmetry; trivial.

split; intros.
 rewrite in_set_elim in H.
 Tdestruct H; simpl in *.
 Tdestruct H0.
 rewrite H0 in H1.
 Tdestruct H1.
 Texists (Z2set x2); trivial.
 rewrite (Eq_proj  _ _ H).
 apply inZ_in; trivial.

 Tdestruct H.
 apply In_intro; simpl; intros.
 apply (proj2 (H2 x')).
 Tdestruct (Z2set_surj x0).
 Texists x1.
  apply in_inZ.
  rewrite <- H3; rewrite <- (Eq_proj _ _ H1); trivial.

  rewrite <- H3; trivial.
Qed.

Definition union a := proj1_sig (union_sig a).
Lemma union_ax: forall a x,
  x \in union a <-> Tr(exists2 y, x \in y & y \in a).
Proof fun a => proj2_sig (union_sig a).

(* subset *)

Lemma subset_sig: forall a P,
  { subset | forall x, x \in subset <->
             (x \in a /\ Tr(exists2 x', x==x' & P x')) }.
intros a P.
apply set_intro with
  (fun x => forall y, y \in Z2set x <->
    (y \in a /\ Tr(exists2 y', y==y' & P y'))); intros.
 Tdestruct (Z2set_surj a).
 Tdestruct (Z.subset_ex x (fun z => Tr(exists2 z', z' == Z2set z & P z'))).
 Texists x0; intros.
 Tdestruct (Z2set_surj y).
 rewrite H1.
 transitivity (Z.in_set x1 x0).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 
  apply iff_trans with (1:=H0 x1).
  rewrite H.
  apply and_iff_morphism.
   split; intros; first [apply inZ_in|apply in_inZ]; trivial. 

   split; intros h; Tdestruct h.
    Tdestruct H3.
    Texists x3; trivial.
    rewrite H1; rewrite H3; apply Zeq_eq; trivial.

    Texists x1;[reflexivity|].
    Texists x2; trivial.
    rewrite <- H1; symmetry; trivial.

 apply eq_Zeq.
 rewrite eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.

 split; intros.
  rewrite in_set_elim in H.
  Tdestruct H; simpl in *.
  Tdestruct H0.
  apply (proj1 (H0 x)).
  constructor.
  Texists x0; trivial; simpl.
  Texists x1; trivial; reflexivity.

  apply In_intro; simpl; intros.
  apply in_inZ.
  rewrite <- (Eq_proj _ _ H0). 
  apply (proj2 (H1 x)); trivial.
Qed.

Definition subset a P := proj1_sig (subset_sig a P).
Lemma subset_ax : forall a P x,
    x \in subset a P <-> (x \in a /\ Tr(exists2 x', x==x' & P x')).
Proof fun a P => proj2_sig (subset_sig a P).

(* power set *)

Lemma power_sig: forall a,
  { power | forall x, x \in power <-> (forall y, y \in x -> y \in a) }.
intro a.
apply set_intro with
 (fun x => forall z,
  Z.in_set z x <-> (forall y, Z.in_set y z -> Z2set y \in a)); intros.
 Tdestruct (Z2set_surj a).
 Tdestruct (Z.power_ex x).
 Texists x0; intros.
 apply iff_trans with (1:= H0 z).
 split; intros.
  rewrite H; apply inZ_in; auto.
  apply in_inZ; rewrite <- H; auto.

 rewrite Z.eq_set_ax; intros.
 apply iff_trans with (1:=H z).
 symmetry; trivial.

split; intros.
 rewrite in_set_elim in H.
 Tdestruct H; simpl in *.
 Tdestruct H1.
 rewrite H1 in H2.
 Tdestruct (Z2set_surj y); intros.
 rewrite H3.
 apply H2.
 apply in_inZ; rewrite <- H3; rewrite <- (Eq_proj _ _ H); trivial.

 apply In_intro; simpl; intros.
 rewrite H1; intros.
 apply H.
 rewrite (Eq_proj _ _ H0); apply inZ_in; trivial.
Qed.

Definition power a := proj1_sig (power_sig a).
Lemma power_ax:
  forall a x, x \in power a <-> (forall y, y \in x -> y \in a).
Proof fun a => proj2_sig (power_sig a).

(* uchoice *)

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  Tr(exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Definition uchoice (P : set -> Prop) (Hp : uchoice_pred P) : set.
exists (fun z => P (Z2set z)).
destruct Hp.
destruct H0.
split; intros.
 Tdestruct H0.
 Tdestruct (Z2set_surj x).
 Texists x0; apply H with x; trivial.

 apply eq_Zeq.
 auto.
Defined.

Lemma uchoice_ax : forall P h x,
  (x \in uchoice P h <-> Tr(exists2 z, P z & x \in z)).
split; intros.
 destruct H.
 Tdestruct H.
 Tdestruct H0.
 simpl in H0.
 Texists (Z2set x1); trivial.
 apply In_intro; intros.
 simpl in H3.
 rewrite H3.
 destruct (proj2_sig x).
 rewrite (H5 x' x0); trivial.

 Tdestruct H.
 destruct H0.
 Tdestruct H0.
 Tdestruct H1.
 constructor.
 Texists x1; trivial.
 simpl.
 Texists x2; trivial.
 apply (proj1 h x0); trivial.
 apply Eq_proj; trivial.
Qed.

Lemma uchoice_morph_raw : forall (P1 P2:set->Prop) h1 h2,
  (forall x x', x == x' -> (P1 x <-> P2 x')) ->
  uchoice P1 h1 == uchoice P2 h2.
intros.
apply eq_set_ax; intros.
rewrite uchoice_ax.
rewrite uchoice_ax.
apply Tr_morph; apply ex2_morph; red; intros.
 apply H; reflexivity.

 reflexivity.
Qed.

Instance uchoice_pred_morph : Proper ((eq_set ==> iff) ==> iff) uchoice_pred.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (?,(?,?)); split;[|split]; intros.
 assert (x x0).
  revert H4; apply H; auto with *.
 revert H5; apply H; trivial.

 Tdestruct H1; Texists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall (P:set->Prop) h x, Tr(P x) -> x == uchoice P h.
intros.
apply eq_set_ax;intros.
rewrite uchoice_ax.
Telim H; intro.
split; intros.
 Texists x; trivial.

 Tdestruct H0.
 destruct h.
 destruct H3.
 rewrite (H4 x x1); auto.
Qed.

Lemma uchoice_def : forall P h, Tr(P (uchoice P h)).
intros.
destruct h.
destruct a.
Tdestruct t.
Tin; apply p with x; trivial.
apply uchoice_ext; trivial.
Tin; trivial.
Qed.

(* replacement *)

Definition funDom (R:set -> set -> Prop) x :=
  forall x' y y', R x y -> R x' y' -> x == x' -> y == y'.
Definition downR (R:set -> set -> Prop) x' y' :=
  Tr(exists2 x, x == Z2set x' /\ funDom R x & Tr(exists2 y, y == Z2set y' & R x y)).

Lemma downR_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> Z.eq_set ==> Z.eq_set ==> iff) downR.
do 4 red; intros.
unfold downR.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply Tr_morph; apply ex2_morph; red; intros.
 apply and_iff_morphism.
  rewrite H0; reflexivity.

  unfold funDom.
  split; intros.
   rewrite <- (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite <- (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

   rewrite (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

 apply Tr_morph; apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

Lemma downR_fun : forall R x x' y y',
  downR R x y ->
  downR R x' y' ->
  Z.eq_set x x' ->
  Z.eq_set y y'.
intros.
Tdestruct H as (xx,(eqx,fdomx),h).
Tdestruct h as (yy,eqy,rel).
Tdestruct H0 as (xx',(eqx',_),h).
Tdestruct h as (yy',eqy',rel').
apply eq_Zeq.
rewrite <- eqy; rewrite <- eqy'.
red in fdomx.
apply fdomx with xx'; trivial.
rewrite eqx; rewrite eqx'.
apply Zeq_eq; trivial.
Qed.

Lemma repl0 : forall (a:set) (R:set->set->Prop), set.
intros a R.
exists
 (fun a' => forall x,
  Z.in_set x a' <-> Tr(exists2 y, Z2set y \in a & Tr(exists2 x', Z.eq_set x x' & downR R y x'))).
split; intros.
 Tdestruct (Z2set_surj a).
 destruct (Z.repl_ex x (downR R)); intros.
  apply downR_fun with (1:=H1)(2:=H2); trivial.

  Texists x0; intros.
  rewrite H0.
  apply Tr_morph; apply ex2_morph; red; intros.
  2:reflexivity.
  split; intros.
   rewrite H.
   apply inZ_in; trivial.

   apply in_inZ.
   rewrite <- H; trivial.

 rewrite Z.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Definition incl_set x y := forall z, z \in x -> z \in y.

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
rewrite in_set_elim in *.
Tdestruct H1.
Texists x1; trivial.
clear z H1.
Tdestruct H2.
simpl in *; intros.
Tdestruct (Z2set_surj y).
destruct (Z.repl_ex x3 (downR y0)).
 intros.
 apply downR_fun with (1:=H5) (2:=H6); trivial.

Texists x4; trivial.
 intro; rewrite H4.
 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H3.
 split; intros.
  apply inZ_in; trivial.
  apply in_inZ; trivial.

 rewrite H4.
 rewrite H1 in H2.
 clear x2 H1 x4 H4.
 Tdestruct H2.
 Tdestruct H2.
 Texists x2.
  apply in_inZ.
  rewrite <- H3; apply H; trivial.

  Texists x4; trivial.
  rewrite <- (fun e1 => downR_morph _ _ H0 x2 x2 e1 x4 x4); auto with *.
Qed. 

Lemma repl_sig :
  { repl |
    Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl /\
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> Tr(exists2 y, y \in a & Tr(exists2 x', x == x' & R y x')) }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 Tdestruct H1; simpl in *.
 rewrite H1 in H2.
 Tdestruct H2.
 Tdestruct H3.
 Tdestruct H4.
 destruct H4.
 Texists x4.
  rewrite H4; trivial.
 Tdestruct H5.
 Texists x5; trivial.
 apply Eq_proj in H0.
 rewrite H0; rewrite H5.
 apply Zeq_eq; trivial.

 Tdestruct H0.
 Tdestruct H1.
 apply In_intro; simpl; intros.
 rewrite H4; clear H4.
 Tdestruct (Z2set_surj x0).
 Texists x2.
  rewrite <- H4; trivial.
 Texists x'.
  reflexivity.
 Texists x0.
  split; intros; eauto.
  red; eauto.
 Texists x1; auto.
 rewrite <- H1.
 apply Eq_proj; trivial.
Defined.

Definition repl := proj1_sig repl_sig.
Lemma repl_mono : 
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof (proj1 (proj2_sig repl_sig)).
Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> Tr(exists2 y, y \in a & Tr(exists2 x', x == x' & R y x')).
Proof proj2 (proj2_sig repl_sig).

(* infinite set (natural numbers) *)

Definition Nat x :=
  forall (P:set),
  empty \in P ->
  (forall x, x \in P -> union (pair x (pair x x)) \in P) ->
  x \in P.

Instance Nat_morph : Proper (eq_set ==> iff) Nat.
unfold Nat; split; intros.
 rewrite <- H; apply H0; trivial.
 rewrite H; apply H0; trivial.
Qed.

Lemma Nat_S : forall x,
  Nat x -> Nat (union (pair x (pair x x))).
unfold Nat; intros; auto.
Qed.

Definition infinite_sig :
  { infty | empty \in infty /\
      forall x, x \in infty -> union (pair x (pair x x)) \in infty }.
apply set_intro with
  (fun x => forall y, Z.in_set y x <-> Nat (Z2set y)); intros.
 Tdestruct Z.infinity_ex; intros.
 elim Z.repl_ex with x (fun x' y' => Z.eq_set x' y' /\ Nat (Z2set y')); intros.
  Texists x0; intros.
  rewrite H1.
  split; intros.
   red; Tdestruct H2.
   Tdestruct H3.
   destruct H4.
   rewrite <- H3 in H5; trivial.

   Texists y.
    red in H2.
    apply in_inZ.
    apply H2; intros.
     Tdestruct H.
     apply inZ_in in H3.
     apply in_reg with (Z2set x1); trivial.
     split; intros.
      Tdestruct (Z2set_surj x2).
      rewrite H5 in H4; apply in_inZ in H4.
      Tabsurd; apply H with x3; trivial.

      Tabsurd; apply empty_ax with x2; trivial.

     Tdestruct (Z2set_surj x1).
     rewrite H4 in H3; apply in_inZ in H3.
     apply H0 in H3.
     Tdestruct H3.
     apply in_reg with (Z2set x3).
     2:apply inZ_in; trivial.
     split; simpl; intros.
      rewrite union_ax.
      Tdestruct (Z2set_surj x4).
      rewrite H7 in H6; apply in_inZ in H6; rewrite H3 in H6.
      Tdestruct H6.
       Texists (pair x1 x1).
        rewrite pair_ax; Tleft.
        rewrite H7; rewrite H4; apply Zeq_eq; trivial.

        rewrite pair_ax; Tright; reflexivity.

       Texists x1.
        rewrite H7; rewrite H4; apply inZ_in; trivial.

        rewrite pair_ax; Tleft; reflexivity.

      Tdestruct (Z2set_surj x4).
      rewrite H7; apply inZ_in.
      rewrite H3.
      rewrite H7 in H6; clear x4 H7.
      rewrite union_ax in H6.
      Tdestruct H6.
      rewrite pair_ax in H7; Tdestruct H7.
       Tright; apply in_inZ.
       rewrite <- H4; rewrite <- H7; trivial.

       rewrite H7 in H6; clear x4 H7.
       Tleft; apply eq_Zeq.
       rewrite <- H4.
       rewrite pair_ax in H6; Tdestruct H6; trivial.

    Texists y; trivial.
    reflexivity.

   split; trivial; reflexivity.

  destruct H2.
  destruct H3.
  transitivity x0; trivial.
   symmetry; trivial.
  transitivity x'; trivial.

 rewrite Z.eq_set_ax; split; intros.
  rewrite H0; rewrite H in H1; trivial.

  rewrite H; rewrite H0 in H1; trivial.

split; intros.
 apply In_intro; simpl; unfold Nat; intros.
 rewrite H0; intros.
 apply in_reg with empty; trivial.
 split; intros.
  Tabsurd; apply empty_ax with x; trivial.

  Tdestruct (Z2set_surj x).
  apply Eq_proj in H.
  rewrite <- H in H3.
  Tabsurd; apply empty_ax with (1:=H3).

 rewrite in_set_elim in H.
 Tdestruct H; simpl in *.
 Tdestruct H0.
 apply In_intro; simpl; intros.
 rewrite H3.
 setoid_replace (Z2set x') with (union (pair x (pair x x))).
  apply Nat_S.
  rewrite (Eq_proj _ _ H).
  rewrite <- H0; trivial.

  split; intros.
   Tdestruct (Z2set_surj x2).
   rewrite H5 in H4 |- *; clear H5 x2.
   apply Eq_proj in H2.
   rewrite <- H2 in H4; trivial. 

   Tdestruct (Z2set_surj x2).
   rewrite H5 in H4 |- *; clear H5 x2.
   apply Eq_proj in H2.
   rewrite <- H2; trivial.
Qed.
Definition infinite := proj1_sig infinite_sig.
Lemma infinity_ax1: empty \in infinite.
Proof proj1 (proj2_sig infinite_sig).

Lemma infinity_ax2: forall x,
  x \in infinite -> union (pair x (pair x x)) \in infinite.
Proof proj2 (proj2_sig infinite_sig).

(* well-founded induction *)

Lemma wf_axL (P:set->Prop):
  (forall x, isL (P x)) ->
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall xs (x:set), x == Z2set xs -> P x).
 intros.
 Tdestruct (Z2set_surj x).
 eauto.
clear x.
intros xs; elim xs using Z.wf_ax; intros; auto.
apply H0; intros.
Tdestruct (Z2set_surj y).
rewrite H2,H4 in H3.
apply in_inZ in H3; eauto.
Qed.

Module ClassicCollection.

(** Proving that collection can be skolemized in classical ZF:
    we need excluded-middle to prove coll_ax_uniq (see EnsEm)
 *)

Section Classic.

Hypothesis EM : forall P, Tr(P \/ (P -> Tr False)).

Lemma coll_sig : forall A (R:set->set->Prop), 
  {coll| Proper (eq_set==>eq_set==>iff) R ->
     forall x, x \in A ->
     Tr(exists y, R x y) ->
     Tr(exists2 y, y \in coll & R x y) }.
intros A R.
pose (R' x y := Tr(exists2 x', Z2set x == x' & Tr(exists2 y', Z2set y == y' & R x' y'))).
assert (R'm : forall x x' y y', Z.eq_set x x' -> Z.eq_set y y' ->
     R' x y -> R' x' y').
 intros x x' y y' ? ? h; red; Tdestruct h as (x'',?,h); Tdestruct h as (y'',?,?).
 Texists x'';[|Texists y'';trivial].
  transitivity (Z2set x); trivial.
  apply Zeq_eq.
  symmetry; trivial.

  transitivity (Z2set y); trivial.
  apply Zeq_eq.
  symmetry; trivial.
apply set_intro with
  (Z.lst_rk(fun B => Tr(exists2 A', Z2set A' == A & forall x, Z.in_set x A' ->
      Tr(exists y, R' x y) ->
      Tr(exists2 y, Z.in_set y B & R' x y)))); intros.
 Tdestruct (Z2set_surj A) as (A',e).
 Tdestruct (Z.coll_ax_uniq EM A' R' (fun x x' y y' _ => R'm x x' y y')) as (B,HB); eauto.
 Texists B.
 revert HB; apply Z.lst_rk_morph; auto with *.
 intros.
 split; intros.
  Texists A'; intros; auto with *.
  Tdestruct (H0 x0 H1 H2) as (y,?,?); trivial.
  Texists y; trivial.
  revert H3; apply Zin_morph; auto with *.

  Tdestruct H0 as (A'',e',?).
  rewrite e in e'.
  apply eq_Zeq in e'.
  rewrite <- e' in H1.
  Tdestruct (H0 x0 H1 H2) as (y,?,?); trivial.
  Texists y; trivial.
  revert H3; apply Zin_morph; auto with *.

 apply Z.lst_fun with (1:=H) (2:=H0).

 Tdestruct Hex as (B,HB).
 assert (Bok := Z.lst_incl _ _ HB).
 Tdestruct Bok as (A',eA,Bok).
 Tdestruct (Z2set_surj x) as (x',ex).
 rewrite ex in H0; rewrite <- eA in H0; apply in_inZ in H0.
 assert (Tr(exists y, R' x' y)).
  Tdestruct H1 as (y,Rxy).
  Tdestruct (Z2set_surj y) as (y',ey).
  Texists y'; Texists x; [|Texists y]; auto with *.
 Tdestruct (Bok x' H0 H2)  as (y,?,?).
 Tdestruct H4 as (x'',?,h); Tdestruct h as (y',?,?).
 Texists (Z2set y).
  apply In_intro; simpl; intros.
  specialize Huniq with (1:=HB) (2:=H8).
  rewrite <- Huniq.
  rewrite H7; trivial.

  revert H6; apply H; trivial.
  rewrite ex; trivial.
Qed.

Definition coll A R := proj1_sig (coll_sig A R).
Lemma coll_ax : forall A (R:set->set->Prop), 
  Proper (eq_set==>eq_set==>iff) R ->
  forall x, x \in A -> Tr(exists y, R x y) ->
  Tr(exists2 y, y \in coll A R & R x y).
Proof (fun A R => proj2_sig (coll_sig A R)).

End Classic.
End ClassicCollection.

End Skolem.

Module IZF_R <: IZF_R_sig.
 Include Skolem CoqSublogic.

 Lemma wf_ax (P:set->Prop):
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
Proof (wf_axL P (fun x h => h)).

End IZF_R.

Module ZF0 <: ZF_sig.
 Include Skolem CoqSublogic.
 Lemma wf_ax (P:set->Prop):
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
 Proof (wf_axL P (fun x h => h)).
 Axiom EM : forall P, P \/ ~P.
 Definition coll := (ClassicCollection.coll EM).
 Lemma coll_ax : forall A R, 
    Proper (eq_set==>eq_set==>iff) R ->
    forall x, x \in A ->
      (exists y, R x y) -> exists2 y, y \in coll A R & R x y.
 Proof ClassicCollection.coll_ax EM.
End ZF0.

(** The "real" ZF, based only on TTColl (no ecluded-middle in the
    metatheory), but does not fit ZF_sig which is not parameterized
    by the logic.
 *)
Module ZF. (*<: ZF_sig.*)
 Include Skolem ClassicSublogic.
 Import Z.Lthms.
 Lemma wf_ax (P:set->Prop):
  (forall x, isL (P x)) ->
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
 Proof (wf_axL P).
 Lemma EM : forall P, Tr(P \/ (P -> Tr False)).
intros P nem.
apply nem.
right; intros p _.
apply nem.
left; exact p.
Qed.
 Definition coll := (ClassicCollection.coll EM).
 Lemma coll_ax : forall A R, 
    Proper (eq_set==>eq_set==>iff) R ->
    forall x, x \in A ->
      Tr(exists y, R x y) -> Tr(exists2 y, y \in coll A R & R x y).
 Proof ClassicCollection.coll_ax EM.
End ZF.

Let ZF0pack := (ZF0.repl_mono,ZF0.repl_ax,ZF0.coll_ax).
Let ZFpack := (ZF.repl_mono,ZF.repl_ax,ZF.coll_ax).
Print Assumptions ZF0pack. (* choice+EM *)
Print Assumptions ZFpack. (* choice *)
