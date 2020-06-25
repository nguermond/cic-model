Require Import basic.
Require Import EnsUniv.

Inductive VV :=
| small : S.set -> VV
| large : B.set -> VV.

Definition spart (x : VV) : S.set :=
  match x with
  | small sx => sx
  | large lx => S.empty
  end.

Definition lpart (x : VV) : B.set :=
  match x with
  | small sx => (injU sx)
  | large lx => lx
  end.

Definition Spart x := small (spart x).

Definition int_small (x : VV) : Prop :=
  match x with
  | small _ => True
  | large _ => False
  end.

Definition int_small_b (x : VV) : bool :=
  match x with
  | small _ => true
  | large _ => false
  end.

Definition VV_in_set (x y : VV) : Prop :=
  B.in_set (lpart x) (lpart y).

Definition VV_eq_set (x y : VV) : Prop :=
  B.eq_set (lpart x) (lpart y).

Definition VV_S_empty : VV := small S.empty.
Definition VV_B_empty : VV := large B.empty.
Definition VV_empty : VV := VV_S_empty.

Definition VV_S_pair (x y : VV) : VV :=
  (small (S.pair (spart x) (spart y))).

Definition VV_B_pair (x y : VV) : VV :=
  (large (B.pair (lpart x) (lpart y))).

Definition VV_pair (x y : VV) : VV :=
  if (int_small_b x && int_small_b y)%bool
  then (VV_S_pair x y)
  else (VV_B_pair x y).

Definition VV_S_union (x : VV) : VV :=
  (small (S.union (spart x))).

Definition VV_B_union (x : VV) : VV :=
  (large (B.union (lpart x))).

Definition VV_union (x : VV) : VV :=
  if (int_small_b x)
  then (VV_S_union x)
  else (VV_B_union x).

Definition VV_S_subset (x : VV) (P : VV -> Prop) : VV :=
  (small (S.subset (spart x) (compose P small))).

Definition VV_B_subset (x : VV) (P : VV -> Prop) : VV :=
  (large (B.subset (lpart x) (compose P large))).

Definition VV_subset (x : VV) (P : VV -> Prop) : VV :=
  if (int_small_b x)
  then (VV_S_subset x P)
  else (VV_B_subset x P).

Definition VV_S_infinity : VV := small S.infinity.
Definition VV_B_infinity : VV := large B.infinity.
Definition VV_infinity : VV := VV_S_infinity.

Definition VV_S_power (x : VV) : VV :=
  (small (S.power (spart x))).

Definition VV_B_power (x : VV) : VV :=
  (large (B.power (lpart x))).

Definition VV_power (x : VV) : VV :=
  if (int_small_b x)
  then (VV_S_power x)
  else (VV_B_power x).

Instance VV_eq_set_equiv : Equivalence VV_eq_set.
Proof.
  split.
  - intro x. unfold VV_eq_set. reflexivity.
  - intros x y. unfold VV_eq_set. symmetry. trivial.
  - intros x y z. unfold VV_eq_set. transitivity (lpart y). trivial. trivial.
Qed.

Instance VV_in_set_cong_2 (z : VV) : Proper (VV_eq_set==>iff) (VV_in_set z).
Proof.
  split; apply (B.eq_set_ax (lpart x) (lpart y)); trivial.
Qed.

Lemma VV_eq_set_ax (x y : VV) : VV_eq_set x y <->
                                (forall z, (VV_in_set z x) <-> (VV_in_set z y)).
Proof.
  split.
  - intros H z. rewrite H. reflexivity. (* requires congruence *)
  - intro H. apply (B.eq_set_ax (lpart x) (lpart y)).
    intro z. apply (H (large z)).
Qed.

Instance VV_in_set_cong : Proper (VV_eq_set==>VV_eq_set==>iff) VV_in_set.
Proof.
  intros x x' p y y' q.
  rewrite <- q. (* requires congruence on second argument *)
  split; intro H.
  - apply (B.in_reg (lpart x) (lpart x')). trivial. trivial.
  - apply (B.in_reg (lpart x') (lpart x)). symmetry. trivial. trivial.
Qed.

Instance large_cong : Proper (B.eq_set==>VV_eq_set) large.
Proof.
  intros x y. trivial.
Qed.
Instance small_cong : Proper (S.eq_set==>VV_eq_set) small.
Proof.
  intros x y. apply (lift_eq x y).
Qed.
Instance lpart_cong : Proper (VV_eq_set==>B.eq_set) lpart.
Proof.
  intros x y H. trivial.
Qed.
Lemma spart_cong : forall x x', (int_small x) -> (int_small x') ->
                                (VV_eq_set x x') -> (S.eq_set (spart x) (spart x')).
Proof.
  destruct x,x'. intros.
  unfold VV_eq_set, lpart in H1.
  apply down_eq. trivial.
  contradiction. contradiction. contradiction.
Qed.


Lemma VV_eq_lpart (x : VV) : VV_eq_set (large (lpart x)) x.
Proof.
  destruct x.
  - unfold VV_eq_set. reflexivity.
  - reflexivity.
Qed.


Lemma lift_VV_S_empty : VV_eq_set VV_S_empty VV_B_empty.
Proof.
  apply empty_equiv.
Qed.

Lemma ext_VV_empty : VV_eq_set VV_empty VV_B_empty.
Proof.
  rewrite lift_VV_S_empty.
  reflexivity.
Qed.

Lemma VV_empty_ax : forall x, (not (VV_in_set x VV_empty)).
Proof.
  intros x H. rewrite ext_VV_empty in H.
  contradiction (B.empty_ax (lpart x)).
Qed.

Lemma VV_lift_S_pair : forall a b, (int_small a) /\ (int_small b) ->
                                   (VV_eq_set (VV_S_pair a b) (VV_B_pair a b)).
Proof.
  intros a b [Sa Sb].
  destruct a as [sa|la]; destruct b as [sb|lb].
  { unfold VV_S_pair, VV_B_pair. simpl.
    rewrite pair_equiv. unfold VV_eq_set. reflexivity. }
  contradiction. contradiction. contradiction.
Qed.

Lemma ext_VV_pair : forall a b, (VV_eq_set (VV_pair a b) (VV_B_pair a b)).
Proof.
  destruct a as [sa|la]; destruct b as [sb|lb]; unfold VV_pair; simpl.
  { rewrite VV_lift_S_pair. reflexivity. simpl. auto. }
  reflexivity. reflexivity. reflexivity.
Qed.

Lemma VV_pair_ax : forall a b x, (VV_in_set x (VV_pair a b)) <->
                                 (VV_eq_set x a \/ VV_eq_set x b).
Proof.
  intros a b x.
  rewrite ext_VV_pair.
  apply (B.pair_ax (lpart a) (lpart b) (lpart x)).
Qed.

Lemma VV_lift_S_union : forall a, (int_small a) ->
                                  (VV_eq_set (VV_S_union a) (VV_B_union a)).
Proof.
  intros a H.
  destruct a as [sa|la].
  - unfold VV_S_union, VV_B_union. simpl. rewrite union_equiv.
    unfold VV_eq_set. reflexivity.
  - contradiction.
Qed.

Lemma ext_VV_union : forall a, (VV_eq_set (VV_union a) (VV_B_union a)).
Proof.
  destruct a as [sa|la]; unfold VV_union; simpl.
  { rewrite VV_lift_S_union. reflexivity. simpl. auto. }
  reflexivity.
Qed.

Lemma VV_union_ax : forall a x, (VV_in_set x (VV_union a)) <->
                                (exists2 y, VV_in_set x y & VV_in_set y a).
Proof.
  intros a x.
  rewrite ext_VV_union.
  split.
  - intro H.
    destruct (B.union_ax (lpart a) (lpart x)) as [K K'].
    destruct (K H) as [y A B].
    exists (large y). trivial. trivial.
  - intro H.
    destruct H as [y A B].
    apply (B.union_ax (lpart a) (lpart x)).
    exists (lpart y). trivial. trivial.
Qed.



Lemma VV_lift_S_subset : forall a P, (int_small a) ->
                                   Proper (VV_eq_set==>iff) P ->
                                   (VV_eq_set (VV_S_subset a P) (VV_B_subset a P)).
Proof.
  intros a P H C.
  destruct a as [sa|la].
  { unfold VV_eq_set, VV_S_subset, VV_B_subset, lpart.
    rewrite subset_equiv. reflexivity.
    { intros x y K. unfold compose. apply C.
      rewrite K. unfold VV_eq_set, lpart. reflexivity. } }
  contradiction.
Qed.

Lemma ext_VV_subset : forall a P, Proper (VV_eq_set==>iff) P ->
                                  (VV_eq_set (VV_subset a P) (VV_B_subset a P)).
Proof.
  destruct a as [sa|la]; intros P C; unfold VV_subset; simpl.
  { rewrite VV_lift_S_subset. reflexivity. simpl. auto. trivial. }
  reflexivity.
Qed.

Lemma VV_subset_ax : forall a P x, (Proper (VV_eq_set==>iff) P) ->
                                ((VV_in_set x (VV_subset a P)) <->
                                 (VV_in_set x a /\ (P x))).
Proof.
  intros a P x C.
  rewrite ext_VV_subset. 2:trivial.
  destruct ((B.subset_ax) (lpart a) (compose P large) (lpart x)) as [H0 H1].
  split; intro K.
  - split.
    + apply H0. trivial.
    + destruct (H0 K) as [H00 [z H01]].
      rewrite <- VV_eq_lpart.
      rewrite H01. trivial.
  - apply H1.
    split.
    + apply K.
    + exists (lpart x). reflexivity.
      rewrite <- (VV_eq_lpart x) in K. apply K.
Qed.

Lemma VV_lift_S_infinity : VV_eq_set VV_S_infinity VV_B_infinity.
Proof.
  unfold VV_eq_set, VV_S_infinity, VV_B_infinity.
  rewrite infinity_equiv.
  reflexivity.
Qed.

Lemma ext_VV_infinity : VV_eq_set VV_infinity VV_B_infinity.
Proof.
  rewrite VV_lift_S_infinity.
  reflexivity.
Qed.

Lemma VV_infinity_ax1 : VV_in_set VV_empty VV_infinity.
Proof.
  rewrite ext_VV_infinity, ext_VV_empty.
  unfold VV_B_infinity, VV_in_set, lpart.
  apply B.infty_ax1.
Qed.

Instance VV_union_cong : Proper (VV_eq_set==>VV_eq_set) VV_union.
Proof.
Admitted.

Instance VV_pair_cong : Proper (VV_eq_set==>VV_eq_set==>VV_eq_set) VV_pair.
Proof.
Admitted.

Instance VV_B_pair_cong : Proper (VV_eq_set==>VV_eq_set==>VV_eq_set) VV_B_pair.
Proof.
Admitted.


Lemma VV_infinity_ax2 : forall x, (VV_in_set x VV_infinity) ->
                                  (VV_in_set (VV_union (VV_pair x (VV_pair x x)))
                                             VV_infinity).
Proof.
  intros x H.
  rewrite ext_VV_infinity, ext_VV_pair, ext_VV_pair, ext_VV_union in *.
  unfold VV_infinity, VV_pair, VV_in_set.
  apply (B.infty_ax2 (lpart x)). trivial.
Qed.

Lemma VV_lift_S_power : forall a, (int_small a) ->
                                  (VV_eq_set (VV_S_power a) (VV_B_power a)).
Proof.
  intros a Sa.
  destruct a as [sa|la].
  { unfold VV_eq_set, VV_S_power, VV_B_power, lpart.
    rewrite power_equiv. reflexivity. }
  contradiction.
Qed.

Lemma ext_VV_power : forall a, VV_eq_set (VV_power a) (VV_B_power a).
  destruct a as [sa|la]; unfold VV_power; simpl.
  { rewrite VV_lift_S_power. reflexivity. simpl. auto. }
  reflexivity.
Qed.

Lemma VV_power_ax : forall a x, VV_in_set x (VV_power a) <->
                                (forall y, (VV_in_set y x) -> (VV_in_set y a)).
Proof.
  intros a x.
  rewrite ext_VV_power.
  pose (B.power_ax (lpart a) (lpart x)) as H.
  split; intro K.
  - intro y. destruct H as [H0 H1].
    apply H0. apply K.
  - apply H.
    intro y. apply (K (large y)).
Qed.

Lemma VV_wf_ax : forall (P : VV -> Prop),
    Proper (VV_eq_set==>iff) P ->
    (forall x, (forall y, (VV_in_set y x) -> P y) -> P x) -> (forall x, P x).
Proof.
  intros P C H.
  pose (B.wf_ax (compose P large)) as Ax.
  intro x. rewrite <- VV_eq_lpart. apply Ax.
  intros x' K. apply H.
  intro y. rewrite <- VV_eq_lpart. apply K.
Qed.

Lemma spart_int_small : forall x, (int_small x) -> (VV_eq_set (small (spart x)) x).
Proof.
  destruct x; simpl.
  reflexivity. contradiction.
Qed.

Definition el (a : VV) := { x : VV | VV_in_set x a}.
Definition inj_el {a : VV} (p : int_small a) (x : (el a)) : (el (Spart a)).
Proof.
  assert (a = (Spart a)).
  destruct a. trivial. contradiction.
  rewrite <- H. trivial.
Defined.

Definition S_el {a : S.set} (w : {x : S.set | S.in_set x a}) : (el (small a)) :=
  (let (x, p) := w in
   (exist _ (small x) (lift_in x a p))).
Definition B_el {a : B.set} (w : {x : B.set | B.in_set x a}) : (el (large a)) :=
  (let (x, p) := w in
   (exist _ (large x) p)).

(* S_el (a : S.set) : {x : S.set | S.in_set x a} -> el (small a) *)
Definition VV_S_repl1 (a : VV) (F : (el (Spart a)) -> VV) : VV :=
  small (S.repl1 (spart a) (compose spart (compose F S_el))).

(* B_el (a : B.set) : {x : B.set | B.in_set x a} -> el (large a) *)
Definition VV_B_repl1 (a : VV) (F : (el a) -> VV) : VV :=
  large (B.repl1 (lpart a) (compose lpart (compose F B_el))).

Definition VV_S_replf (a : VV) (F : VV -> VV) : VV :=
  small (S.replf (spart a) (compose spart (compose F small))).

Definition VV_B_replf (a : VV) (F : VV -> VV) : VV :=
  large (B.replf (lpart a) (compose lpart (compose F large))).

(* On ne peut pas étendre VV_S_replf, VV_S_repl1, car
   on ne peut pas décider si F préserve les petits ensembles. *)

(* B_el (a : B.set) : {x : B.set | B.in_set x a} -> el (large a) *)
(* S_el (a : S.set) : {x : S.set | S.in_set x a} -> el (small a) *)
(* inj_el (a : VV) : int_small a -> el a -> el (Spart a) *)
Lemma VV_lift_S_repl1 :
  forall (a : VV) (F : (el (Spart a)) -> VV) (p : int_small a),
    (forall (x y : (el (Spart a))),
        (VV_eq_set (proj1_sig x) (proj1_sig y)) -> (VV_eq_set (F x) (F y))) ->
    (forall x, (int_small (F x))) ->
    (VV_eq_set (VV_S_repl1 a F) (VV_B_repl1 a (compose F (inj_el p)))).
Proof.
  intros a F p C SH.
  destruct a as [sa|la].
  { unfold VV_B_repl1, VV_S_repl1, VV_eq_set, compose, lpart.
    rewrite repl1_equiv. reflexivity.
    - reflexivity.
    - intros x x' H.
      pose (SH (inj_el p (B_el x'))) as SH1.
      pose (SH (S_el x)) as SH2.
      fold (lpart (F (inj_el p (B_el x')))).
      rewrite <- (spart_int_small (F (inj_el _ _))).
      apply lift_eq.
      apply spart_cong.
      trivial. trivial.
      apply C. destruct x,x'.
      unfold inj_el, B_el, S_el. simpl in *.
      apply H. apply SH1. }
  contradiction.
Qed.

(* Lemma replf_equiv : forall a f F, *)
(*     (forall x, F (injU x) == injU (f x)) -> *)
(*     B.replf (injU a) F == injU (S.replf a f). *)
(* Proof. *)
(* Admitted. *)

(* Lemma VV_lift_S_replf (a : VV) (F : VV -> VV) : *)
(*   Proper (VV_eq_set==>VV_eq_set) F -> *)
(*   (int_small a) -> (forall x, (int_small x) -> (int_small (F x))) -> *)
(*   (VV_eq_set (VV_S_replf a F) (VV_B_replf a F)). *)
(* Proof. *)
(*   intros C Sa H. *)
(*   destruct a as [sa|la]. *)
(*   { unfold VV_eq_set, VV_S_replf, VV_B_replf, compose, lpart. *)
(*     rewrite replf_equiv. reflexivity. *)
(*     { intro x. fold (lpart (F (large (injU x)))). simpl. *)
(*       specialize (H (small x) I). *)
(*       assert ((injU (spart (F (small x)))) == (lpart (F (small x)))) as R. *)
(*       { unfold lpart. *)
(*         revert H. *)
(*         destruct (F (small x)). *)
(*         - reflexivity. *)
(*         - contradiction. } *)
(*       assert (VV_eq_set (F (large (injU x))) (F (small x))) as R'. *)
(*       { apply C. unfold VV_eq_set. reflexivity. } *)
(*       rewrite R', R. reflexivity. } } *)
(*   contradiction. *)
(* Qed. *)

Lemma VV_repl1_ax (a : VV) (F : (el a) -> VV) : forall y,
  (forall x x', (VV_eq_set (proj1_sig x) (proj1_sig x')) ->
                (VV_eq_set (F x) (F x'))) ->
  ((VV_in_set y (VV_B_repl1 a F)) <-> (exists x, VV_eq_set y (F x))).
Proof.
  intros y C.
  remember (compose lpart (compose F B_el)) as F'.
  assert (forall z z', proj1_sig z == proj1_sig z' -> F' z == F' z') as H.
  { intros z z' K.
    rewrite HeqF'. unfold compose.
    apply lpart_cong. apply C.
    destruct z, z'. apply large_cong. trivial. }
  pose (B.repl1_ax (lpart a) F' (lpart y) H) as K.
  rewrite HeqF' in K.
  destruct K as [K0 K1].
  split; intro L.
  - destruct (K0 L) as [y0 p].
    exists (B_el y0).
    unfold VV_eq_set. rewrite p. reflexivity.
  - apply K1. destruct L as [x0 p].
    exists (exist _ (lpart (proj1_sig x0)) (proj2_sig x0)).
    unfold compose.
    apply lpart_cong. rewrite p. apply C.
    destruct x0. simpl.
    unfold VV_eq_set. reflexivity.
Qed.

Lemma VV_replf_ax : forall a F y, Proper (VV_eq_set==>VV_eq_set) F ->
                                  ((VV_in_set y (VV_B_replf a F)) <->
                                   (exists2 x, (VV_in_set x a) &
                                               (VV_eq_set y (F x)))).
Proof.
  intros a F y C.
  remember (fun x => (lpart (F (large x)))) as F'.
  assert (forall z z', (B.in_set z (lpart a)) -> z == z' -> F' z == F' z').
  { intros z z' K p.
    rewrite HeqF'. apply lpart_cong.
    apply C. apply large_cong. trivial. }
  pose (B.replf_ax (lpart a) F' (lpart y) H) as K.
  rewrite HeqF' in K.
  destruct K as [K0 K1].
  split; intro L.
  - destruct (K0 L) as [y0 p].
    exists (large y0). trivial. trivial.
  - apply K1. destruct L as [x0 p].
    exists (lpart x0). trivial. apply lpart_cong.
    rewrite VV_eq_lpart. trivial.
Qed.

(* (* On pourrait utiliser une égalité extensionelle sur F *) *)
(* Instance VV_replf_cong : Proper (VV_eq_set==>eq==>VV_eq_set) VV_B_replf. *)
(* (* use B.replf_morph *) *)
(* Admitted. *)

Definition tr_el : forall a a', (VV_eq_set a a') -> (el a) -> (el a').
Proof.
  intros a a' H x.
  destruct x.
  apply (exist _ x).
  apply (VV_eq_set_ax a a').
  trivial. trivial.
Defined.


Lemma VV_repl1_cong : forall a a' F F',
    (VV_eq_set a a') ->
    (forall x x', (VV_eq_set (proj1_sig x) (proj1_sig x')) ->
                  VV_eq_set (F x) (F' x')) ->
    (VV_eq_set (VV_B_repl1 a F) (VV_B_repl1 a' F')).
Proof.
  intros a a' F F' H L.
  unfold VV_B_repl1.
  rewrite (B.repl1_morph (lpart a) (lpart a')
                         (compose lpart (compose F B_el))
                         (compose lpart (compose F' B_el))).
  reflexivity.
  apply H.
  intros x y K.
  unfold compose. apply lpart_cong.
  apply symmetry in H.
  apply (L (B_el x) (B_el y)).
  destruct x,y.
  simpl in *.
  apply K.
Qed.

Definition VV_U : VV := large U.

Lemma VV_U_elim : forall x, (VV_in_set x VV_U) <->
                                        (exists x', (VV_eq_set x (small x'))).
Proof.
  intro x.
  split; intro H.
  - apply U_elim. trivial.
  - destruct H as [sx H'].
    rewrite H'. apply (U_intro sx).
Qed.

Record VV_weak_grot_univ (U : VV) : Prop :=
  {G_trans : forall x y, (VV_in_set y x) -> (VV_in_set x VV_U) ->
                         (VV_in_set y VV_U);
   G_pair : forall x y, (VV_in_set x VV_U) -> (VV_in_set y VV_U) ->
                        (VV_in_set (VV_pair x y) VV_U);
   G_power : forall x, (VV_in_set x VV_U) -> (VV_in_set (VV_power x) VV_U);
   G_union_wrepl1 : forall a F,
       (forall x x', (VV_eq_set (proj1_sig x) (proj1_sig x')) ->
                     (VV_eq_set (F x) (F x'))) ->
       (VV_in_set a VV_U) ->
       (forall x, (int_small (F x))) ->
       (VV_in_set (VV_union (VV_B_repl1 a F)) VV_U)
  }.

Lemma VV_U_trans : forall x y, (VV_in_set y x) -> (VV_in_set x VV_U)
                               -> (VV_in_set y VV_U).
Proof.
  intros x y H K.
  apply (U_trans (lpart x) (lpart y)).
  trivial. trivial.
Qed.


Lemma VV_U_pair : forall x y, (VV_in_set x VV_U) -> (VV_in_set y VV_U) ->
                              (VV_in_set (VV_pair x y) VV_U).
Proof.
  intros x y H K.
  rewrite ext_VV_pair.
  apply U_pair.
  trivial. trivial.
Qed.

Lemma VV_U_power : forall x, (VV_in_set x VV_U) ->
                             (VV_in_set (VV_power x) VV_U).
Proof.
  intros x H.
  rewrite ext_VV_power.
  apply U_power.
  trivial.
Qed.

Lemma VV_U_union : forall x, (VV_in_set x VV_U) ->
                             (VV_in_set (VV_union x) VV_U).
Proof.
  intros x H.
  rewrite ext_VV_union.
  apply U_union.
  trivial.
Qed.

Lemma VV_U_wrepl1 : forall a F,
    (forall x x', (VV_eq_set (proj1_sig x) (proj1_sig x')) ->
                  (VV_eq_set (F x) (F x'))) ->
    (VV_in_set a VV_U) ->
    (forall x, (int_small (F x))) ->
    (VV_in_set (VV_B_repl1 a F) VV_U).
Proof.
  intros a F C Sa SF.
  destruct (VV_U_elim a) as [L0 L1].
  apply L0 in Sa.
  destruct Sa as [sa p].
  apply symmetry in p.
  rewrite  (VV_repl1_cong a (small sa) F (compose F (tr_el _ _ p))).
  - rewrite <- (VV_lift_S_repl1 (small sa) (compose F (tr_el _ _ p)) I).
    + unfold VV_S_repl1. apply (VV_U_elim).
      exists (S.repl1 sa (fun x => spart (F (tr_el _ _ p (S_el x))))).
      reflexivity.
    + unfold Spart, compose. simpl.
      intros x y H.
      apply C.
      destruct x, y.
      unfold tr_el. simpl in *.
      apply H.
    + unfold Spart, compose. simpl.
      intro x.
      specialize (SF (tr_el _ _ p x)).
      trivial.
  - symmetry. trivial.
  - intros x x' H.
    apply (C x (tr_el (small sa) a p x')).
    destruct x, x'.
    trivial.
Qed.

(* Lemma VV_U_wreplf : *)
(*   forall a F, Proper (VV_eq_set==>VV_eq_set) F -> *)
(*               (VV_in_set a VV_U) -> *)
(*               (forall x, (int_small x) -> (int_small (F x))) -> *)
(*               (VV_in_set (VV_B_replf a F) VV_U). *)
(* Proof. *)
(*   intros a F C H SH. *)
(*   destruct (VV_U_elim a) as [L0 L1]. *)
(*   destruct (L0 H) as [I L2]. *)
(*   apply (VV_U_elim (VV_B_replf a F)). *)
(*   exists (S.replf I (compose spart (compose F small))). *)
(*   rewrite L2. *)
(*   unfold VV_B_replf, lpart. *)
(*   rewrite replf_equiv. *)
(*   split; intro i; exists i; reflexivity. *)
(*   intro x. *)
(*   assert (forall w, (injU w) = (lpart (small w))). *)
(*   {  trivial. } *)
(*   unfold compose. *)
(*   rewrite (H0 (spart (F (small x)))). *)
(*   apply lpart_cong. *)
(*   rewrite (spart_int_small (F (small x))). *)
(*   apply C. unfold VV_eq_set. reflexivity. *)
(*   apply SH. simpl. auto. *)
(* Qed. *)

Lemma VV_U_union_wrepl1 : forall a F,
      (forall x x', (VV_eq_set (proj1_sig x) (proj1_sig x')) ->
                    (VV_eq_set (F x) (F x'))) ->
      (VV_in_set a VV_U) ->
      (forall x, (int_small (F x))) ->
      (VV_in_set (VV_union (VV_B_repl1 a F)) VV_U).
Proof.
  intros a F C H SH.
  apply VV_U_union.
  apply VV_U_wrepl1.
  trivial. trivial. trivial.
Qed.

(* Lemma VV_U_union_wreplf : forall I F, *)
(*     (Proper (VV_eq_set==>VV_eq_set) F) -> *)
(*     (VV_in_set I VV_U) -> *)
(*     (forall x, (int_small x) -> (int_small (F x))) -> *)
(*     (VV_in_set (VV_union (VV_B_replf I F)) VV_U). *)
(* Proof. *)
(*   intros I F C H SH. *)
(*   apply VV_U_union. *)
(*   apply VV_U_wreplf. *)
(*   trivial. trivial. trivial. *)
(* Qed. *)


Theorem VV_U_weak_grot_univ : VV_weak_grot_univ VV_U.
Proof.
  split.
  - apply VV_U_trans.
  - apply VV_U_pair.
  - apply VV_U_power.
  - apply VV_U_union_wrepl1.
Qed.
