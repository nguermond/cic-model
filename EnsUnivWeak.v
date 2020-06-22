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

Definition Spart (x : VV) : VV := (small (spart x)).
Definition Lpart (x : VV) : VV := (large (lpart x)).

Definition VV_in_set (x y : VV) : Prop :=
  B.in_set (lpart x) (lpart y).

Definition VV_eq_set (x y : VV) : Prop :=
  B.eq_set (lpart x) (lpart y).

Definition VV_empty : VV := small S.empty.

Definition VV_pair (x y : VV) : VV :=
  large (B.pair (lpart x) (lpart y)).

Definition VV_union (x : VV) : VV :=
  large (B.union (lpart x)).

Definition VV_subset (x : VV) (P : VV -> Prop) : VV :=
  large (B.subset (lpart x) (compose P large)).

Definition VV_infinity : VV := small S.infinity.

Definition VV_power (x : VV) : VV :=
  large (B.power (lpart x)).

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
  - intros H z. apply VV_in_set_cong_2. trivial.
  - intro H. apply (B.eq_set_ax (lpart x) (lpart y)).
    intro z. apply (H (large z)).
Qed.

Instance VV_in_set_cong : Proper (VV_eq_set==>VV_eq_set==>iff) VV_in_set.
Proof.
  intros x x' p y y' q.
  rewrite <- q.
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

Lemma lift_VV_empty : VV_eq_set VV_empty (large B.empty).
Proof.
  apply empty_equiv.
Qed.

Lemma VV_empty_ax : forall x, (not (VV_in_set x VV_empty)).
  intros x H.
  rewrite lift_VV_empty in H.
  contradiction (B.empty_ax (lpart x)).
Qed.

Lemma VV_pair_ax : forall a b x, (VV_in_set x (VV_pair a b)) <->
                                 (VV_eq_set x a \/ VV_eq_set x b).
Proof.
  intros a b x.
  apply (B.pair_ax (lpart a) (lpart b) (lpart x)).
Qed.

Lemma VV_union_ax : forall a x, (VV_in_set x (VV_union a)) <->
                                (exists2 y, VV_in_set x y & VV_in_set y a).
Proof.
  intros a x.
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

Lemma VV_eq_lpart (x : VV) : VV_eq_set (large (lpart x)) x.
Proof.
  destruct x.
  - unfold VV_eq_set. reflexivity.
  - reflexivity.
Qed.

(* This no longer holds if P is not assumed well defined on VV *)
Lemma subset_ax : forall a P x, (Proper (VV_eq_set==>iff) P) ->
                                ((VV_in_set x (VV_subset a P)) <->
                                 (VV_in_set x a /\ (P x))).
Proof.
  pose (B.subset_ax) as H.
  intros a P x C.
  destruct (H (lpart a) (compose P large) (lpart x)) as [H0 H1].
  split.
  - intro K.
    split.
    + apply H0. trivial.
    + destruct (H0 K) as [H00 [z H01]].
      rewrite <- VV_eq_lpart.
      rewrite H01. trivial.
  - intro K.
    apply H1.
    split.
    + apply K.
    + exists (lpart x). reflexivity.
      rewrite <- (VV_eq_lpart x) in K. apply K.
Qed.

Lemma VV_infinity_ax1 : VV_in_set VV_empty VV_infinity.
Proof.
  rewrite lift_VV_empty.
  unfold VV_infinity.
  unfold VV_in_set. unfold lpart.
  rewrite infinity_equiv.
  apply B.infty_ax1.
Qed.

Lemma VV_infinity_ax2 : forall x, (VV_in_set x VV_infinity) ->
                                  (VV_in_set
                                     (VV_union (VV_pair x (VV_pair x x))) VV_infinity).
Proof.
  intros x H.
  unfold VV_infinity.
  unfold VV_pair.
  unfold VV_in_set.
  rewrite infinity_equiv.
  simpl. apply (B.infty_ax2 (lpart x)).
  rewrite <- infinity_equiv. trivial.
Qed.

Lemma VV_power_ax : forall a x, VV_in_set x (VV_power a) <->
                                (forall y, (VV_in_set y x) -> (VV_in_set y a)).
Proof.
  intros a x.
  pose (B.power_ax (lpart a) (lpart x)) as H.
  split; intro K.
  - intro y. destruct H as [H0 H1].
    apply H0. apply K.
  - apply H.
    intro y. apply (K (large y)).
Qed.



Lemma VV_wf_ax : forall (P : VV -> Prop),
    (forall x, (forall y, (VV_in_set y x) -> P y) -> P x) -> (forall x, P x).
Proof.
Admitted.


(* repl n'est pas admis dans VV? *)
(* Lemma VV_repl_ax : forall a R, *)
(*     Proper (VV_eq_set==>VV_eq_set==>iff) R -> *)
(*     (forall x y y', (R x y) -> (R x y') -> (VV_eq_set y y')) -> *)
(*     (exists b, (forall y, (VV_in_set y b) <-> *)
(*                           (exists2 x, (VV_in_set x a) & (R x y)))). *)
(* Proof. *)
(* Admitted. *)


Definition VV_replf (a : VV) (F : VV -> VV) : VV :=
  large (B.replf (lpart a) (fun x => (lpart (F (large x))))).

Lemma VV_replf_ax : forall a F y, Proper (VV_eq_set==>VV_eq_set) F ->
                                  ((VV_in_set y (VV_replf a F)) <->
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

(* we need intensional equality on F *)
Instance VV_replf_cong : Proper (VV_eq_set==>eq==>VV_eq_set) VV_replf.
(* use B.replf_morph *)
Admitted.

Definition VV_U : VV := large U.

Lemma VV_U_char : forall x, (VV_in_set x VV_U) <->
                                        (exists x', (VV_eq_set x (small x'))).
Admitted.

Definition intensionally_small (x : VV) : Prop :=
  match x with
  | small _ => True
  | large _ => False
  end.

(* The converse does not hold! *)
Lemma int_small_in_VV_U : forall x, (intensionally_small x) -> (VV_in_set x VV_U).
Admitted.

Lemma spart_int_retraction (x : VV) : (intensionally_small x) ->
                                      (VV_eq_set (small (spart x)) x).
Proof.
  intro H.
  destruct x as [sx|lx].
  - reflexivity.
  - split; contradiction.
Qed.

Record VV_grot_univ (U : VV) : Prop :=
  {G_trans : forall x y, (VV_in_set y x) -> (VV_in_set x VV_U) ->
                         (VV_in_set y VV_U);
   G_pair : forall x y, (VV_in_set x VV_U) -> (VV_in_set y VV_U) ->
                        (VV_in_set (VV_pair x y) VV_U);
   G_power : forall x, (VV_in_set x VV_U) -> (VV_in_set (VV_power x) VV_U);
   G_union_wreplf : forall I F,
       (Proper (VV_eq_set==>VV_eq_set) F) ->
       (VV_in_set I VV_U) ->
       (forall x, intensionally_small (F x)) ->
       (VV_in_set (VV_union (VV_replf I F)) VV_U)
  }.

Lemma VV_U_weak_replf :
  forall a F, Proper (VV_eq_set==>VV_eq_set) F ->
              (VV_in_set a VV_U) ->
              (forall x, (intensionally_small (F x))) ->
              (VV_in_set (VV_replf a F) VV_U).
Proof.
  intros a F C H K.
  destruct (VV_U_char a) as [L0 L1].
  destruct (L0 H) as [I L2].
  destruct (VV_U_char (VV_replf a F)) as [M0 M1].
  apply M1.
  exists (S.replf I (compose spart (compose F small))).
  rewrite L2.
  unfold VV_replf.
  remember (fun x => (lpart (F (large x)))) as F'.
  unfold lpart.
  rewrite replf_equiv. unfold VV_eq_set. simpl.
  split; intro i; exists i; reflexivity.
  rewrite HeqF'.
  intro x.
  pose (spart_int_retraction (F (small x))).
  assert (forall w, (injU w) = (lpart (small w))).
  { intro w. trivial. }
  unfold compose.
  rewrite (H0 (spart (F (small x)))).
  apply lpart_cong.
  rewrite v. apply C.
  unfold VV_eq_set. reflexivity.
  apply K.
Qed.
