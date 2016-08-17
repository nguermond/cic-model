
(** A theory about realizability of natural numbers.
    It is similar to SATnat, but it supports type-based termination

    Caveat: uses NAT instead of NAT', with all inhabitation problems this
    implies...
 *)

Require Import ZF ZFpairs ZFsum ZFord ZFfix ZFind_nat Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** NAT *)

Definition fNAT (A:set->SAT) : set->SAT :=
  sumReal (fun _ => unitSAT) A.

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
unfold sumReal.
apply interSAT_morph.
apply indexed_relation_id.
intros.
apply prodSAT_morph.
 unfold depSAT.
 apply interSAT_morph_subset; intros; auto with *.
 rewrite H0; reflexivity.

 apply prodSAT_morph; auto with *.
 unfold depSAT.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H0; reflexivity.

  apply prodSAT_morph; auto with *.
Qed.
Hint Resolve fNAT_morph.

Lemma fNAT_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI NATf o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI NATf (osucc o) -> x == x' -> eqSAT (fNAT R x) (fNAT R' x').
intros.
unfold fNAT.
apply interSAT_morph.
apply indexed_relation_id; intro C.
apply prodSAT_morph.
 apply interSAT_morph_subset; simpl; intros; auto with *.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H2; reflexivity.

  apply prodSAT_morph; auto with *.
  apply H0; auto with *.
  rewrite TI_mono_succ in H1; auto.
  rewrite Px in H1; apply sum_inv_r in H1; trivial.
Qed.

Definition ZE := INL ID.

Lemma Real_ZERO_gen A :
  inSAT ZE (fNAT A ZERO).
apply Real_inl.
 do 2 red; reflexivity.

 apply ID_intro.
Qed.

Definition SU := INR.

Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  inSAT t (A n) ->
  inSAT (SU t) (fNAT A (SUCC n)).
intros.
apply Real_inr; trivial.
Qed.

Definition NCASE f g n := Lc.App2 n (Lc.Abs (Lc.lift 1 f)) g.

Lemma ZE_iota t1 t2 :
  Lc.redp (NCASE t1 t2 ZE) t1.
unfold NCASE, ZE.
eapply t_trans.
 apply INL_iota.
apply t_step; apply Lc.red1_beta.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial.
rewrite Lc.lift0; trivial.
Qed.

Lemma SU_iota n t1 t2 :
  Lc.redp (NCASE t1 t2 (SU n)) (Lc.App t2 n).
unfold NCASE, SU.
apply INR_iota.
Qed.


Lemma Real_NATCASE_gen X A C n nt ft gt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATf X ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ X) A (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with ZFind_basic.UNIT X n (fun _ => unitSAT) A; trivial.
 apply piSAT0_intro.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in freal; trivial.

  intros x u eqn ureal.
  rewrite eqn in nty; apply sum_inv_l in nty.
  apply ZFind_basic.unit_elim in nty.
  rewrite nty in eqn.
  apply inSAT_exp; [right; apply sat_sn in ureal;trivial|].
  unfold Lc.subst; rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
  rewrite eqn; trivial.

 apply piSAT0_intro.
  apply sat_sn in greal; trivial.

  intros.
  rewrite H in nty; apply sum_inv_r in nty.
  rewrite H.
  apply piSAT0_elim with (1:=greal); trivial.
Qed.

Definition fNATi o := tiSAT NATf fNAT o.

Instance fNATi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) fNATi.
apply tiSAT_morph; auto.
Qed.

Lemma fNATi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ NATi o1 ->
  eqSAT (fNATi o1 x) (fNATi o2 x).
intros.
apply tiSAT_mono; trivial.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_succ_eq o x :
  isOrd o ->
  x ∈ NATi (osucc o) ->
  eqSAT (fNATi (osucc o) x) (fNAT (fNATi o) x).
intros.
apply tiSAT_succ_eq; auto.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma Real_ZERO o :
  isOrd o ->
  inSAT ZE (fNATi (osucc o) ZERO).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_ZERO_gen.

 apply ZEROi_typ; trivial.
Qed.

Lemma Real_SUCC o n t :
  isOrd o ->
  n ∈ NATi o ->
  inSAT t (fNATi o n) ->
  inSAT (SU t) (fNATi (osucc o) (SUCC n)).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_inr; trivial.
 apply fNATi_morph; reflexivity.

 apply SUCCi_typ; trivial.
Qed.


Lemma Real_NATCASE o C n nt ft gt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATi (osucc o) ->
  inSAT nt (fNATi (osucc o) n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ NATi o) (fNATi o) (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros oo Cm nty nreal freal greal.
rewrite fNATi_succ_eq in nreal; trivial.
unfold NATi in nty; rewrite TI_mono_succ in nty; auto.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
Qed.


(** * Structural fixpoint: *)

(** NATFIX m n --> m (NATFIX m) n when n is a (sum) constructor.
   let G m := "\n. (match n with inl _ => m | inr _ => m end) m n"
   let G m := \n. n (\_.m) (\_.m) m n
    G m -/-> ; G m (inl a) --> m m (inl a); G m (inr b) --> m m (inr b)
   NATFIX m n := G (\x. m (G x)) n
     --> (\x. m (G x)) (\x. m (G x)) n
     --> m (G (\x. m (G x))) n == m (NATFIX m) n
 *)
(*
Definition guard_sum m :=
  Lc.Abs (Lc.App2 (Lc.App2 (Lc.Ref 0) (Lc.Abs (Lc.lift 2 m)) (Lc.Abs (Lc.lift 2 m))) (Lc.lift 1 m) (Lc.Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Lc.Abs (Lc.Abs (Lc.App (Lc.Ref c) t))) ->
  Lc.redp (Lc.App (guard_sum m) n) (Lc.App2 m m n).
intros m n (t,(c,(eqc,eqn))).
unfold guard_sum.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
rewrite eqn.
eapply t_trans.
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.
destruct eqc; subst c.
 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl.
 rewrite Lc.lift0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.

 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl; rewrite Lc.simpl_subst_rec; auto.
 rewrite Lc.lift_rec0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.
Qed.

Lemma G_INL m a :
  Lc.redp (Lc.App (guard_sum m) (INL a)) (Lc.App2 m m (INL a)).
apply G_sim.
econstructor; exists 1; split; auto.
reflexivity.
Qed.
Lemma G_INR m a :
  Lc.redp (Lc.App (guard_sum m) (INR a)) (Lc.App2 m m (INR a)).
apply G_sim.
econstructor; exists 0; split; auto.
reflexivity.
Qed.
*)
(*
Lemma G_sn m :
  sn m -> sn (App guard_sum m).
unfold guard_sum; intros.
apply sat_sn with snSAT.

apply sn_abs.
apply sat_sn with snSAT.
apply prodSAT_elim with snSAT;[|apply varSAT].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_lift;trivial].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_abs;apply sn_lift;trivial].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_abs;apply sn_lift;trivial].
apply varSAT.
Qed.
*)
Lemma G_sat_gen A k m t X :
  k ∈ NAT ->
  inSAT t (fNAT A k) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App2 guard_sum m t) X.
intros.
unfold guard_sum.
apply GUARD_sat.
revert H1; apply inSAT_context.
apply inSAT_context.
intros.
rewrite NAT_eq in H.
apply WHEN_SUM_sat with (1:=H) (2:=H0); trivial.
Qed.


(*
Lemma sn_G_inv m : Lc.sn (guard_sum m) -> Lc.sn m.
intros.
unfold guard_sum in H.
eapply subterm_sn in H;[|constructor].
eapply subterm_sn in H;[|apply sbtrm_app_l].
eapply subterm_sn in H;[|apply sbtrm_app_r].
apply sn_lift_inv with (1:=H) (2:=eq_refl).
Qed.
*)

(**)

Lemma G_sat o x t m (X:SAT):
  isOrd o ->
  x ∈ NATi o ->
  inSAT t (fNATi o x) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App2 guard_sum m t) X.
intros.
assert (x ∈ NAT).
 apply NATi_NAT in H0; trivial.
apply TI_elim in H0; auto.
destruct H0 as (o',?,?).
assert (isOrd o') by eauto using isOrd_inv.
assert (osucc o' ⊆ o).
 red; intros.
 apply isOrd_plump with o'; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
rewrite <- TI_mono_succ in H4; auto.
rewrite <- fNATi_mono with (o1:=osucc o') in H1; auto.
rewrite fNATi_succ_eq in H1; auto.
apply G_sat_gen with (2:=H1); trivial.
Qed.


(* specialized fix *)

Definition NATFIX := FIXP WHEN_SUM.

Lemma ZE_iotafix m :
  Lc.redp (Lc.App (NATFIX m) ZE) (Lc.App2 m (NATFIX m) ZE).
apply FIXP_sim.
intros.
apply WHEN_SUM_INL.
Qed.
Lemma SU_iotafix m n :
  Lc.redp (Lc.App (NATFIX m) (SU n)) (Lc.App2 m (NATFIX m) (SU n)).
apply FIXP_sim.
intros.
apply WHEN_SUM_INR.
Qed.

Lemma NATFIX_sat : forall o m X,
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ NATi y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' =>o' ∈ osucc o) 
             (fun o1 => piSAT0 (fun n => n ∈ NATi o1) (fNATi o1) (X o1))
             (fun o1 => let o2 := osucc o1 in
                        piSAT0 (fun n => n ∈ NATi o2) (fNATi o2) (X o2))) ->
  inSAT (NATFIX m) (piSAT0 (fun n => n ∈ NATi o) (fNATi o) (X o)).
Require Import ZFcoc.
intros.
cut (inSAT (NATFIX m) (piSAT0 (fun n => n ∈ cc_bot(NATi o)) (fNATi o) (X o))).
 apply piSAT0_mono with (f:=fun x =>x); auto with *.
apply FIXP_sat0 with (T:=NATi) (U:=fun o => cc_bot (NATi o)) (RT:=fNATi); trivial.
 intros.
 apply cc_bot_ax in H4; destruct H4; [left|right].
  intros.
  apply tiSAT_outside_domain; auto with *.
   intros.
   eapply fNAT_irrel with (o:=o'); trivial.

   rewrite H4; intros mt_in.
   apply TI_elim in mt_in; auto.
   destruct mt_in as (o',?,mt_in).
   apply sum_ind with (3:=mt_in); intros.
    symmetry in H7; apply couple_mt_discr in H7; trivial.
    symmetry in H7; apply couple_mt_discr in H7; trivial.

  apply TI_elim in H4; auto.
  destruct H4 as (o',?,?); exists o'; trivial.
  rewrite <- TI_mono_succ in H5; eauto using isOrd_inv.

 exists empty; auto.

 intros.
 apply fNATi_mono; trivial.

 intros.
 apply WHEN_SUM_neutral; trivial.

 intros.
 unfold fNATi in H4; rewrite tiSAT_eq in H4; auto with *.
  apply TI_elim in H3; auto with *.
  destruct H3 as (o',?,?).
  eapply WHEN_SUM_sat with (1:=H6) (2:=H4); trivial.

  intros.
  apply fNAT_irrel with (o:=o'); auto.

 revert H1; apply piSAT0_mono with (f:=fun x=>x); intros; auto with *.
  apply piSAT0_mono with (f:=fun x=>x); intros; auto with *.
  reflexivity.
(*

apply FIXP_sat; trivial.
 intros.
 cut (sn (App2 (GUARD WHEN_SUM) m0 (Ref 0))).
  intro h; apply subterm_sn with (1:=h); auto.
  unfold App2; auto.
 apply sat_sn with snSAT.
 apply GUARD_neutral; trivial.
 apply WHEN_SUM_neutral.
 apply varSAT.

 intros.
 apply G_sat with (3:=H4); auto.

 intros.
 apply TI_elim in H4; auto.
 destruct H4 as (o',?,?); exists o'; trivial.
 rewrite <- TI_mono_succ in H5; eauto using isOrd_inv.

 intros.
 apply fNATi_mono; trivial.*)
Qed.