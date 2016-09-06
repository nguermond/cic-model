Set Implicit Arguments.
Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist ZFcoc.
Import ZFrepl.
Require Export ZFind_nat.

(** In this file we develop an alternative model of nat contain the empty set.
    In contrast with the standard model, we have extra values:
    ⊥, S ⊥, S S ⊥, etc.
    Interpreting the natural numbers just as N+{∅} would force to have
    S ⊥ = ⊥, and then (match S ⊥ with S k => g(k) end) would be ⊥ instead
    of g(⊥)... 
 *)

(** * Definition and properties of the new operator *)

Definition NATf' X := NATf (cc_bot X).

Instance NATf'_morph : morph1 NATf'.
do 2 red; intros.
apply NATf_morph.
apply cc_bot_morph; trivial.
Qed.

Instance NATf'_mono : Proper (incl_set==>incl_set) NATf'.
do 2 red; intros.
unfold NATf'; apply NATf_mono; trivial.
apply cc_bot_mono; auto with *.
Qed.

  Lemma mt_not_in_NATf' o x :
    isOrd o ->
    x ∈ TI NATf' o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold NATf' in H2.
rewrite H1 in H2.
apply NATf_case with (3:=H2); intros.
 apply discr_mt_pair in H3; trivial.
 apply discr_mt_pair in H4; trivial.
Qed.

Definition NAT' := TI NATf' omega.

Require Import ZFcont.

  Lemma cc_bot_cont o F :
    ext_fun o F ->
    (exists w, w ∈ o) ->
    cc_bot (sup o F) == sup o (fun y => cc_bot (F y)).
intros.
apply eq_set_ax; intros z.
rewrite cc_bot_ax.
rewrite sup_ax; auto with *.
rewrite sup_ax.
 split; intros.
  destruct H1 as [?|(w,?,?)]; eauto.
  destruct H0 as (w,?).
  exists w; trivial.
  rewrite H1; auto.

  destruct H1 as (w,?,?).
  rewrite cc_bot_ax in H2; destruct H2; eauto.

 do 2 red; intros; apply cc_bot_morph; auto.
Qed.

  Lemma NAT'_continuous : forall F,
    ext_fun omega F ->
    NATf' (sup omega F) == sup omega (fun n => NATf' (F n)).
intros.
unfold NATf', NATf.
rewrite <- sum_cont; auto.
 rewrite <- cst_cont.
 2:exists zero; apply zero_omega.
 rewrite cc_bot_cont; auto with *.
 exists zero; apply zero_omega.

 do 2 red; intros; apply cc_bot_morph; auto.
Qed.


  Lemma NAT'_eq : NAT' == NATf' NAT'.
unfold NAT' at 1, NAT, NATi.
assert (ext_fun omega (TI NATf')).
 do 2 red; intros; apply TI_morph; auto with *.
rewrite TI_eq; auto with *.
rewrite <- NAT'_continuous; trivial.
apply (Fmono_morph _ NATf'_mono).
unfold NAT'.
apply eq_set_ax; intros z.
rewrite sup_ax; auto.
split; intros.
 destruct H0 as (o,?,?).
 assert (isOrd o) by eauto using isOrd_inv.
 apply TI_intro with o; auto with *.
 rewrite <- TI_mono_succ; auto with *.
 revert H1; apply TI_incl; auto with *.

 apply TI_elim in H0; auto with *.
 destruct H0 as (o,?,?).
 exists (osucc o); auto.
  apply osucc_omega; trivial.

  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with omega; auto.
Qed.

  Lemma NATf'_stages o :
    isOrd o ->
    TI NATf' o ⊆ NAT'.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',?,?).
rewrite NAT'_eq.
revert H3; apply NATf'_mono; auto.
Qed.

  Lemma ZERO_typ' :
    ZERO ∈ NAT'.
rewrite NAT'_eq.
apply ZERO_typ_gen.
Qed.

  Lemma SUCC_typ' n :
    n ∈ cc_bot NAT' ->
    SUCC n ∈ NAT'.
intros.
rewrite NAT'_eq.
apply SUCC_typ_gen; auto.
Qed.

Lemma NAT'_ind P n :
  Proper (eq_set==>iff) P ->
  n ∈ cc_bot NAT' ->
  P empty ->
  P ZERO ->
  (forall m, m ∈ cc_bot NAT' -> P m -> P (SUCC m)) -> 
  P n.
intros.
revert n H0; unfold NAT'; apply isOrd_ind with (2:=isOrd_omega); intros.
apply cc_bot_ax in H6; destruct H6.
 rewrite H6; trivial.

 apply TI_elim in H6; auto with *.
 destruct H6 as (o',o'o,?).
 apply NATf_case with (3:=H6); intros.
  rewrite H7; trivial.

  rewrite H8; apply H3.
   revert H7; apply cc_bot_mono.
   apply NATf'_stages.
   apply isOrd_inv with y; trivial.

   apply H5 with o'; trivial. 
Qed.

Lemma NAT_NAT' : NAT ⊆ NAT'.
intros z tyz.
apply NAT_ind with (4:=tyz); intros.
 rewrite <- H0; trivial.

 apply ZERO_typ'.

 apply SUCC_typ'; auto.
Qed.


(** The usual recursor on NAT, extended to NAT' *)

Definition NREC f g n y :=
  forall (P:set->set->Prop),
  Proper (eq_set==>eq_set==>iff) P ->
  P empty empty ->
  P ZERO f ->
  (forall m z, m ∈ cc_bot NAT' -> P m z -> P (SUCC m) (g m z)) ->
  P n y.

Lemma NREC_mt f g : NREC f g empty empty.
red; intros; trivial.
Qed.
Lemma NREC_ZERO f g : NREC f g ZERO f.
red; intros; trivial.
Qed.
Lemma NREC_SUCC f g n y:
  n ∈ cc_bot NAT' -> NREC f g n y -> NREC f g (SUCC n) (g n y).
unfold NREC; intros.
apply H4; trivial.
apply H0; trivial.
Qed.
Instance NREC_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
intros.
rewrite (H0 _ _ (reflexivity m) _ _ (reflexivity z)).
auto.
Qed.
Instance NREC_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
subst x0; rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
Qed.

Lemma NREC_inv f g n y :
  NREC f g n y ->
   NREC f g n y /\
   ((n==empty/\y==empty) \/
    (n==ZERO/\y==f) \/
    (exists2 m, n == SUCC m & exists2 z, NREC f g m z & y==g m z)).
intros H; apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply NREC_morph_eq; auto with *.

  repeat apply or_iff_morphism.
   rewrite H0; rewrite H1; reflexivity.
   rewrite H0; rewrite H1; reflexivity.
   apply ex2_morph; red; intros.
    rewrite H0; reflexivity.
   apply ex2_morph; red; intros.
    apply NREC_morph_eq; auto with *.
    rewrite H1; reflexivity.

 split; auto with *.
 apply NREC_mt.

 split; auto with *.
 apply NREC_ZERO.

 destruct H1 as (?,_).
 split.
  apply NREC_SUCC; trivial.

  right; right.
  exists m;[reflexivity|].
  exists z; auto with *.
Qed.
Lemma NREC_inv_mt f g y :
  NREC f g empty y -> y == empty.
intros; apply NREC_inv in H;
   destruct H as (_,[(_,eqy)|[(abs,_)|(n,abs,_)]]); auto.
 apply discr_mt_pair in abs; contradiction.
 apply discr_mt_pair in abs; contradiction.
Qed.
Lemma NREC_inv_ZERO f g y :
  NREC f g ZERO y -> y == f.
intros; apply NREC_inv in H;
   destruct H as (_,[(abs,_)|[(_,eqy)|(n,abs,_)]]); auto.
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 apply NATf_discr in abs; contradiction.
Qed.
Lemma NREC_inv_SUCC f g n y :
  morph2 g ->
  NREC f g (SUCC n) y -> exists2 z, NREC f g n z & y == g n z.
intros; apply NREC_inv in H0;
   destruct H0 as (_,[(abs,_)|[(abs,_)|(m,eqS,(z,defz,eqy))]]).
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 symmetry in abs; apply NATf_discr in abs; contradiction.

 apply SUCC_inj in eqS.
 rewrite <- eqS in defz, eqy; eauto.
Qed.

Lemma NREC_uch_mt f g :
  uchoice_pred (NREC f g empty).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists empty; apply NREC_mt.
 apply NREC_inv_mt in H.
 apply NREC_inv_mt in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch_ZERO f g :
  uchoice_pred (NREC f g ZERO).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists f; apply NREC_ZERO.
 apply NREC_inv_ZERO in H.
 apply NREC_inv_ZERO in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  uchoice_pred (NREC f g n).
intros gm tyn.
apply NAT'_ind with (2:=tyn).
 do 2 red; intros; apply uchoice_pred_morph.
 red; intros; apply NREC_morph_eq; auto with *.

 apply NREC_uch_mt.

 apply NREC_uch_ZERO.

 intros m tym (_,((z,?),muniq)).
 split; [|split]; intros.
  rewrite <- H0; trivial.

  exists (g m z); apply NREC_SUCC; trivial.

  apply NREC_inv_SUCC in H0; trivial.
  apply NREC_inv_SUCC in H1; trivial.
  destruct H0 as (y,?,eqx).
  destruct H1 as (y',?,eqx').
  rewrite eqx; rewrite eqx'; apply gm; eauto with *.
Qed.

Definition NAT_RECT f g n := uchoice (NREC f g n).

Instance NAT_RECT_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph; trivial.
Qed.
Instance NAT_RECT_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph_eq; trivial.
Qed.

Lemma NAT_RECT_mt f g :
  NAT_RECT f g empty == empty.
symmetry; apply uchoice_ext.
 apply NREC_uch_mt.

 apply NREC_mt.
Qed.

Lemma NAT_RECT_ZERO f g :
  NAT_RECT f g ZERO == f.
symmetry; apply uchoice_ext.
 apply NREC_uch_ZERO.

 apply NREC_ZERO.
Qed.

Lemma NAT_RECT_eq f g n y :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  (NAT_RECT f g n == y <-> NREC f g n y).
intros.
assert (ch := NREC_uch f H H0).
assert (eqn := uchoice_def _ ch).
split; intros.
 rewrite <- H1; trivial.

 symmetry; apply uchoice_ext; trivial.
Qed.

Lemma NAT_RECT_SUCC f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  NAT_RECT f g (SUCC n) == g n (NAT_RECT f g n).
intros.
apply NAT_RECT_eq; trivial.
 apply cc_bot_intro.
 apply SUCC_typ'; trivial.

 apply NREC_SUCC; trivial.

 apply NAT_RECT_eq; trivial.
 reflexivity.
Qed.


Lemma NAT_RECT_typ f g n P :
  morph1 P ->
  n ∈ cc_bot NAT' ->
  empty ∈ P empty ->
  f ∈ P ZERO ->
  g ∈ cc_prod (cc_bot NAT') (fun m => cc_arr (P m) (P (SUCC m))) ->
  NAT_RECT f (fun m y => cc_app (cc_app g m) y) n ∈ P n.
intros.
apply NAT'_ind with (2:=H0).
 do 2 red; intros.
 apply in_set_morph; auto.  
 apply NAT_RECT_morph_eq; auto with *.

 rewrite NAT_RECT_mt; trivial.

 rewrite NAT_RECT_ZERO; trivial.

 intros.
 rewrite NAT_RECT_SUCC; trivial.
  apply cc_prod_elim with (2:=H4) in H3.
  apply cc_arr_elim with (1:=H3) (2:=H5).

  do 3 red; intros.
  rewrite H6; rewrite H7; reflexivity.
Qed.

(** Recursor on NAT' *)

Require Import ZFfunext ZFfixrec.

Definition NATREC' M :=
  NATREC (fun o' f => squash (M o' f)).

Section Recursor.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable M : set -> set -> set.
  Hypothesis Mm : morph2 M.

  Variable U : set -> set -> set.
  Hypothesis Um : morph2 U.
(*  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ cc_bot (TI NATf' o) -> x == x' ->
    U o x ⊆ U o' x'.*)
  Hypothesis Ubot : forall o x, empty ∈ U o x.

  Let Nati o := cc_bot (TI NATf' o).
  Let Ty' o := cc_prod (Nati o) (U o).
  Let F := fun o' f => squash (M o' f).
  Let Q' o f := forall x, x ∈ TI NATf' o -> cc_app f x ∈ U o x.

  Hypothesis Mtyp : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty' o -> M o f ∈ Ty' (osucc o).

  Definition NAT_ord_irrel' :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty' o -> g ∈ Ty' o' ->
    fcompat (Nati o) f g ->
    fcompat (Nati (osucc o)) (M o f) (M o' g).

  Hypothesis Mirrel : NAT_ord_irrel'.

  Instance morph_fix_body : morph2 F.
unfold F; do 3 red; intros.
apply squash_morph.
apply Mm; trivial.
Qed.
  Lemma ext_fun_ty : forall o,
    ext_fun (Nati o) (U o).
do 2 red; intros.
apply Um; auto with *.
Qed.

  Hypothesis fx_sub_U : forall o' o'' x,
    isOrd o' -> o' ⊆ o'' -> o'' ∈ osucc ord ->
    x ∈ Nati o' ->
    U o' x ⊆ U o'' x.
(*
Lemma Umorph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ Nati o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply U'mono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply U'mono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma U'ext : forall o, isOrd o -> o ⊆ ord -> ext_fun (TI NATf' o) (U' o).
red; red; intros.
apply U'morph; auto with *.
Qed.
*)

Lemma natprod_ext_mt o f :
  isOrd o ->
  f ∈ cc_prod (TI NATf' o) (U o) ->
  f ∈ cc_prod (Nati o) (U o).
intros oo fty.
apply cc_prod_ext_mt in fty; trivial.
 apply ext_fun_ty.

 intros h; apply mt_not_in_NATf' in h; trivial.
 apply h; reflexivity.
Qed.


  Lemma ty_fix_body : forall o f,
   o < osucc ord ->
   f ∈ cc_prod (TI NATf' o) (U o) ->
   F o f ∈ cc_prod (TI NATf' (osucc o)) (U (osucc o)).
unfold F; intros.
apply squash_typ.
 apply ext_fun_ty.

 intros h; apply mt_not_in_NATf' in h; auto with *.
 eauto using isOrd_inv.

 apply Mtyp.
  apply isOrd_inv with (osucc ord); auto.
  apply olts_le in H; trivial.
 apply natprod_ext_mt in H0; trivial.
 simpl; eauto using isOrd_inv. 
Qed.

  Lemma fix_body_irrel : forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ cc_prod (TI NATf' o) (U o) ->
    g ∈ cc_prod (TI NATf' o') (U o') ->
    fcompat (TI NATf' o) f g ->
    fcompat (TI NATf' (osucc o)) (F o f) (F o' g).
red; intros.
assert (o'typ : o' ∈ osucc ord).
 apply ole_lts; trivial.
assert (o0typ : o ∈ osucc ord).
 apply le_lt_trans with o'; auto.
 apply ole_lts; trivial.
unfold F.
assert (tyf : f ∈ Ty' o).
 unfold Ty'; apply natprod_ext_mt; trivial.
assert (tyg : g ∈ Ty' o').
 unfold Ty'; apply natprod_ext_mt; trivial.
assert (appm : forall X h, ext_fun X (cc_app h)).
 do 2 red; intros; apply cc_app_morph; auto with *.
rewrite squash_eq with (A:=TI NATf' (osucc o)) (B:= U (osucc o)).
rewrite cc_beta_eq; trivial.
2:intros h; apply mt_not_in_NATf' in h; auto with *.
2:apply Mtyp; trivial.
2:transitivity o'; trivial.
rewrite squash_eq with (A:=TI NATf' (osucc o')) (B:= U (osucc o')).
rewrite cc_beta_eq; trivial.
3:intros h; apply mt_not_in_NATf' in h; auto with *.
3:apply Mtyp; trivial.
apply Mirrel; trivial.
 red; intros.
 unfold Nati in H7; rewrite cc_bot_ax in H7.
 destruct H7; auto.
 rewrite H7.
 rewrite cc_app_outside_domain.
  rewrite cc_app_outside_domain; auto with *.
   rewrite cc_eta_eq with (1:=H4).
   apply is_cc_fun_lam; trivial.

   intros h; apply mt_not_in_NATf' in h; auto with *.

  rewrite cc_eta_eq with (1:=H3).
  apply is_cc_fun_lam; trivial.

  intros h; apply mt_not_in_NATf' in h; auto with *.

  apply cc_bot_intro; trivial.

revert H6; apply TI_mono; auto with *.
apply osucc_mono; trivial.
Qed.

  Let Qty o f :
    isOrd o ->
    (is_cc_fun (TI NATf' o) f /\ Q' o f <-> f ∈ cc_prod (TI NATf' o) (U o)).
split; intros.
 destruct H0.
 rewrite cc_eta_eq' with (1:=H0).
 apply cc_prod_intro; auto.
  do 2 red; intros; apply cc_app_morph; auto with *.

  do 2 red; intros; apply Um; auto with *.

 split.
  rewrite cc_eta_eq with (1:=H0).
  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  apply cc_prod_elim with (1:=H0); trivial.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty.

  Lemma NATREC'_recursor o :
    isOrd o -> o ⊆ ord -> recursor o (TI NATf') Q' F.
split; intros; trivial.
 apply TI_morph; auto.

 rewrite TI_eq; auto with *.
 apply sup_morph;[reflexivity|red; intros].
 symmetry; rewrite <- H3; apply TI_mono_succ; auto with *.
 eauto using isOrd_inv.

 (* Q ext *)
 red; intros.
 rewrite <- H3.
 rewrite <- H3 in H6.
 red in H4.
 rewrite <- H4; auto.

 (* Q cont *)
 red; intros.
 apply TI_inv in H5; auto with *.
 destruct H5 as (o',?,?).
 red in H4; specialize H4 with (1:=H5) (2:=H6).
 revert H4; apply fx_sub_U; eauto using isOrd_inv with *.
  red; intros; apply le_lt_trans with o'; auto.

  apply ole_lts; trivial.
  transitivity o; trivial.

  unfold Nati; auto.

 (* F typing *)
 apply Qty; auto.
 apply ty_fix_body.
  apply ole_lts; auto.
  transitivity o; trivial.

  apply Qty; auto.

 (* F irr *)
 red; intros.
 destruct H3 as (?,fty).
 destruct H4 as (?,gty).
 apply Qty in fty; trivial.
 apply Qty in gty; trivial.
 apply fix_body_irrel; auto with *.
 transitivity o; trivial.
Qed.


  Lemma NATREC'_typ_strict o :
    isOrd o ->
    o ⊆ ord ->
    NATREC' M o ∈ cc_prod (TI NATf' o) (U o).
intros.
destruct REC_wt with (1:=H) (2:=NATREC'_recursor H H0).
apply Qty; auto.
Qed.
Hint Resolve NATREC'_typ_strict.

  Lemma NATREC'_typ o:
    isOrd o ->
    o ⊆ ord ->
    NATREC' M o ∈ cc_prod (Nati o) (U o).
intros.
apply natprod_ext_mt; trivial.
apply NATREC'_typ_strict with (1:=H); trivial.
Qed.
Hint Resolve NATREC'_typ.


  Lemma NATREC'_strict o x :
    isOrd o ->
    o ⊆ ord ->
    ~ x ∈ TI NATf' o ->
    cc_app (NATREC' M o) x == empty.
intros.
eapply cc_app_outside_domain.
 rewrite cc_eta_eq with (f:=NATREC' M o).
  eapply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  apply NATREC'_typ_strict; trivial.

  trivial.
Qed.

  Lemma NATREC'_mt o :
    isOrd o ->
    o ⊆ ord ->
    cc_app (NATREC' M o) empty == empty.
intros.
apply NATREC'_strict; trivial.
intros h; apply mt_not_in_NATf' in h; auto with *.
Qed.

  Lemma NATREC'_irr o o' x :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    x ∈ Nati o ->
    cc_app (NATREC' M o) x == cc_app (NATREC' M o') x.
intros.
apply cc_bot_ax in H3; destruct H3.
 rewrite H3.
 rewrite NATREC'_mt; trivial.
 2:transitivity o'; trivial.
 rewrite NATREC'_mt; auto with *.

 apply REC_ord_irrel with (1:=H0) (2:=NATREC'_recursor H0 H2); auto with *.
Qed.

Lemma fix_eqn0 : forall o,
  isOrd o ->
  o ⊆ ord ->
  NATREC' M (osucc o) == F o (NATREC' M o).
intros.
unfold NATREC', NATREC at 1; fold F.
rewrite REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H1 as (o',o'lt,zty).
 change (z ∈ F o (NATREC' M o)).
 change (z ∈ F o' (NATREC' M o')) in zty.
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ o) by (apply olts_le; auto).
 assert (o'le' : o' ⊆ ord) by (transitivity o; trivial).
 assert (F o' (NATREC' M o') ∈ cc_prod (TI NATf' (osucc o')) (U (osucc o'))).
  apply ty_fix_body; auto.
  apply ole_lts; auto.
 assert (F o (NATREC' M o) ∈ cc_prod (TI NATf' (osucc o)) (U (osucc o))).
  apply ty_fix_body; auto.
  apply ole_lts; auto.
 rewrite cc_eta_eq with (1:=H1) in zty.
 rewrite cc_eta_eq with (1:=H2).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  revert n'ty; apply TI_mono; auto with *.
  apply osucc_mono; auto.
 exists y; trivial.
 revert yty; apply eq_elim.
 apply fix_body_irrel; auto with *.
 red; intros.
 apply NATREC'_irr; auto.
 apply cc_bot_intro; trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.


Lemma NATREC'_unfold : forall o n,
  isOrd o ->
  o ⊆ ord ->
  n ∈ TI NATf' (osucc o) ->
  cc_app (NATREC' M (osucc o)) n ==
  cc_app (M o (NATREC' M o)) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
rewrite squash_beta with (3:=H1) (B:=U (osucc o)).
 reflexivity.

 intros h; apply mt_not_in_NATf' in h; auto with *.

 apply Mtyp; auto.
 unfold Ty'; auto.
Qed.



Lemma NATREC'_typ_app o n:
  isOrd o ->
  o ⊆ ord ->
  n ∈ Nati o ->
  cc_app (NATREC' M o) n ∈ U o n.
intros.
apply cc_prod_elim with (dom:=Nati o); trivial.
apply NATREC'_typ; trivial.
Qed.

Lemma NATREC'_eqn : forall o n,
  isOrd o ->
  o ⊆ ord ->
  n ∈ TI NATf' o ->
  cc_app (NATREC' M o) n ==
  cc_app (M o (NATREC' M o)) n.
intros.
apply TI_inv in H1; auto with *.
destruct H1 as (o',?,?).
assert (o'o: isOrd o') by eauto using isOrd_inv.
rewrite <- NATREC'_irr with (o:=osucc o'); auto.
 rewrite NATREC'_unfold; auto.
 eapply Mirrel; auto.
  unfold Ty'; auto.
  unfold Ty'; auto.

  red; intros.
  apply NATREC'_irr; auto.

  apply cc_bot_intro; trivial.

 red; intros.
 apply le_lt_trans with o'; trivial.

 apply cc_bot_intro; trivial.
Qed.


(*......*)

(*

  Lemma NATREC_typing' : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (TI NATf' o) f -> Q' o f -> f ∈ Ty' o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply U'ext; trivial.
Qed.

Let Q'm :
   forall o o',
   isOrd o ->
   o ⊆ ord ->
   o == o' -> forall f f', fcompat (TI NATf' o) f f' -> Q' o f -> Q' o' f'.
intros.
unfold Q' in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply U'mono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.


Let Q'cont : forall o f : set,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI NATf' o) f ->
 (forall o' : set, o' ∈ o -> Q' (osucc o') f) -> Q' o f.
intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
2:apply NATf'_mono.
generalize (H2 _ H3 _ H4).
apply U'mono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Q'typ : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI NATf' o) f ->
 Q' o f -> is_cc_fun (TI NATf' (osucc o)) (F o f) /\ Q' (osucc o) (F o f).
intros.
assert (F o f ∈ Ty' (osucc o)).
 apply Ftyp'; trivial.
 apply NATREC_typing'; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma NATREC_recursor' : recursor ord (TI NATf') Q' F.
split; auto.
 apply TI_morph.

 intros.
 apply TI_mono_eq; auto with *.

 red; red; intros.
 destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
 apply Firrel'; trivial.
  apply NATREC_typing'; trivial. 
  transitivity o'; trivial.

  apply NATREC_typing'; trivial. 
Qed.

  Lemma NATREC_wt' : NATREC' F ord ∈ Ty' ord.
intros.
destruct REC_wt with (1:=oord) (2:=NATREC_recursor').
apply NATREC_typing'; auto with *.
Qed.

  Lemma NATREC_ind' : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x ∈ NATf' (TI NATf' o) ->
     (forall y, y ∈ TI NATf' o -> P o y (cc_app (NATREC F ord) y)) ->
     forall w, isOrd w -> w ⊆ ord -> lt o w ->
     P w x (cc_app (F ord (NATREC F ord)) x)) ->
    x ∈ TI NATf' ord ->
    P ord x (cc_app (NATREC F ord) x).
intros.
unfold NATREC.
apply REC_ind with (2:=NATREC_recursor'); auto.
intros.
apply TI_elim in H4; auto with *.
destruct H4 as (o',?,?).
apply H0 with o'; eauto using isOrd_inv.
red; auto.
Qed.

  Lemma NATREC_expand' : forall n,
    n ∈ TI NATf' ord -> cc_app (NATREC F ord) n == cc_app (F ord (NATREC F ord)) n.
intros.
apply REC_expand with (2:=NATREC_recursor') (Q:=Q'); auto.
Qed.

  Lemma NATREC_irrel' o o' :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    eq_fun (TI NATf' o) (cc_app (NATREC F o)) (cc_app (NATREC F o')).
red; intros.
rewrite <- H4.
apply REC_ord_irrel with (2:=NATREC_recursor'); auto with *.
Qed.

*)
End Recursor.

(** * Universe facts: NAT' belongs to any Grothendieck universes that
      is contains omega.
 *)

Section NAT'_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.

  Lemma G_NATf' X : X ∈ U -> NATf' X ∈ U.
intros.
assert (empty ∈ U).
 apply G_incl with X; trivial.
intros z h; apply empty_ax in h; contradiction.
unfold NATf'.
apply G_sum; trivial.
 unfold ZFind_basic.UNIT.
 apply G_union2; trivial.
 apply G_singl; trivial.

 apply G_union2; trivial.
 apply G_singl; auto.
Qed.

  Lemma G_NAT' : omega ∈ U -> NAT' ∈ U.
intros.
apply G_TI; auto with *.
apply G_NATf'.
Qed.

End NAT'_Univ.
