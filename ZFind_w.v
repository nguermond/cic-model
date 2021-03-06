Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist.
Import ZFrepl.

(** In this file we develop the theory of W-types:
    - typing
    - existence of a fixpoint
    - recursor
 *)

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(* The intended type operator *)
Definition W_F X := Σ x ∈ A, cc_arr (B x) X.

Lemma wfm1 : forall X, ext_fun A (fun x => cc_arr (B x) X).
do 2 red; intros.
apply cc_arr_morph; auto with *.
Qed.
Hint Resolve wfm1.

Lemma W_F_intro X a f :
  ext_fun (B a) f ->
  a ∈ A ->
  (forall i, i ∈ B a -> f i ∈ X) ->
  couple a (cc_lam (B a) f) ∈ W_F X.
intros.
apply couple_intro_sigma; auto with *.
apply cc_arr_intro; intros; auto with *.
Qed.

Lemma W_F_elim X x :
  x ∈ W_F X ->
  fst x ∈ A /\
  (forall i, i ∈ B (fst x) -> cc_app (snd x) i ∈ X) /\
  x ==couple (fst x) (cc_lam (B (fst x)) (cc_app (snd x))). 
intros.
assert (ty1 := fst_typ_sigma _ _ _ H).
assert (eq1 := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
split; trivial.
split; intros.
 apply cc_arr_elim with (1:=H); trivial.

 rewrite cc_eta_eq with (1:=H) in eq1; trivial.
Qed.

Instance W_F_mono : Proper (incl_set ==> incl_set) W_F.
do 3 red; intros.
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
rewrite H2.
apply W_F_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Instance W_F_morph : morph1 W_F.
apply Fmono_morph; auto with *.
Qed.

Lemma W_F_stable : stable W_F.
unfold W_F.
apply sigma2_stable_class; auto with *.
 intros; apply cc_prod_ext; auto with *.
 red; trivial.

 intros.
 apply cc_prod_stable_class; intros; auto.
 apply id_stable_class.
Qed.

Lemma WFi_ext a a' f f' :
  a ∈ A ->
  a == a' ->
  (a == a' -> eq_fun (B a) f f') ->
  couple a (cc_lam (B a) f) == couple a' (cc_lam (B a') f').
intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
Qed.

Lemma WFi_inv a a' Y Y' f f' :
  couple a (cc_lam Y f) == couple a' (cc_lam Y' f') ->
  ext_fun Y f ->
  ext_fun Y' f' ->
  (a == a' -> Y == Y') ->
  a == a' /\ eq_fun Y f f'.
intros.
apply couple_injection in H; destruct H; split; trivial.
red; intros.
assert (eqr := cc_app_morph _ _ H3 _ _ H5).
rewrite cc_beta_eq in eqr; trivial.
rewrite cc_beta_eq in eqr; trivial.
rewrite <- H2; trivial; rewrite <- H5; trivial.
Qed.


  Definition WFmap f x :=
    couple (fst x) (λ i ∈ B (fst x), f (cc_app (snd x) i)).

  Lemma WFmap_ext : forall f f' x x',
    fst x ∈ A ->
    fst x == fst x' ->
    (forall i i', i ∈ B (fst x) -> i == i' ->
     f (cc_app (snd x) i) == f' (cc_app (snd x') i')) ->
    WFmap f x == WFmap f' x'.
intros.
apply WFi_ext; auto.
Qed.

  Instance WFmap_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) WFmap.
do 3 red; intros.
apply couple_morph.
 apply fst_morph; trivial.

 apply cc_lam_ext; intros.
  rewrite H0; reflexivity.

  red; intros.
  apply H.
  rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma WFmap_comp : forall f g X Y x,
  morph1 g ->
  morph1 f ->
  (forall x, x ∈ X -> g x ∈ Y) ->
  x ∈ W_F X ->
  WFmap f (WFmap g x) == WFmap (fun x => f (g x)) x.
intros.
unfold WFmap.
apply W_F_elim in H2; destruct H2 as (?,(?,_)).
symmetry; apply WFi_ext; intros; auto.
 rewrite fst_def; reflexivity.

 red; intros.
 apply H0; auto.
 rewrite snd_def.
 rewrite <- H6.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros; apply H; auto.
 rewrite H8; reflexivity.
Qed.

Lemma WF_eta : forall X x,
  x ∈ W_F X ->
  x == WFmap (fun x => x) x.
intros.
apply W_F_elim in H; destruct H as (_,(_,?)); assumption.
Qed.

  Lemma WFmap_inj : forall X Y g g' x x',
    x ∈ W_F X -> x' ∈ W_F Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a ∈ X -> a' ∈ Y -> g a == g' a' -> a == a') ->
    WFmap g x == WFmap g' x' -> x == x'.
unfold WFmap; intros.
apply W_F_elim in H; destruct H as (?,(?,?)).
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
apply WFi_inv in H4; auto.
 destruct H4.
 red in H9.
 rewrite H6; rewrite H8; apply WFi_ext; intros; auto.
 red; intros.
 apply H3; auto.
 apply H7.
 rewrite <- H12; revert H11; apply eq_elim; apply Bm; trivial.

 do 2 red; intros; apply H1; auto.
 rewrite H10; reflexivity.

 do 2 red; intros; apply H2; auto.
 rewrite H10; reflexivity.
Qed.

  Lemma WFmap_typ : forall X Y f x,
    ext_fun X f ->
    x ∈ W_F X ->
    (forall a, a ∈ X -> f a ∈ Y) ->
    WFmap f x ∈ W_F Y.
intros.
apply W_F_elim in H0; destruct H0 as (?,(?,_)).
apply W_F_intro; auto.
do 2 red; intros.
apply H; auto.
rewrite H4; reflexivity.
Qed.

Require Import ZFiso.

Lemma WFmap_iso X Y f :
  iso_fun X Y f ->
  iso_fun (W_F X) (W_F Y) (WFmap f).
intros isof.
assert (fm := iso_funm isof).
assert (fext : ext_fun X f).
 apply morph_is_ext; trivial.
constructor; intros.
 apply WFmap_morph; trivial.

 red; intros.
 eapply WFmap_typ with (2:=H); intros; trivial.
 apply (iso_typ isof); trivial.

 apply WFmap_inj with (1:=H)(2:=H0) in H1; intros; trivial.
 apply (iso_inj isof) in H4; trivial.

 exists (WFmap (iso_inv X f) y).
  apply WFmap_typ with (2:=H); intros; trivial.
   apply morph_is_ext; apply (iso_funm (iso_fun_sym isof)).

   apply iso_inv_typ with (1:=isof); trivial.

  rewrite WFmap_comp with (1:=iso_funm (iso_fun_sym isof)) (2:=fm) (4:=H); intros; trivial.
   transitivity (WFmap (fun x => x) y).
   2:symmetry; apply WF_eta with (1:=H); trivial.
   apply WFmap_ext; intros; auto with *.
    apply W_F_elim with (1:=H).

    rewrite <- H1.
    apply iso_inv_eq with (1:=isof); trivial.
    apply W_F_elim with (1:=H); trivial.

   apply iso_inv_typ with (1:=isof); trivial.
Qed.

(** * Encoding W-types as sets of path in a tree *)

(** We show that up to isomorphism, W_F is equivalent to another
    operator Wf, which has a bound. This bound is the set of trees represented
    as a partial function from paths (indexed by the union of all B(x)) to
    labels (of type A).
 *)

(** The construction domain and the constructor *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x :=
   singl (couple Nil (fst x)) ∪
   sup (B (fst x)) (fun y =>
      replf (cc_app (snd x) y)
        (fun p => couple (Cons y (fst p)) (snd p))).

Instance Wsup_morph : morph1 Wsup.
do 2 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply sup_morph.
  rewrite H; reflexivity.

  red; intros.
  apply replf_morph_raw; auto.
   rewrite H; rewrite H1; reflexivity.

   red; intros.
   rewrite H1; rewrite H2; reflexivity.
Qed.

Lemma Wsup_ext : forall X, ext_fun (W_F X) Wsup.
do 2 red; intros; apply Wsup_morph; trivial.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X g,
  ext_fun X (fun y =>
     replf (cc_app g y) (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
Hint Resolve Wsup_ext wext1 wext2.

Lemma Wsup_def :
  forall x p,
  (p ∈ Wsup x <->
   p == couple Nil (fst x) \/
   exists2 i, i ∈ B (fst x) &
   exists2 q, q ∈ cc_app (snd x) i &
   p == couple (Cons i (fst q)) (snd q)).
intros x p; intros.
unfold Wsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; auto.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.

 destruct H as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.

Lemma Wsup_hd_prop : forall a x,
  (couple Nil a ∈ Wsup x <-> a == fst x).
split; intros.
 apply union2_elim in H; destruct H.
  apply singl_elim in H.
  apply couple_injection in H; destruct H; trivial.

  rewrite sup_ax in H; auto.
  destruct H.
  rewrite replf_ax in H0; trivial.
  destruct H0.
  apply couple_injection in H1; destruct H1 as (H1,_).
   apply discr_mt_couple in H1; contradiction.

 rewrite H.
 unfold Wsup.
 apply union2_intro1.
 apply singl_intro.
Qed.

Lemma Wsup_tl_prop : forall X i l a x,
  x ∈ W_F X ->
  X ⊆ Wdom ->
  (couple (Cons i l) a ∈ Wsup x <->
   i ∈ B (fst x) /\ couple l a ∈ cc_app (snd x) i).
intros X i l a x H inclX.
apply W_F_elim in H; destruct H as (tyx, (tys,_)).
rewrite Wsup_def.
split; intros.
 destruct H.
  apply couple_injection in H; destruct H as (H,_).
  symmetry in H.
  apply discr_mt_couple in H; contradiction.

  destruct H as (i',?,(q,?,?)).
  apply couple_injection in H1; destruct H1.
  apply couple_injection in H1; destruct H1.
  rewrite H1.
  split; trivial.
  specialize tys with (1:=H).
  apply inclX in tys.
  specialize power_elim with (1:=tys) (2:=H0); intro.
  rewrite H3; rewrite H2.
  rewrite <- surj_pair with (1:=H4); trivial.

 destruct H.
 right; exists i; trivial.
 exists (couple l a); trivial.
 rewrite fst_def; rewrite snd_def; reflexivity.
Qed.

Lemma Wsup_inj : forall X Y x x',
  X ⊆ Wdom ->
  Y ⊆ Wdom ->
  x ∈ W_F X ->
  x' ∈ W_F Y ->
  Wsup x == Wsup x' -> x == x'.
intros X Y x x' tyf tyf' H H0 H1.
destruct W_F_elim with (1:=H) as (?,(?,?)).
destruct W_F_elim with (1:=H0) as (?,(?,?)).
rewrite H4; rewrite H7; apply WFi_ext; intros; auto.
 generalize (Wsup_hd_prop (fst x) x); intro.
 generalize (Wsup_hd_prop (fst x) x'); intro.
 apply H9.
 rewrite <- H1.
 apply H8.
 reflexivity.

 red; intros.
 assert (x'0 ∈ B (fst x')).
  revert H9; apply in_set_morph; auto with *.
 assert (cc_app (snd x) x0 ⊆ prodcart (List (sup A B)) A).
  red; intros.
  apply power_elim with (2:=H12); auto.
 assert (cc_app (snd x') x'0 ⊆ prodcart (List (sup A B)) A).
  red; intros.
  apply power_elim with (2:=H13); auto.
 generalize (fun z l => Wsup_tl_prop _ x0 l z _ H tyf); intros.
 generalize (fun z l => Wsup_tl_prop _ x'0 l z _ H0 tyf'); intros.
 apply eq_intro; intros.
  generalize (surj_pair _ _ _ (H12 _ H16)); intro.
  rewrite H17.
  apply H15.
  rewrite <- H10; rewrite <- H1; rewrite H14.
  rewrite <- H17; auto.

  generalize (surj_pair _ _ _ (H13 _ H16)); intro.
  rewrite H17.
  apply H14.
  rewrite H10; rewrite H1; rewrite H15.
  rewrite <- H17; auto.
Qed.

Lemma Wsup_typ_gen : forall X x,
  X ⊆ Wdom ->
  x ∈ W_F X ->
  Wsup x ∈ Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H1; trivial.
apply W_F_elim in H0; destruct H0 as (?,(?,_)).
destruct H1 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply couple_intro; trivial.
 apply Nil_typ.

 assert (q ∈ prodcart (List (sup A B)) A).
  specialize H2 with (1:=H1); apply H in H2.
  apply power_elim with (1:=H2); trivial.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax; eauto with *.

   apply fst_typ with (1:=H4).

  apply snd_typ with (1:=H4).
Qed.

(** The type operator on the construction domain *)
Definition Wf X := replf (W_F X) Wsup.

Hint Resolve Wsup_morph.

Lemma Wf_intro : forall x X,
  x ∈ W_F X ->
  Wsup x ∈ Wf X.
intros.
unfold Wf.
rewrite replf_ax; trivial.
exists x; auto with *.
Qed.

Lemma Wf_elim : forall a X,
  a ∈ Wf X ->
  exists2 x, x ∈ W_F X &
  a == Wsup x.
intros.
unfold Wf in H.
rewrite replf_ax in H; trivial.
Qed.

Instance Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 3 red; intros.
apply Wf_elim in H0; destruct H0 as (f,?,?).
rewrite H1; apply Wf_intro; trivial.
clear H1; revert f H0.
apply W_F_mono; trivial.
Qed.

Instance Wf_morph : morph1 Wf.
apply Fmono_morph; auto with *.
Qed.
Hint Resolve Wf_mono Wf_morph.

Lemma Wf_typ : forall X,
  X ⊆ Wdom -> Wf X ⊆ Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,?,?).
rewrite H1.
apply Wsup_typ_gen with X; auto with *.
Qed.
Hint Resolve Wf_typ.

Lemma Wf_stable0 (K:set->Prop) :
  (forall X, K X -> X ⊆ Wdom) ->
 stable_class K Wf.
red; intros Kdef X Xty z H.
unfold Wf.
assert (forall a, a ∈ X -> z ∈ Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Wf_morph; trivial.
 exists a; auto with *.
rewrite replf_ax; auto.
destruct inter_wit with (2:=H).
 apply Fmono_morph; trivial.
assert (z ∈ Wf x); auto.
apply Wf_elim in H2.
destruct H2.
exists x0; auto.
apply W_F_stable; auto.
apply inter_intro.
 intros.
 rewrite replf_ax in H4.
 2:red;red;intros;apply W_F_morph; auto.
 destruct H4.
 rewrite H5; clear y H5.
 specialize H0 with (1:=H4).
 apply Wf_elim in H0; destruct H0.
 rewrite H3 in H5; apply Wsup_inj with (X:=x) (Y:=x1)in H5; auto.
 rewrite H5; trivial.

 exists (W_F x).
 rewrite replf_ax.
 2:red;red;intros;apply W_F_morph;auto.
 exists x; auto with *.
Qed.

Lemma Wf_stable : stable_class (fun X : set => X ⊆ Ffix Wf Wdom) Wf.
apply Wf_stable0.
intros.
rewrite H; apply Ffix_inA.
Qed.

Lemma W_F_Wf_iso X :
  X ⊆ Wdom ->
  iso_fun (W_F X) (Wf X) Wsup.
split; intros.
 apply Wsup_morph.

 red; intros.
 apply Wf_intro; trivial.

 apply Wsup_inj with X X; auto.

 destruct Wf_elim with (1:=H0); eauto with *.
Qed.

(** The fixpoint of Wf (we have shown that Wf is monotone, bounded and stable) *)

Definition W' := Ffix Wf Wdom.

Lemma W'typ : W' ⊆ Wdom.
apply Ffix_inA.
Qed.

Lemma Wi_W' : forall o, isOrd o -> TI Wf o ⊆ W'.
apply TI_Ffix; auto.
Qed.

Lemma TI_Wf_elim : forall a o,
  isOrd o ->
  a ∈ TI Wf o ->
  exists2 o', lt o' o &
  exists2 x, x ∈ W_F (TI Wf o') &
  a == Wsup x.
intros.
apply TI_elim in H0; trivial.
destruct H0.
apply Wf_elim in H1.
eauto.
Qed.

Lemma Wsup_typ : forall o x,
  isOrd o ->
  x ∈ W_F (TI Wf o) ->
  Wsup x ∈ TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

Lemma W'_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x ∈ W_F (TI Wf o') ->
   (forall i, i ∈ B (fst x) -> P (cc_app (snd x) i)) ->
   P (Wsup x)) ->
  forall a, a ∈ W' -> P a.
intros.
unfold W' in H1; rewrite Ffix_def in H1; auto.
destruct H1.
revert a H2.
apply isOrd_ind with (2:=H1); intros.
apply TI_Wf_elim in H5; trivial.
destruct H5 as (o',?,(x',?,?)).
destruct W_F_elim with (1:=H6) as (_,(?,_)).
rewrite H7; clear a H7.
apply H0 with o'; eauto.
apply isOrd_inv with y; eauto.
Qed.

(** The closure ordinal of Wf (and W_F) *)

  Definition W_ord := Ffix_ord Wf Wdom.

  Lemma W_o_o : isOrd W_ord.
apply Ffix_o_o; auto.
Qed.
Hint Resolve W_o_o.

  Lemma W'_post : forall a,
   a ∈ W' ->
   a ∈ TI Wf W_ord.
apply Ffix_post; eauto.
apply Wf_stable.
Qed.

  Lemma W'_clos : W' == TI Wf W_ord.
apply incl_eq.
 red; intros; apply W'_post; trivial.

 apply Wi_W'; trivial.
Qed.

  Lemma W'_eqn : W' == Wf W'.
apply Ffix_eqn; eauto.
apply Wf_stable.
Qed.

(** * The fixpoint of the W_type operator *)

(** We get W the fixpoint of W_F by isomorphism *)

  Definition W := TI W_F W_ord.

Definition wiso f := comp_iso (WFmap f) Wsup.

Lemma W_F_Wf_iso' o f :
  isOrd o ->
  iso_fun (TI W_F o) (TI Wf o) f ->
  iso_fun (W_F (TI W_F o)) (Wf (TI Wf o)) (wiso f).
intros.
apply iso_fun_trans with (W_F (TI Wf o)).
 apply WFmap_iso; trivial.

 apply W_F_Wf_iso.
 transitivity W'; [apply Wi_W';trivial|apply W'typ].
Qed.

Instance wisom  : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) wiso.
do 3 red; intros.
unfold wiso.
apply comp_iso_morph; trivial.
 apply WFmap_morph; trivial.

 apply Wsup_morph.
Qed.

Lemma wiso_ext : forall X f f',
  eq_fun X f f' -> eq_fun (W_F X) (wiso f) (wiso f').
red; intros.
apply Wsup_morph.
apply WFmap_ext.
 apply W_F_elim with (1:=H0).

 rewrite H1; reflexivity.

 intros.
 apply H.
  apply W_F_elim with (1:=H0); trivial.

  rewrite H1; rewrite H3; reflexivity.
Qed.
Hint Resolve wiso_ext.

Lemma TI_W_F_Wf_iso o :
  isOrd o ->
  iso_fun (TI W_F o) (TI Wf o) (TI_iso W_F wiso o).
intros.
apply TI_iso_fun; intros; auto with *.
apply W_F_Wf_iso'; trivial.
Qed.

  Lemma W_eqn : W == W_F W.
cut (TI Wf W_ord == Wf (TI Wf W_ord)).
 apply <- TI_iso_fixpoint; auto with *.
  apply W_F_Wf_iso'; trivial.
assert (W' == TI Wf W_ord).
 apply incl_eq.
  red; intros; apply W'_post; trivial.
  apply Wi_W'; auto.
rewrite <- H.
apply W'_eqn.
Qed.

  Lemma W_post : forall o, isOrd o -> TI W_F o ⊆ W.
intros.
apply TI_pre_fix; auto with *.
rewrite <- W_eqn; reflexivity.
Qed.

  Lemma W_eta w : w ∈ W -> w == couple (fst w) (snd w).
intros.
rewrite W_eqn in H.
apply surj_pair with (1:=subset_elim1 _ _ _ H).
Qed.

(** Recursor on W *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Hint Resolve W_F_mono.

  Lemma Wi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i ⊆ o ->
     (forall i' m, lt i' i -> m ∈ TI W_F i' -> P m) ->
     forall n, n ∈ TI W_F i -> P n) ->
    forall n, n ∈ TI W_F o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U : set -> set -> set.
  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ TI W_F o -> x == x' ->
    U o x ⊆ U o' x'.

  Let Ty o := cc_prod (TI W_F o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty o -> F o f ∈ Ty (osucc o).

  Let Q o f := forall x, x ∈ TI W_F o -> cc_app f x ∈ U o x.

Definition fcompat2 domf domg f g :=
  forall x : set, x ∈ domf -> x ∈ domg -> cc_app f x == cc_app g x.

  Definition Wi_ord_irrel :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty o -> g ∈ Ty o' ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : Wi_ord_irrel.

  Definition WREC := REC F.

Lemma Umorph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ TI W_F o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma Uext : forall o, isOrd o -> o ⊆ ord -> ext_fun (TI W_F o) (U o).
red; red; intros.
apply Umorph; auto with *.
Qed.


  Lemma WREC_typing : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (TI W_F o) f -> Q o f -> f ∈ Ty o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply Uext; trivial.
Qed.


Let Wi_cont : forall o,
   isOrd o -> TI W_F o == sup o (fun o' => TI W_F (osucc o')).
apply TI_mono_eq; trivial.
Qed.

Let Qm :
   forall o o',
   isOrd o ->
   o ⊆ ord ->
   o == o' -> forall f f', fcompat (TI W_F o) f f' -> Q o f -> Q o' f'.
intros.
unfold Q in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply Umono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.

Let Qcont : forall o f : set,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI W_F o) f ->
 (forall o' : set, o' ∈ o -> Q (osucc o') f) -> Q o f.
intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
generalize (H2 _ H3 _ H4).
apply Umono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Qtyp : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI W_F o) f ->
 Q o f -> is_cc_fun (TI W_F (osucc o)) (F o f) /\ Q (osucc o) (F o f).
intros.
assert (F o f ∈ Ty (osucc o)).
 apply Ftyp; trivial.
 apply WREC_typing; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma Firrel_W : stage_irrelevance ord (TI W_F) Q F.
red; red; intros.
destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
apply Firrel; trivial.
 apply WREC_typing; trivial. 
 transitivity o'; trivial.

 apply WREC_typing; trivial. 
Qed.

  Lemma WREC_recursor : recursor ord (TI W_F) Q F.
split; auto.
 apply TI_morph.

 apply Firrel_W.
Qed.
Hint Resolve WREC_recursor.

  (* Main properties of WREC: typing and equation *)
  Lemma WREC_wt : WREC ord ∈ Ty ord.
intros.
apply WREC_typing; auto with *.
 apply REC_wt with (1:=oord) (2:=WREC_recursor).
 apply REC_wt with (1:=oord) (2:=WREC_recursor).
Qed.

  Lemma WREC_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x ∈ W_F (TI W_F o) ->
     (forall y, y ∈ TI W_F o -> P o y (cc_app (WREC ord) y)) ->
     forall w, isOrd w -> w ⊆ ord -> lt o w ->
     P w x (cc_app (F ord (WREC ord)) x)) ->
    x ∈ TI W_F ord ->
    P ord x (cc_app (WREC ord) x).
intros.
unfold WREC.
apply REC_ind with (2:=WREC_recursor); auto.
intros.
apply TI_elim in H4; auto with *.
destruct H4 as (o',?,?).
apply H0 with o'; eauto using isOrd_inv.
red; auto.
Qed.

  Lemma WREC_expand : forall n,
    n ∈ TI W_F ord -> cc_app (WREC ord) n == cc_app (F ord (WREC ord)) n.
intros.
apply REC_expand with (2:=WREC_recursor) (Q:=Q); auto.
Qed.

  Lemma WREC_irrel o o' :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    eq_fun (TI W_F o) (cc_app (WREC o)) (cc_app (WREC o')).
red; intros.
rewrite <- H4.
apply REC_ord_irrel with (2:=WREC_recursor); auto with *.
Qed.

End Recursor.

Section SimpleRecursor.

  Variable F : set -> set.
  Hypothesis Fm : morph1 F.
  
  Variable U : set -> set.
  Hypothesis Um : morph1 U.

  Hypothesis Ftyp : forall o f, isOrd o ->
    (forall w, w ∈ TI W_F o -> cc_app f w ∈ U w) ->
    (forall w, w ∈ TI W_F (osucc o) -> cc_app (F f) w ∈ U w).

  Hypothesis Firr : forall o f g, isOrd o ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F f) (F g).
    
  Definition W_REC := WREC (fun o fct => λ w ∈ TI W_F (osucc o), cc_app (F fct) w) W_ord.

  Lemma W_REC_eqn w :
    w ∈ W ->
    cc_app W_REC w == cc_app (F W_REC) w.
intros.
unfold W_REC.
rewrite WREC_expand with (U:=fun _ w => U w); trivial.
 rewrite cc_beta_eq; trivial.
  reflexivity.

  do 2 red; intros.
  rewrite H1; reflexivity.

  rewrite TI_mono_succ; auto with *.
  fold W.
  rewrite <- W_eqn; trivial.
  
  do 3 red; intros.
  apply cc_lam_ext.
   rewrite H0; reflexivity.

   red; intros.
   apply cc_app_morph; auto.

 intros.
 rewrite H5; reflexivity.

 intros.
 apply cc_prod_intro.
  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; auto.
  intros.
  apply Ftyp with o; trivial.
  intros.
  apply cc_prod_elim with (1:=H2); trivial.

 red; red; intros.
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq. 
  red in Firr.
  eapply Firr with o; trivial.

  do 2 red; intros.
  rewrite H9; reflexivity.

 revert H7; apply TI_mono; auto with *.
 apply osucc_mono; auto.

 do 2 red; intros.
 rewrite H9; reflexivity.
Qed.

  Lemma W_REC_typ : W_REC ∈ cc_prod W U.
apply WREC_wt with (U:=fun _ w => U w); trivial.
 do 3 red; intros.
 apply cc_lam_ext.
  rewrite H; reflexivity.

  red; intros.
  apply cc_app_morph; auto.

 intros.
 rewrite H4; reflexivity.

 intros.
 apply cc_prod_intro.
  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; auto.
  intros.
  apply Ftyp with o; trivial.
  intros.
  apply cc_prod_elim with (1:=H1); trivial.

 red; red; intros.
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq. 
  red in Firr.
  eapply Firr with o; trivial.

  do 2 red; intros.
  rewrite H8; reflexivity.

 revert H6; apply TI_mono; auto with *.
 apply osucc_mono; auto.

 do 2 red; intros.
 rewrite H8; reflexivity.
Qed.

  Lemma W_REC_unicity :
    forall f,
    f ∈ (Π w ∈ W, U w) ->
    fcompat W f (F f) ->
    f == W_REC.
    intros.
assert (forall w, w ∈ W -> cc_app f w ∈ U w).
 intros.
 apply cc_prod_elim with (1:=H); trivial.
rename H into fty.
assert (fcompat W f W_REC).
revert H1 H0; unfold W.
apply isOrd_ind with (2:=W_o_o).
intros.
red; intros.
rewrite W_REC_eqn.
red in H3.
rewrite H3; trivial.
red in Firr.
apply TI_elim in H4; auto with *.
destruct H4 as (o',o'o,H4).
assert (isOrd o').
 apply isOrd_inv with y; trivial.
rewrite <- TI_mono_succ in H4; auto with *.
assert (TI W_F o' ⊆ TI W_F y).
 apply TI_mono; auto with *.
apply Firr with (o:=o'); trivial.
apply H1; trivial.
 intros.
 apply H2; auto.

 red; intros.
 apply H3; auto.

 revert H4; apply TI_mono; auto with *.

rewrite cc_eta_eq with (1:=fty).
rewrite cc_eta_eq with (1:=W_REC_typ).
apply cc_lam_ext.
reflexivity.
red; intros.
red in H.
rewrite <- H3.
apply H.
trivial.
Qed.
    
  (*
  Lemma W_REC_ind : forall P x,
    Proper (eq_set==>eq_set==>iff) P ->
    (forall x,
     x ∈ W ->
     (forall y, y ∈ W -> P y (cc_app WREC y)) ->
     P x (cc_app (F WREC) x)) ->
    x ∈ W -> P x (cc_app WREC x).
*)
End SimpleRecursor.

Section PrimRecursor.

  Variable P : set -> set.
  Hypothesis Pm : morph1 P.
  
  Variable F : set -> set -> set -> set.
  Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.

  Hypothesis Ftyp : forall x y recy,
    x ∈ A ->
    y ∈ (Π i ∈ B x, W) ->
    recy ∈ (Π i ∈ B x, P (cc_app y i)) ->
    F x y recy ∈ P (couple x y).

  Definition WPREC : set :=
    W_REC (fun f =>
             λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i))).

  Let lam_m1 : forall f f' w w', f==f' -> w ∈ W -> w==w' ->
    F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i)) ==
    F (fst w') (snd w') (λ i ∈ B (fst w'), cc_app f' (cc_app (snd w') i)).
intros.
apply Fm.
 apply fst_morph; trivial.
 apply snd_morph; trivial.
apply cc_lam_ext.
 apply Bm.
 apply fst_morph; trivial.

 red; intros.
 rewrite H,H1,H3; reflexivity.
Qed.

  Let lam_m :
    morph1
     (fun f : set =>
      λ w ∈ W,
      F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i))).
do 2 red; intros.
apply cc_lam_ext.
 reflexivity.
red; intros.
apply lam_m1; trivial.
Qed.
  
Let lam_typ :
 forall o f : set,
 isOrd o ->
 (forall w : set, w ∈ TI W_F o -> cc_app f w ∈ P w) ->
 forall w : set,
 w ∈ TI W_F (osucc o) ->
 cc_app
   (λ w0 ∈ W,
    F (fst w0) (snd w0) (λ i ∈ B (fst w0), cc_app f (cc_app (snd w0) i))) w
   ∈ P w.
intros.
rewrite cc_beta_eq.
rewrite TI_mono_succ in H1; auto with *.
  setoid_replace (P w) with (P (couple (fst w) (snd w))).
 apply Ftyp.
  apply fst_typ_sigma in H1; trivial.

  eapply snd_typ_sigma in H1.
  3:reflexivity.
  revert H1; apply cc_prod_covariant.   
  do 2 red; reflexivity.
  reflexivity.   
  intros.
  apply W_post; trivial.
  do 2 red; intros.
  apply cc_arr_morph.
  auto.
  reflexivity.

  apply cc_prod_intro.
   do 2 red; intros.
   rewrite H3; reflexivity.
   do 2 red; intros.
   rewrite H3; reflexivity.
   intros.
   apply H0.
   eapply snd_typ_sigma in H1.
   3:reflexivity.
   apply cc_prod_elim with (1:=H1); trivial.
   do 2 red; intros.
   apply cc_arr_morph.
   auto.
   reflexivity.

 apply Pm.
 apply surj_pair with (1:=subset_elim1 _ _ _ H1).

 do 2 red; intros.
 apply lam_m1; trivial.
 reflexivity. 

 revert H1; apply W_post; auto.
Qed.

Let lam_irr :
 forall o f f',
 isOrd o ->
 fcompat (TI W_F o) f f' ->
 fcompat (TI W_F (osucc o))
   (λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i)))
   (λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f' (cc_app (snd w) i))).
red; intros.
rewrite cc_beta_eq.
rewrite cc_beta_eq.
apply Fm.
reflexivity.
reflexivity.
apply cc_lam_ext.
reflexivity.
red; intros.
rewrite <- H3.
apply H0.
rewrite TI_mono_succ in H1; auto with *.
eapply snd_typ_sigma in H1.
3:reflexivity.
apply cc_prod_elim with (1:=H1); trivial.
do 2 red; intros.
apply cc_arr_morph.
auto.
reflexivity.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity. 

revert H1; apply W_post; auto.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity. 

revert H1; apply W_post; auto.
Qed.

Lemma WPREC_typ : WPREC ∈ Π w ∈ W, P w.
intros.
unfold WPREC.
apply W_REC_typ with (U:=P); trivial.
Qed.

  Lemma WPREC_eqn x y :
    couple x y ∈ W ->
    cc_app WPREC (couple x y) == F x y (λ i ∈ B x, cc_app WPREC (cc_app y i)).
intros.
unfold WPREC.
rewrite W_REC_eqn with (U:=P); trivial.
rewrite cc_beta_eq; trivial.
apply Fm.
 apply fst_def.
 apply snd_def.

 apply cc_lam_ext.
 apply Bm.
 apply fst_def.
 red; intros.
 rewrite snd_def.
 rewrite H1.
 reflexivity.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity.
Qed.
  


End PrimRecursor.

 (** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)

Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_Wdom : Wdom ∈ U.
unfold Wdom.
apply G_rel; trivial.
apply G_List; trivial.
apply G_sup; trivial.
apply morph_is_ext; trivial.
Qed.

  Lemma G_W' : W' ∈ U.
apply G_subset; trivial.
apply G_Wdom.
Qed.

  Lemma G_W_F X : X ∈ U -> W_F X ∈ U.
intros.
unfold W_F.
apply G_sigma; intros; trivial.
apply G_cc_prod; auto.
Qed.

  Lemma G_W_ord : W_ord ∈ U.
unfold W_ord.
apply G_Ffix_ord; auto.
apply G_Wdom.
Qed.


  Lemma G_W : W ∈ U.
apply G_TI; intros; trivial.
 do 2 red; intros; apply sigma_ext; intros; auto with *.
 apply cc_prod_morph; auto with *.
 red; trivial.

 apply G_W_ord.

 apply G_W_F; trivial.
Qed.

End W_Univ.

End W_theory.

(* More on W_F: *)
(*
Lemma W_F_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; trivial.
Qed.
*)

Instance W_F_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_ext; trivial.
intros.
rewrite (H0 _ _ H3),H1; reflexivity.
Qed.

Lemma W_F_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  W_F A B X == W_F A' B' X'.
unfold W_F; intros.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; auto.
Qed.

Instance Wsup_morph_gen : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H0; reflexivity.

 apply sup_morph.
 apply H; rewrite H0; reflexivity.
 red; intros.
 apply replf_morph_raw.
 rewrite H0,H2; reflexivity.
 red; intros.
 rewrite H2,H3; reflexivity.
Qed.

Instance Wf_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) Wf.
do 4 red; intros.
unfold Wf.
apply replf_morph_raw.
 apply W_F_morph_gen; trivial.

 red; intros.
 apply Wsup_morph_gen; trivial.
Qed.

Instance Wdom_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) Wdom.
do 3 red; intros.
unfold Wdom.
apply rel_morph; trivial.
apply List_morph.
apply sup_morph; trivial.
red; intros.
auto.
Qed.


Lemma W_ord_morph_gen : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W_ord.
do 3 red; intros.
unfold W_ord.  
apply Ffix_ord_morph.
 red; intros.
 apply Wf_morph_gen; trivial.

 apply Wdom_morph; trivial.
Qed.

Lemma WREC_morph_gen : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.
do 3 red; intros.
unfold WREC.
unfold REC.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply H; auto.
Qed.

Hint Resolve wfm1.

(** A specific instance of W-type: the type of sets (cf Ens.set) *)

Section Sets.

Hypothesis U : set.
Hypothesis Ugrot : grot_univ U.

  Definition sets := W U (fun X =>X).

  Let sm : morph1 (fun X => X).
do 2 red; trivial.
Qed.

  Lemma sets_ind :
    forall P : set -> Prop,
    (forall y X f, morph1 f ->
     (* y ∈ sigma X:U. U->Ens.set *)
     y == couple X (cc_lam X f) ->
     X ∈ U ->
     (forall x, x ∈ X -> f x ∈ sets) ->
     (* induction hypothesis *)
     (forall x, x ∈ X -> P (f x)) ->
     P y) ->
    forall x, x ∈ sets -> P x.
unfold sets,W;intros.
assert (isOrd (W_ord U (fun X => X))).
 apply W_o_o; trivial.
revert x H0; elim H1 using isOrd_ind; intros.
apply TI_elim in H4; auto with *.
2:apply W_F_morph; trivial.
destruct H4 as (o',?,?).
apply W_F_elim in H5; auto with *.
destruct H5 as (?,(?,?)).
apply H with (fst x) (cc_app (snd x)); intros; trivial.
 apply cc_app_morph; reflexivity.

 generalize (H6 _ H8); apply TI_incl; auto with *.
  apply W_F_morph; trivial.

  apply H2; trivial.

 apply H3 with o'; auto.
Qed.

  Lemma sets_incl_U : sets ⊆ U.
red; intros.
apply sets_ind with (2:=H); intros.
rewrite H1; clear H1 y.
apply G_couple; trivial.
apply G_cc_lam; auto.
Qed.

End Sets.
