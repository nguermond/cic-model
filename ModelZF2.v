Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFcoc.

Require Import EnsUnivWeak.

Require Import ZF2.
Require Import ZFrelations2.
Require Import ZFcoc2.


(** Set-theoretical model of the Calculus of Constructions + Universe in
    IZF + Groth Universe *)


(* We should parametrize over instance of IZFU_sig *)

Module IZF_FR_Thms := (IZF_FR_Thms_ZFcoc IZFU_Model).
Import IZF_FR_Thms.


(* ******************* *)

(* S -> (S -> S) -> S    ok *)
(* B -> (B -> S) -> B    ok *)
(* S -> (S -> B) -> B    ok *)
(* S -> (B -> S) -> S    !! *)
Definition replf (a : VV) (F : VV -> VV) : VV :=
  repl1 a (fun w => F (proj1_sig w)).
Definition S_replf (a : VV) (F : VV -> VV) : VV :=
  S_repl1 a (fun w => F (proj1_sig w)).

Lemma S_replf_type : forall a F, S_set (S_replf a F).
Proof.
  intros a F.
  apply (S_repl1_type a).
Qed.

Lemma S_set_VV_U_intro : forall x, (S_set x) -> (in_set x VV_U).
Proof.
  intros x H.
  apply int_small_VV_U_intro.
  trivial.
Qed.


Module SetsMod <: Sets.
  Definition X := set.
  Definition inX := in_set.
  Definition eqX := eq_set.
  Definition eqX_equiv := eq_set_equiv.
  Definition in_ext := in_set_morph.

  Definition inclX := incl_set.
  Definition eq_fun := eq_fun.
End SetsMod.

Module CCUModel <: CCU_Model.
  Include SetsMod.

  Definition lam := cc_lam.
  Definition app := cc_app.
  Definition prod := cc_prod.

  Definition props := props.
  Definition type0 := VV_U.

  Definition S_lam (A : set) (f : set -> set) :=
    S_replf A (fun x => S_replf (f x) (fun y => couple x y)).

  Definition S_prod (A : set) (F : set -> set) :=
    S_replf (dep_func A F) (fun f => λ x ∈ A, app f x).

  Definition lam_ext := cc_lam_ext.

  Definition app_ext: Proper (eq_set ==> eq_set ==> eq_set) app :=
    cc_app_morph.

  Definition prod_ext :
    forall x1 x2 f1 f2,
      x1 == x2 ->
      eq_fun x1 f1 f2 ->
      prod x1 f1 == prod x2 f2 :=
    cc_prod_ext.

  Definition prod_intro := cc_prod_intro.
  Lemma prod_elim : forall (dom f x : set) F,
      (eq_fun dom F F) -> (in_set f (prod dom F)) ->
      (in_set x dom) -> (in_set (app f x) (F x)).
  Proof.
    intros dom f x F H.
    apply cc_prod_elim.
  Qed.

  Definition beta_eq:
    forall A F x,
      eq_fun A F F ->
      x ∈ A ->
      app (lam A F) x == F x :=
    cc_beta_eq.

  Lemma impredicative_prod (A : X) (F : X -> X) :
    (eq_fun A F F) ->
    (forall (x : X), (in_set x A) -> (in_set (F x) props)) ->
    (in_set (prod A F) props).
  Proof. intro H.
         apply (cc_impredicative_prod A F).
  Qed.

  Lemma props_in_type0 : props ∈ type0.
  Proof.
    unfold props, IZF_FR_Thms.props.
    apply int_small_VV_U_intro.
    apply power_type.
    unfold singl.
    apply pair_type.
    unfold prf_trm.
    apply empty_type.
    apply empty_type.
  Qed.

  Lemma type_incl_props : inclX props type0.
  Proof.
    intros x H.
    apply (VV_U_trans props x).
    trivial. apply props_in_type0.
  Qed.

  Lemma S_prod_in_type0 : forall (A : X) (F : X -> X),
      (eq_fun A F F) -> (inX A type0) ->
      (forall x, (inX x A) -> (inX (F x) type0)) ->
      (inX (S_prod A F) type0).
  Proof.
    intros A F H K L.
    unfold S_prod.
    apply (S_set_VV_U_intro).
    apply S_replf_type.
  Qed.

  Lemma lift_S_lam : forall (A : X) (f : X -> X),
      (eq_fun A f f) -> (inX A type0) ->
      (forall x, (inX x A) -> (inX (f x) type0)) ->
      (eqX (S_lam A f) (lam A f)).
  Proof.
    intros A f Eq SA Sf.
    Transparent cc_lam.
    unfold S_lam, lam, cc_lam.
    unfold S_replf.
    unfold IZF_FR_Thms_ZFrelations.replf.
    unfold compose.
    unfold S_repl1.
    destruct A. simpl.
  Admitted.

  Lemma lift_S_prod : forall (A : X) (F : X -> X),
      (eq_fun A F F) -> (inX A type0) ->
      (forall x, (inX x A) -> (inX (F x) type0)) ->
      (eqX (S_prod A F) (prod A F)).
  Admitted.
End CCUModel.
