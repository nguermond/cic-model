
Require Import basic.
Require Import Models TypModels List.

(** A general model construction of a model of CC + U given an
    abstract model. *)

Module SyntaxCCU (Import M : CCU_Model) <: Syntax.
  Module T.
    Parameter sub : Type.

    Inductive lvl := small | large.

    Parameter max : (nat -> lvl) -> lvl.
    Parameter max2 : lvl -> lvl -> lvl.


    (* Option 1 *)
    Parameter lset : X -> lvl -> Prop.

    (* Option 2 *)
    Parameter tset : lvl -> Type.
    Parameter inj : forall (ℓ : lvl), (tset ℓ) -> X.


    Definition term : Type :=
      option
        (forall (γ : nat -> lvl) (σ : (forall n, (tset (γ n)))),
            {ℓ : lvl & (tset ℓ)}).

    (* ignore kind for now *)
    Definition term' : Type :=
      (forall (γ : nat -> lvl) (σ : nat -> X), lvl * X).

    Parameter term'_type : forall (tm : term') γ σ,
        (let (ℓ,x) := (tm γ σ) in (lset x ℓ)).

    Parameter eq_term : term -> term -> Prop.

    Parameter const : X -> term.
    Definition prop : term := (const props).

    Definition kind : term := None.

    Parameter lift : forall (γ : nat -> lvl) n, (tset (γ n)) -> (tset (max γ)).

    Definition Ref (n : nat) : term :=
      Some (fun γ σ => existT _ (γ n) (σ n)).

    Definition Ref' (n : nat) : term' :=
      (fun γ σ => (γ n, σ n)).

    Definition get_lvl (tm : term) γ σ : lvl :=
      match tm with
      | Some t => (projT1 (t γ σ))
      | None => large
      end.

    (* den (Some tm) γ σ := (tm γ σ) *)
    Parameter den : forall (tm : term) (γ : nat -> lvl)
                           (σ : (forall n, tset (γ n))),
        (tset (max2 (max γ) (get_lvl tm γ σ))).

    Definition App' (u v : term') : term' :=
      (fun γ σ =>
         (let (ℓu,ℓv) := (fst (u γ σ), fst (v γ σ)) in
          (max2 (max γ) (max2 ℓu ℓv),
           (app (snd (u γ σ)) (snd (v γ σ)))))).

    Parameter App'_type : forall (u v : term') γ σ ℓ ℓ',
        (lset (snd (u γ σ)) ℓ) ->
        (lset (snd (v γ σ)) ℓ') ->
        (lset (snd ((App' u v) γ σ)) (max2 ℓ ℓ')).


    (* Il faut que 'app' soit typé! *)
    (* Definition App (u v : term) : term := *)
    (*   Some (fun γ σ => *)
    (*           (let (ℓu,ℓv) := (get_lvl u γ σ, get_lvl v γ σ) in *)
    (*            existT _ (max2 (max γ) (max2 ℓu ℓv)) *)
    (*                   (app (inj ℓu (den u γ σ)) *)
    (*                        (inj ℓv (den v γ σ))))). *)

    Parameter ext : forall {TT : Type}, (nat -> TT) -> TT -> (nat -> TT).

    Definition Abs' (A M : term') : term' :=
      (fun γ σ =>
         (*  (γ,σ) : Γ ⊢ A : set_ℓA *)
         (let ℓA := fst (A γ σ) in
          (* (γ,σ) : Γ, (ℓ,x) : A ⊢ M : set_ℓM *)
          (* this looks wrong... *)
          (let ℓM := fst (M (ext γ ℓA) (ext σ props)) in
           (let lam' := (match (ℓA, ℓM) with
                         | (small,small) => S_lam
                         | (_,_) => lam
                         end) in
            (max2 ℓA ℓM, lam' (snd (A γ σ))
                              (fun x => (snd (M (ext γ ℓA) (ext σ x))))))))).

    Parameter Abs'_type : forall (A M : term') γ σ ℓ ℓ',
           (lset (snd (A γ σ)) ℓ) ->
           (forall x, (inX x (snd (A γ σ))) ->
                      (lset (snd (M (ext γ ℓ) (ext σ x))) ℓ')) ->
           (lset (snd ((Abs' A M) γ σ)) (max2 ℓ ℓ')).

    Definition Prod' (A B : term') : term' :=
      (fun γ σ =>
         (*  (γ,σ) : Γ ⊢ A : set_ℓA *)
         (let ℓA := fst (A γ σ) in
          (* (γ,σ) : Γ, (ℓ,x) : A ⊢ B : set_ℓB *)
          (* this looks wrong... *)
          (let ℓB := fst (B (ext γ ℓA) (ext σ props)) in
           (let prod' := (match (ℓA, ℓB) with
                         | (small,small) => S_prod
                         | (_,_) => prod
                         end) in
            (max2 ℓA ℓB, prod' (snd (A γ σ))
                              (fun x => (snd (B (ext γ ℓA) (ext σ x))))))))).

    Parameter Prod'_type : forall (A B : term') γ σ ℓ ℓ',
        (lset (snd (A γ σ)) ℓ) ->
        (forall x, (inX x (snd (A γ σ))) ->
                   (lset (snd (B (ext γ ℓ) (ext σ x))) ℓ')) ->
        (lset (snd ((Prod' A B) γ σ)) (max2 ℓ ℓ')).

    Parameter eq_sub : sub -> sub -> Prop.
    Parameter sub_id : sub.
    Parameter sub_comp : sub -> sub -> sub.
    Parameter sub_lift : nat -> sub -> sub.
    Parameter sub_shift : nat -> sub.
    Parameter sub_cons : term -> sub -> sub.

    Parameter Sub : term -> sub -> term.

    Parameter lift : nat -> term -> term.
    Parameter lift1 : nat -> term -> term.
    Parameter subst : term -> term -> term.
  End T.
  Import T.

  Definition env : Type := list term.

  Module J.
    Parameter typ eq_typ sub_typ : env -> term -> term -> Prop.
    Parameter typ_sub : env -> sub -> env -> Prop.
  End J.
  Import J.

End SyntaxCCU.









(* *********************************************** *)

(* Module MakeModel(M : CCU_Model) <: Judge. *)
(* Import M. *)

(* GenModel copy *)
