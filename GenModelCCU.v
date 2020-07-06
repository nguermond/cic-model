
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

    Parameter eq_term : term -> term -> Prop.

    Parameter const : X -> term.
    Definition prop : term := (const props).

    Definition kind : term := None.

    Parameter lift : forall (γ : nat -> lvl) n, (tset (γ n)) -> (tset (max γ)).

    Definition Ref (n : nat) : term :=
      Some (fun γ σ => existT _ (γ n) (σ n)).

    Definition get_lvl (tm : term) γ σ : lvl :=
      match tm with
      | Some t => (projT1 (t γ σ))
      | None => large
      end.

    (* den (Some tm) γ σ := (tm γ σ) *)
    Parameter den : forall (tm : term) (γ : nat -> lvl)
                           (σ : (forall n, tset (γ n))),
        (tset (max2 (max γ) (get_lvl tm γ σ))).

    (* Definition App (u v : term) : term := *)
    (*   Some (fun γ σ => *)
    (*           (let (ℓu,ℓv) := (get_lvl u γ σ, get_lvl v γ σ) in *)
    (*            existT _ (max2 (max γ) (max2 ℓu ℓv)) *)
    (*                   (app (inj ℓu (den u γ σ)) *)
    (*                        (inj ℓv (den v γ σ))))). *)

    (* S -> (S -> S) -> S    ok *)
    (* B -> (B -> S) -> B    ok *)
    (* S -> (S -> B) -> B    ok *)
    (* S -> (B -> S) -> S    !! *)

    (* Definition Abs (A M : term) : term := *)
    (*   (fun γ σ => *)
    (*      lam (inj (max γ) (den A γ σ)) *)
    (*          (fun x => *)
    (*             (let γ' := γ >> lvl(x) in *)
    (*              (inj (max γ') (den M γ' (σ >> x)))))). *)

    (* Definition Prod (A B : term) : term := *)
    (*   (fun γ σ => *)
    (*      prod (den A γ σ) *)
    (*           (fun x => den B (γ >> lvl(x)) (σ >> x))). *)

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
