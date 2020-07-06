
Require Import basic.
Require Import Models TypModels List.

(** A general model construction of a model of CC + U given an
    abstract model. *)

Module SyntaxCCU (Import M : CCU_Model) <: Syntax.
  Module T.
    Parameter sub : Type.

    Inductive lvl := small | large.

    Parameter max : (nat -> lvl) -> lvl.
    Parameter tset : lvl -> Type.

    Definition term : Type :=
      option
        (forall (γ : nat -> lvl) (σ : (forall n, (tset (γ n)))),
            (tset (max γ))).

    (* indépendant de γ? *)
    Parameter eq_term : term -> term -> Prop.

    Parameter const : X -> term.
    Definition prop : term := (const props).

    Definition kind : term := None.

    Parameter lift : forall (γ : nat -> lvl) n, (tset (γ n)) -> (tset (max γ)).

    Definition Ref (n : nat) : term :=
      Some (fun γ σ => (lift γ n (σ n))).

    (* den (Some tm) γ σ := (tm γ σ) *)
    Parameter den : forall (tm : term) (γ : nat -> lvl)
                           (σ : (forall n, tset (γ n))), (tset (max γ)).


(*    Parameter app : ??? *)
    Definition App (u v : term) : term :=
      (fun γ σ =>
         app (den u γ σ) (den v γ σ)).

    Definition Abs (A M : term) : term :=
      (fun γ σ =>
         lam (den A γ σ)
             (fun x => (den M (γ >> lvl(x)) (σ >> x)))).



    Definition Prod (A B : term) : term :=
      (fun γ σ =>
         prod (den A γ σ)
              (fun x => den B (γ >> lvl(x)) (σ >> x))).

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
