(* Ensembles hétérogènes *)


Require Import basic.
Require Import EnsUniv.

Require Import ZFdef.
Require Import Sublogic.

Inductive Hset :=
| sup (X : Type) : (X -> Hset) -> Hset
| inj : S.set -> Hset.

Definition U := sup S.set inj.

Print S.eq_set.

Definition idx (x : Hset) : Type :=
  match x with
  | sup X f => X
  | inj sx => S.idx sx
  end.

Definition elts (x : Hset) (i : idx x) : Hset.
  destruct x as [X f|sx].
  - exact (f i).
  - exact (inj (S.elts sx i)).
Defined.

Fixpoint liftS (sx : S.set) : Hset :=
  sup (S.idx sx) (fun i => (liftS (S.elts sx i))).

Fixpoint lift (x : Hset) : Hset :=
  match x with
  | sup X f => sup X (fun i => lift (f i))
  | inj sx => liftS sx
  end.

Fixpoint eq_set_int (x y : Hset) : Prop :=
  match (x,y) with
  | (sup X f, sup Y g) => (forall i : X, (exists j : Y, eq_set_int (f i) (g j))) /\
                          (forall j : Y, (exists i : X, eq_set_int (f i) (g j)))
  | (inj sx, inj sy) => (S.eq_set sx sy)
  | _ => False
  end.

Definition eq_set (x y : Hset) : Prop :=
  eq_set_int (lift x) (lift y).

Instance eq_set_int_refl : Reflexive eq_set_int.
Proof.
  induction x as [X f| sx].
  - split; intro i; exists i; apply H.
  - apply S.eq_set_refl.
Qed.

Instance eq_set_int_sym : Symmetric eq_set_int.
Proof.
  induction x as [X f | sx].
  - destruct y as [Y g | sy]; simpl. intro K.
    destruct K.
    { split.
      + intro j. destruct (H1 j) as [i E].
        exists i. apply H. apply E.
      + intro i. destruct (H0 i) as [j E].
        exists j. apply H.  apply E. }
    trivial.
  - destruct y as [Y g | sy].
    simpl. trivial.
    apply S.eq_set_sym.
Qed.

Instance eq_set_int_trans : Transitive eq_set_int.
Proof.
  induction x as [X f | sx]; destruct y as [Y g | sy];
    destruct z as [Z h | sz]; simpl.
  { intros K L. destruct K as [K0 K1]. destruct L as [L0 L1]. split.
    + intro i. destruct (K0 i) as [j E].
      destruct (L0 j) as [k F].
      exists k. apply (H i (g j)). trivial. trivial.
    + intro k. destruct (L1 k) as [j E].
      destruct (K1 j) as [i F].
      exists i. apply (H i (g j)). trivial. trivial. }
  contradiction. contradiction. contradiction.
  contradiction. contradiction. contradiction.
  apply S.eq_set_trans.
Qed.

Instance eq_set_int_equiv : Equivalence eq_set_int.
Proof.
  split.
  apply eq_set_int_refl.
  apply eq_set_int_sym.
  apply eq_set_int_trans.
Qed.

Instance eq_set_refl : Reflexive eq_set.
Proof.
  destruct x as [X f|sx]; unfold eq_set; reflexivity.
Qed.

Instance eq_set_sym : Symmetric eq_set.
Proof.
  destruct x as [X f|sx]; destruct y as [Y g|sy];
    unfold eq_set; symmetry; trivial.
Qed.

Instance eq_set_trans : Transitive eq_set.
Proof.
  destruct x as [X f|sx]; destruct y as [Y g|sy];
    destruct z as [Z h|sz]; unfold eq_set.
  - transitivity (lift (sup Y g)); trivial.
  - transitivity (lift (sup Y g)); trivial.
  - transitivity (lift (inj sy)); trivial.
  - transitivity (lift (inj sy)); trivial.
  - transitivity (lift (sup Y g)); trivial.
  - transitivity (lift (sup Y g)); trivial.
  - transitivity (lift (inj sy)); trivial.
  - transitivity (lift (inj sy)); trivial.
Qed.

Instance eq_set_equiv : Equivalence eq_set.
Proof.
  split. apply eq_set_refl. apply eq_set_sym. apply eq_set_trans.
Qed.

Definition in_set_int (x y : Hset) : Prop :=
  exists j, (eq_set_int x (elts y j)).

Definition in_set (x y : Hset) : Prop :=
  in_set_int (lift x) (lift y).

Definition empty : Hset := inj S.empty.

Definition pair (x y : Hset) : Hset :=
  match (x,y) with
  | (inj sx, inj sy) => inj (S.pair sx sy)
  | _ => sup bool (fun b => if b then x else y)
  end.

Definition union (x : Hset) : Hset :=
  match x with
  | inj sx => inj (S.union sx)
  | _ => sup {i:idx x & idx (elts x i)}
             (fun p => elts (elts x (projS1 p)) (projS2 p))
  end.

Definition subset (x : Hset) (P : Hset -> Prop) : Hset :=
  match x with
  | inj sx => inj (S.subset sx (compose P inj))
  | _ => sup {a|exists2 x', eq_set (elts x a) x' & P x'}
             (fun y => elts x (proj1_sig y))
  end.

Definition power (x : Hset) : Hset :=
  match x with
  | inj sx => inj (S.power sx)
  | _ => sup (idx x->Prop)
             (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i))
  end.

Definition infinity : Hset := inj S.infinity.

Definition replf (a : Hset) (F : Hset -> Hset) : Hset :=
  sup (idx a) (fun i => F (elts a i)).


(* Ensembles constructibles *)
(* Inductive Cset := *)
(* | cempty : Cset *)
(* | cpair : Cset -> Cset -> Cset *)
(* | cunion : Cset -> Cset *)
(* | csubset : Cset -> (Cset -> Prop) -> Cset *)
(* | cpower : Cset -> Cset. *)

(* Fixpoint Hset_ind (F : Hset -> Hset) : Prop := *)
(*   (forall x : Hset, *)
(*       (F x) = empty \/ *)
(*       (exists s t, (F x) = pair (s x) (t x) *)
