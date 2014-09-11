Require Import QArith_base Qcanon Equalities Orders OrdersTac.

Local Open Scope Qc_scope.


Module Qc_as_DT <: DecidableTypeFull.
  Lemma  Qc_eq_bool_iff : forall x y, Qc_eq_bool x y = true <-> x = y.
  Proof.
  intros. split.
    apply Qc_eq_bool_correct.
    intro. unfold Qc_eq_bool. destruct (Qc_eq_dec x y). reflexivity. contradiction.
  Qed.
  
  Definition t := Qc.
  Definition eq := @eq Qc.
  Definition eq_equiv := @eq_equivalence Qc.
  Definition eqb := Qc_eq_bool.
  Definition eqb_eq := Qc_eq_bool_iff.
  
  Include BackportEq.
  Include HasEqBool2Dec.
  
End Qc_as_DT.


Module Qc_as_OT <: OrderedTypeFull.
  Lemma Qccompare_spec (x y : Qc) : CompareSpec (x=y) (x<y) (x>y) (x ?= y).
  Proof. now case_eq (x ?= y); constructor; [rewrite Qceq_alt | rewrite Qclt_alt | rewrite Qcgt_alt]. Qed.
  
  Include Qc_as_DT.
  Definition lt := Qclt.
  Definition le := Qcle.
  Definition compare := Qccompare.
  
  Instance lt_strorder : StrictOrder Qclt.
  Proof. split.
    intro. apply Qlt_irrefl.
    intros x y z. apply Qlt_trans.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) Qclt.
  Proof. intros x y Hxy z t Hzt. now rewrite Hxy, Hzt. Qed.
  
  Theorem le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
  intros x y. unfold le,lt,eq. split; intro H.
    destruct (Qcle_lt_or_eq _ _ H). now left. right. now apply Qc_is_canon.
    destruct H. now apply Qlt_le_weak. subst. now apply Qcle_refl.
  Qed.
  Definition compare_spec (x y : Qc) := Qccompare_spec x y.
  
End Qc_as_OT.
