Require Import QArith_base Qcanon Orders QcOrderedType GenericMinMax.

Local Open Scope Qc_scope.

Definition Qcmax := gmax Qccompare.
Definition Qcmin := gmin Qccompare.

Module QcHasMinMax <: HasMinMax Qc_as_OT.
  Module QcMM := GenericMinMax Qc_as_OT.
  Definition max := Qcmax.
  Definition min := Qcmin.
  Definition max_l := QcMM.max_l.
  Definition max_r := QcMM.max_r.
  Definition min_l := QcMM.min_l.
  Definition min_r := QcMM.min_r.
End QcHasMinMax.

Module Qc.
  
  Include MinMaxProperties Qc_as_OT QcHasMinMax.
  
  Lemma plus_max_distr_l : forall n m p, Qcmax (p + n) (p + m) = p + Qcmax n m.
  Proof.
  intros n m p. destruct (Qclt_le_dec n m).
    repeat rewrite max_r.
      reflexivity.
      now apply Qclt_le_weak.
      apply Qcplus_le_compat. now apply Qcle_refl. now apply Qclt_le_weak.
    repeat rewrite max_l.
      reflexivity.
      assumption.
      apply Qcplus_le_compat. now apply Qcle_refl. assumption.
  Qed.
  
  Lemma plus_max_distr_r : forall n m p, Qcmax (n + p) (m + p) = Qcmax n m + p.
  Proof.
  intros n m p. destruct (Qclt_le_dec n m).
    repeat rewrite max_r.
      reflexivity.
      now apply Qclt_le_weak.
      apply Qcplus_le_compat. now apply Qclt_le_weak. now apply Qcle_refl.
    repeat rewrite max_l.
      reflexivity.
      assumption.
      apply Qcplus_le_compat. assumption. now apply Qcle_refl.
  Qed.
  
  Lemma plus_min_distr_l : forall n m p, Qcmin (p + n) (p + m) = p + Qcmin n m.
  Proof.
  intros n m p. destruct (Qclt_le_dec n m).
    repeat rewrite min_l.
      reflexivity.
      now apply Qclt_le_weak.
      apply Qcplus_le_compat. now apply Qcle_refl. now apply Qclt_le_weak.
    repeat rewrite min_r.
      reflexivity.
      assumption.
      apply Qcplus_le_compat. now apply Qcle_refl. assumption.
  Qed.
  
  Lemma plus_min_distr_r : forall n m p, Qcmin (n + p) (m + p) = Qcmin n m + p.
  Proof.
  intros n m p. destruct (Qclt_le_dec n m).
    repeat rewrite min_l.
      reflexivity.
      now apply Qclt_le_weak.
      apply Qcplus_le_compat. now apply Qclt_le_weak. now apply Qcle_refl.
    repeat rewrite min_r.
      reflexivity.
      assumption.
      apply Qcplus_le_compat. assumption. now apply Qcle_refl.
  Qed.
  
End Qc.
