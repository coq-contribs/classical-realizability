(** Complement of file Qcanon **)

Require Import Qfield.
Require Import Qreduction.
Require Export Qcanon.

Hint Unfold Qcle Qcplus Qcminus Qcmult Qcdiv Qclt : qarith.


(*******************)
(** *  Relations  **)
(*******************)

Instance Neq_sym (A : Type) : Symmetric (fun x y : A => not (eq x y)).
Proof. intros x y Hneq Heq. apply Hneq. now symmetry. Qed.

Lemma Q2Qc_correct : forall q : Q, Q2Qc q == q.
Proof. intros. apply Qred_correct. Qed.

Ltac qc :=
  lazymatch goal with
    | q:Qc |- _ => destruct q; qc
    | _ => (try apply Qc_is_canon); simpl; repeat rewrite Qred_correct; easy || trivial with qarith
end.

Lemma Qceq_Qeq : forall q q' : Qc, q = q' <-> q == q'.
Proof. intros; split; intro. now subst. now apply Qc_is_canon. Qed.
(*
Theorem Qred_idempotent : forall q : Qc, Qred q = q.
Proof. intros [q Hq]. now simpl. Qed.
*)
Lemma Q2Qc_idempotent : forall q : Qc, Q2Qc q = q.
Proof. intros. qc. Qed.

Instance Q2Qc_wd : Proper (Qeq ==> eq) Q2Qc.
Proof. intros q q' Heq. qc. Qed.

Instance Qcle_PreOrder : PreOrder Qcle.
Proof. split. intros x. apply Qcle_refl. exact Qcle_trans. Qed.

Instance Qcle_PartialOrder : PartialOrder eq Qcle.
Proof.
intros x y. split; [intro Heq | intros [Hle₁ Hle₂]].
  split; rewrite Heq; reflexivity.
  now apply Qcle_antisym.
Qed.

Instance Qclt_irrefl : Irreflexive Qclt.
Proof. intro. apply Qcle_not_lt. reflexivity. Qed.


(*********************************)
(** *  Arithmetical operations  **)
(*********************************)

(** **  Addition  **)

Lemma Qcplus_lt_le_compat : forall q₁ q₂ q₃ q₄, q₁ < q₃ -> q₂ <= q₄ -> q₁ + q₂ < q₃ + q₄.
Proof. intros q₁ q₂ q₃ q₄ Hlt Hle. unfold Qcplus,Qclt. repeat rewrite Q2Qc_correct. now apply Qplus_lt_le_compat. Qed.

Lemma Qcplus_le_lt_compat : forall q₁ q₂ q₃ q₄, q₁ <= q₃ -> q₂ < q₄ -> q₁ + q₂ < q₃ + q₄.
Proof. intros q₁ q₂ q₃ q₄ Hle Hlt. setoid_rewrite Qcplus_comm. now apply Qcplus_lt_le_compat. Qed.

Lemma Qcplus_lt_compat : forall q₁ q₂ q₃ q₄, q₁ < q₃ -> q₂ < q₄ -> q₁ + q₂ < q₃ + q₄.
Proof.
intros q₁ q₂ q₃ q₄ Hlt₁ Hlt₂. unfold Qcplus,Qclt. repeat rewrite Q2Qc_correct.
apply Qplus_lt_le_compat. easy. now apply Qlt_le_weak.
Qed.

Lemma Qcplus_le_reg_r : forall q₁ q₂ q₃, q₁ + q₃ <= q₂ + q₃ -> q₁ <= q₂.
Proof. intros q₁ q₂ q₃ Hle. rewrite Qcle_minus_iff in *. ring_simplify in Hle. now ring_simplify. Qed.

Lemma Qcplus_le_reg_l : forall q₁ q₂ q₃, q₃ + q₁ <= q₃ + q₂ -> q₁ <= q₂.
Proof. intros q₁ q₂ q₃ Hle. rewrite Qcle_minus_iff in *. ring_simplify in Hle. now ring_simplify. Qed.

Lemma Qcplus_lt_reg_r : forall q₁ q₂ q₃, q₁ + q₃ < q₂ + q₃ -> q₁ < q₂.
Proof. intros q₁ q₂ q₃ Hlt. rewrite Qclt_minus_iff in *. ring_simplify in Hlt. now ring_simplify. Qed.

Lemma Qcplus_lt_reg_l : forall q₁ q₂ q₃, q₃ + q₁ < q₃ + q₂ -> q₁ < q₂.
Proof. intros q₁ q₂ q₃ Hlt. rewrite Qclt_minus_iff in *. ring_simplify in Hlt. now ring_simplify. Qed.

Lemma Qcplus_split_Qplus : forall q q' : Q, Q2Qc (q + q') = Q2Qc q + Q2Qc q'.
Proof. intros. unfold Qcplus. apply Qc_is_canon. now repeat rewrite Q2Qc_correct. Qed.

(** **  Opposite and subtraction  **)

Lemma Qcopp_lt_compat : forall q q', q < q' -> -q' < -q.
Proof. intros x y Hxy. apply Qcplus_lt_reg_l with (x + y). now ring_simplify. Qed. 

Instance Qcopp_lt_compat_instance : Proper (Qclt --> Qclt) Qcopp.
Proof. intros ? ?. now apply Qcopp_lt_compat. Qed.

Lemma Qcopp_distr_plus : forall q q', - (q + q') = -q + -q'.
Proof. intros; ring. Qed.

Lemma Qcminus_le_compat : forall q₁ q₂ q₃ q₄, q₁ <= q₃ -> q₄ <= q₂ -> q₁ - q₂ <= q₃ - q₄.
Proof.
intros q₁ q₂ q₃ q₄ Hle₁ Hle₂. unfold Qcminus,Qcopp,Qcplus,Qcle. repeat rewrite Q2Qc_correct.
apply Qplus_le_compat. easy. now apply Qopp_le_compat.
Qed.

Lemma Qcle_shift_minus_l : forall q₁ q₂ q₃, q₁ + q₃ <= q₂ -> q₁ <= q₂ - q₃.
Proof. intros q₁ q₂ q₃ Hle. replace q₁ with (q₁ + q₃ - q₃) by ring. apply Qcminus_le_compat. easy. reflexivity. Qed.
(*/!\ bug : easy should be stronger that reflexivity and thus succeed. *)

(** **  Multiplication  **)

Lemma Qcmult_0_l : forall q, 0 * q = 0.
Proof. intro. qc. Qed.

Lemma Qcmult_0_r : forall q, q * 0 = 0.
Proof. intro. rewrite Qcmult_comm. qc. Qed.

Lemma Qcmult_le_compat_l : forall q₁ q₂ q₃ : Qc, q₁ <= q₂ -> 0 <= q₃ -> q₃ * q₁ <= q₃ * q₂.
Proof. intros. setoid_rewrite Qcmult_comm. now apply Qcmult_le_compat_r. Qed.

Lemma Qcmult_lt_compat_l : forall q₁ q₂ q₃ : Qc, q₁ < q₂ -> 0 < q₃ -> q₃ * q₁ < q₃ * q₂.
Proof. intros. setoid_rewrite Qcmult_comm. now apply Qcmult_lt_compat_r. Qed.

Lemma Qcmult_le_compat : forall q₁ q₂ q₃ q₄, 0 <= q₁ -> 0 <= q₃ -> q₁ <= q₂ -> q₃ <= q₄ -> q₁ * q₃ <= q₂ * q₄. 
Proof.
intros q₁ q₂ q₃ q₄ Hpos Hpos' Hle Hle'. etransitivity.
  apply Qcmult_le_compat_l; eassumption.
  apply Qcmult_le_compat_r. assumption. etransitivity; eassumption.
Qed.

Lemma Qcmult_resp_nonneg : forall q q', 0 <= q -> 0 <= q' -> 0 <= q * q'.
Proof.
intros q q' Hq Hq'. apply Qcle_trans with (0 * q').
  now unfold Qcle,Q2Qc,Qred.
  now apply Qcmult_le_compat_r.
Qed.

Lemma Qcmult_lt_l : forall q₁ q₂ q₃, 0 < q₃ -> (q₃ * q₁ < q₃ * q₂ <-> q₁ < q₂).
Proof. intros q q₂ q₃. unfold Qclt,Qcmult,Qred. repeat rewrite Q2Qc_correct. apply Qmult_lt_l. Qed.

Lemma Qcmult_lt_r : forall q₁ q₂ q₃, 0 < q₃ -> (q₁ * q₃ < q₂ * q₃ <-> q₁ < q₂).
Proof. intros q₁ q₂ q₃. unfold Qclt,Qcmult,Qred. repeat rewrite Q2Qc_correct. apply Qmult_lt_r. Qed.

Lemma Qcmult_split_Qmult : forall q q' : Q, Q2Qc (q * q') = Q2Qc q * Q2Qc q'.
Proof. intros. apply Qc_is_canon. unfold Qcmult. now repeat rewrite Q2Qc_correct. Qed.

Lemma Qcmult_lt_compat : forall q₁ q₂ q₃ q₄, 0 < q₁ -> 0 < q₃ -> q₁ < q₂ -> q₃ < q₄ -> q₁ * q₃ < q₂ * q₄. 
Proof.
intros q₁ q₂ q₃ q₄ Hpos Hpos' Hlt Hlt'. apply Qclt_trans with (q₁ * q₄).
  rewrite Qcmult_lt_l; eassumption.
  rewrite Qcmult_lt_r. assumption. apply Qclt_trans with q₃; eassumption.
Qed. 

Lemma Qcsquare_nonneg : forall q, 0 <= q * q.
Proof. intros [[[] q₂] ?]; unfold Qcle,Qcmult; do 2 rewrite Q2Qc_correct; simpl; now compute. Qed.

Lemma Qcsquare_pos : forall q, q <> 0 -> 0 < q * q.
Proof.
intros q Hq. destruct (Qcle_lt_or_eq _ _ (Qcsquare_nonneg q)) as [| Heq].
  assumption.
  symmetry in Heq. apply Qcmult_integral in Heq. destruct Heq; contradiction.
Qed.

(** **  Inverse and division  **)

Lemma Qcinv_involutive : forall q, //q = q.
Proof. intro. unfold Qcinv. qc. apply Qinv_involutive. Qed.

Lemma Qcinv_opp_comm : forall q, / -q = - /q.
Proof. 
intros q. unfold Qcinv,Qcopp. apply Qc_is_canon. repeat rewrite Q2Qc_correct.
destruct q as [[[][]]]; red; reflexivity.
Qed.

Lemma Qcinv_pos : forall q, 0 < /q <-> 0 < q.
Proof.
intro q. split; intro Hle.
  rewrite <- Qcinv_involutive. rewrite <- Qcmult_lt_r; try eassumption. rewrite Qcmult_0_l.
  rewrite Qcmult_inv_l. now compute. symmetry. now apply Qclt_not_eq.
  rewrite <- Qcmult_lt_r; try eassumption. rewrite Qcmult_0_l.
  rewrite Qcmult_inv_l. now compute. symmetry. now apply Qclt_not_eq.
Qed.

Lemma Qcinv_nonneg : forall q, 0 <= / q <-> 0 <= q.
Proof.
intro q. unfold Qcle,Qcinv. do 2 rewrite Q2Qc_correct. split.
  intro. setoid_rewrite <- Qinv_involutive at 2. now apply Qinv_le_0_compat.
  now apply Qinv_le_0_compat.
Qed.

Lemma Qcinv_neg : forall q, /q < 0 <-> q < 0.
Proof.
intro q; split; intro Hlt; apply Qcopp_lt_compat in Hlt; setoid_rewrite <- Qcopp_involutive at 1 2;
apply Qcopp_lt_compat; replace (- 0) with 0 in * by ring; now rewrite <- Qcinv_opp_comm, Qcinv_pos in *.
Qed.

Lemma Qcinv_nonpos : forall q, / q <= 0 <-> q <= 0.
Proof.
intro q. split; intro Hq; apply Qcopp_le_compat in Hq; setoid_rewrite <- Qcopp_involutive at 1 2;
apply Qcopp_le_compat; replace (- 0) with 0 in * by ring.
now rewrite <- Qcinv_nonneg,Qcinv_opp_comm. now rewrite <- Qcinv_opp_comm,Qcinv_nonneg. 
Qed.

Lemma Qclt_shift_div_l : forall q q' q'', 0 < q'' -> (q < q' / q'' <-> q * q'' < q').
Proof.
intros q q' q'' Hq''. unfold Qclt,Qcdiv,Qcmult,Qcinv in *. repeat rewrite Q2Qc_correct in *.
change (q < q' * / q'')%Q with (q < q' / q'')%Q. split.
  intro. rewrite <- (Qmult_div_r q' q''). setoid_rewrite Qmult_comm at 2.
  now apply Qmult_lt_compat_r. intro Goal. symmetry in Goal. revert Goal. now apply Qlt_not_eq.
  now apply Qlt_shift_div_l.
Qed.

Lemma Qclt_shift_div_r : forall q q' q'', 0 < q' -> (q / q' < q'' <-> q < q'' * q').
Proof.
intros q q' q'' Hq'. unfold Qclt,Qcdiv,Qcmult,Qcinv in *. repeat rewrite Q2Qc_correct in *.
change (q * / q' < q'')%Q with (q / q' < q'')%Q. split.
  intro. rewrite <- (Qmult_div_r q q'). rewrite Qmult_comm.
  now apply Qmult_lt_compat_r. intro Goal. symmetry in Goal. revert Goal. now apply Qlt_not_eq.
  now apply Qlt_shift_div_r.
Qed.

Lemma Qcle_shift_div_l : forall q q' q'', 0 < q'' -> (q <= q' / q'' <-> q * q'' <= q').
Proof.
intros q q' q'' Hq''. unfold Qcle,Qcdiv,Qcmult,Qcinv in *. repeat rewrite Q2Qc_correct in *.
change (q <= q' * / q'')%Q with (q <= q' / q'')%Q. split.
  intro. rewrite <- (Qmult_div_r q' q''). setoid_rewrite Qmult_comm at 2. apply Qlt_le_weak in Hq''.
  now apply Qmult_le_compat_r. intro Goal. symmetry in Goal. revert Goal. now apply Qlt_not_eq.
  now apply Qle_shift_div_l.
Qed.

Lemma Qcle_shift_div_r : forall q q' q'', 0 < q' -> (q / q' <= q'' <-> q <= q'' * q').
Proof.
intros q q' q'' Hq'. unfold Qcle,Qcdiv,Qcmult,Qcinv in *. repeat rewrite Q2Qc_correct in *.
change (q * / q' <= q'')%Q with (q / q' <= q'')%Q. split.
  intro. rewrite <- (Qmult_div_r q q'). rewrite Qmult_comm. apply Qlt_le_weak in Hq'.
  now apply Qmult_le_compat_r. intro Goal. symmetry in Goal. revert Goal. now apply Qlt_not_eq.
  now apply Qle_shift_div_r.
Qed.

Lemma Qcdiv_resp_pos : forall p q, 0 < p -> 0 < q -> 0 < p / q.
Proof. intros p q Hp Hq. now apply Qclt_shift_div_l; try rewrite Qcmult_0_l. Qed.

Lemma Qcinv_pos_le_compat : forall q q', 0 < q -> q <= q' -> / q' <= / q.
Proof.
intros q q' Hpos Hlt. rewrite <- Qcmult_1_l. change (1 * / q) with (1 / q). rewrite Qcle_shift_div_l.
rewrite Qcmult_comm. change (q * / q') with (q / q'). rewrite Qcle_shift_div_r. now rewrite Qcmult_1_l.
now apply Qclt_le_trans with q. assumption.
Qed.

Lemma Qcinv_le_1 : forall q, 0 < q -> (/ q <= 1 <-> 1 <= q).
Proof.
intros q Hq. rewrite <- (Qcmult_1_l (/ q)). setoid_rewrite <- (Qcmult_1_l q) at 2.
change (1 * / q) with (1 / q). now apply Qcle_shift_div_r. 
Qed.

Lemma Qcinv_ge_1 : forall q, 0 < q -> (1 <= /q <-> q <= 1).
Proof.
intros q Hq. rewrite <- (Qcmult_1_l (/ q)). setoid_rewrite <- (Qcmult_1_l q) at 2.
change (1 * / q) with (1 / q). now apply Qcle_shift_div_l.
Qed.


(*************************)
(** *  Stuff for Reals  **)
(*************************)

Lemma Qred_1_r : forall n, Qred (n#1) = n#1.
Proof.
intro n. unfold Qred. cut (Z.ggcd n 1 = (1, (n, 1)))%Z. intro H. now rewrite H.
pose (Hggcd := Z.ggcd_correct_divisors n 1). clearbody Hggcd.
assert (fst (Z.ggcd n 1) = 1%Z) as Hgcd. rewrite Z.ggcd_gcd. now apply Z.gcd_1_r. 
destruct (Z.ggcd n 1) as [d [a b]]. simpl in *. subst. f_equal.
do 2 rewrite Zmult_1_l in Hggcd. now destruct Hggcd; subst.
Qed.

Coercion Z.of_nat : nat >-> Z.
Definition embed_ℤ_ℚ (n : Z) := {| this := n#1; canon := Qred_1_r n |}.
Coercion embed_ℤ_ℚ : Z >-> Qc.


(************************************)
(** *  Lemmas on rational numbers  **)
(************************************)

Ltac Qcunfold :=
  unfold Qcle,Qclt,Qcdiv,Qcminus,Qcinv,Qcopp,Qcmult,Qcplus;
  try apply Qc_is_canon; repeat rewrite Q2Qc_correct.

Lemma half_pos : forall q, 0 < q -> 0 < q / 2.
Proof. intros. apply Qclt_shift_div_l. now compute. now rewrite Qcmult_0_l. Qed.

Lemma third_pos : forall q, 0 < q -> 0 < q / 3.
Proof. intros. apply Qclt_shift_div_l. now compute. now rewrite Qcmult_0_l. Qed.

Lemma quarter_pos : forall q, 0 < q -> 0 < q / 4.
Proof. intros. apply Qclt_shift_div_l. now compute. now rewrite Qcmult_0_l. Qed.

Lemma fifth_pos : forall q, 0 < q -> 0 < q / 5.
Proof. intros. apply Qclt_shift_div_l. now compute. now rewrite Qcmult_0_l. Qed.

Lemma half_nneg : forall q, 0 <= q -> 0 <= q / 2.
Proof.
intros q H. apply Qcmult_lt_0_le_reg_r with 2. now compute.
rewrite Qcmult_0_l. unfold Qcdiv. rewrite <- Qcmult_assoc. rewrite Qcmult_inv_l. now rewrite Qcmult_1_r. now compute.
Qed.

Lemma eq_half : forall q, q = q / (1+1) + q / (1+1).
Proof. intro. Qcunfold. field. Qed.
