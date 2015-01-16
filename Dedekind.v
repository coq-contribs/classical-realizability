Require Import QArith.
Require Import Psatz.
Require Import Kbase.
Require Import Rationals.

(** **  Definition of real numbers through Dedekind cuts  **)

(** The sort of rational predicates used to interpret real numbers **)
Definition ρ := { x : Qc -> formula | forall q q' : Qc, q < q' -> x q' ⊆ x q}.
Notation "x [ q ]" := (proj1_sig x q) (at level 10).
Notation "↓ x" := (proj2_sig x _) (at level 10).

(** The operator lifting any predicate into a downward-closed one **)
Lemma F_open (x : Qc -> formula) :
  forall q q', q < q' -> (∀q'0, q'0 <= q' ↦ x q'0) ⊆ (∀q'0, q'0 <= q ↦ x q'0).
Proof.
intros ? ? Hlt. apply Forall_sub_compat. intro.
apply mapsto_sub_compat. apply Qclt_le_weak in Hlt. now transitivity q. reflexivity.
Qed.

(** The variant with an existential quantifier, ie by upper closure **)
Lemma Fbis_open (x : Qc -> formula) :
  forall q q', q < q' -> (∀Z, (∀q'', q' <= q'' ↦ x q'' → Z) → Z) ⊆ (∀Z, (∀q'', q <= q'' ↦ x q'' → Z) → Z).
Proof.
intros ? ? Hlt. apply Forall_sub_compat. intro. apply sub_Impl; [| reflexivity].
apply Forall_sub_compat. intro. apply mapsto_sub_compat; [| reflexivity].
revert Hlt. Qcunfold. lra.
Qed.

Definition F (x : Qc -> formula) : ρ := exist _ (fun q => ∀q', q' <= q ↦ x q') (F_open x).

(** Addition **)
Lemma Radd_open (x y : ρ) : forall q q', q < q' ->
  (∀Z : formula, (∀q'0, x [q'0] → y [q' - q'0] → Z) → Z)
  ⊆ (∀Z : formula, (∀q'0, x [q'0] → y [q - q'0] → Z) → Z).
Proof.
intros. apply Forall_sub_compat. intro. apply sub_Impl; [|reflexivity].
apply Forall_sub_compat. intro. repeat apply sub_Impl; try reflexivity.
apply (↓ y). revert H. Qcunfold. lra.
Qed.

Definition Radd (x y : ρ) : ρ := exist _ (fun q => ∀Z, (∀q', x[q'] → y[q - q'] → Z) → Z) (Radd_open x y).
Infix "+" := Radd.

(** Opposite **)
Definition Ropp (x : ρ) : ρ := F (fun q => ¬ x[-q]).
Notation "- x" := (Ropp x).

(** Relations **)
Definition Rle (x y : ρ) := ∀₂q,q'∈ℚ×ℚ, q' < q ↦ x[q] → y[q'].
Infix "≤" := Rle.

Definition Req x y := x ≤ y ∧ y ≤ x.
Infix "≡" := Req.

(** Example of a defined operation: the average
    
    Notice that the term is written in CPS style because of the definition of rational operations in the KAM.
**)
Definition average := λ"q₁" λ"q₂" Qq 2 @ (ℚadd @ "q₁" @ "q₂" @ ℚdiv).

Lemma average_realizer : forall e, average↓e ⊩ ∀₂q₁,q₂∈ℚ×ℚ, ℚ (Qcdiv (Qcplus q₁ q₂) 2).
Proof. Ksolve. apply Qq_realizer. find. start. apply ℚdiv_realizer. find. Qed.

(** **  Order and equivalence properties of ≤ and =  **)

Definition swap := λ"f" λ"x" λ"y" "f" @ "y" @ "x".

Definition Rle_refl := λ"_" λ"_" λ"x" "x".

Lemma Rle_refl_realizer : forall x e, Rle_refl↓e ⊩ x ≤ x.
Proof. unfold Rle. intros. start. apply (sub_term Ht (B:=x[q'])). now apply (↓x q). ok. Qed.

Definition Rle_trans := λ"x" λ"y" λ"q" λ"q'" λ"z" average @ "q" @ "q'" @
                       (λ"q''" "y" @ "q''" @ "q'" @ ("x" @ "q" @ "q''" @ "z")).

Lemma Rle_trans_realizer : forall x y z e, Rle_trans↓e ⊩ x ≤ y → y ≤ z → x ≤ z.
Proof.
unfold Rle. Ksolve. apply average_realizer. find.
Ksolve. rewrite Qclt_shift_div_l.
  replace (q' * 2%Z) with (q' + q')%Qc. now apply Qcplus_lt_le_compat.
  Qcunfold. simpl. ring. now compute.
Ksolve.
rewrite Qclt_shift_div_r.
  replace (q * 2%Z) with (q + q)%Qc. now apply Qcplus_le_lt_compat.
  Qcunfold. simpl. ring. now compute.
Qed.

Definition Rle_antisym := λ"x" λ"y" λ"f" "f" @ "x" @ "y".

Lemma Rle_antisym_realizer : forall x y e, Rle_antisym↓e ⊩ x ≤ y → y ≤ x → x ≡ y.
Proof. unfold Req. Ksolve. Qed.

Definition Req_refl := λ"f" "f" @ Rle_refl @ Rle_refl.

Lemma Req_refl_realizer : forall x e, Req_refl↓e ⊩ x ≡ x.
Proof. unfold Req. Ksolve; apply Rle_refl_realizer. Qed.

Definition Req_sym := λ"f" λ"g" "f" @ (swap @ "g").

Lemma Req_sym_realizer : forall x y e, Req_sym↓e ⊩ x ≡ y → y ≡ x.
Proof. unfold Req. repeat Ksolve. unfold swap. Ksolve. Qed.

Definition Req_trans := λ"x" λ"y" λ"f" "x" @ λ"x₁" λ"x₂" "y" @ λ"y₁" λ"y₂"
  "f" @ (Rle_trans @ "x₁" @ "y₁") @ (Rle_trans @ "y₂" @ "x₂").

Lemma Req_trans_realizer : forall x y z e, Req_trans↓e ⊩ x ≡ y → y ≡ z → x ≡ z.
Proof. unfold Req. repeat Ksolve; eapply Rle_trans_realizer; find. Qed.

(** **  Dichotomy  **)

Definition D := λ"l" λ"r" callcc @ λ"k" "l" @ λ"qx" λ"qx'" λ"x" callcc @ λ"k'" (* args in 1st branch *)
                                   "k" @ ("r" @ λ"qy" λ"qy'" λ"y" (* args in 2nd branch *)
                                   ℚle @ "qy" @ "qx'" @ "x" @ ("k'" @ "y")).
Theorem dichotomy : forall x y e, D↓e ⊩ (x ≤ y ∨ y ≤ x).
Proof.
Ksolve. unfold Rle. Ksolve. unfold Rle. Kmove.
destruct (Qclt_le_dec q' q0).
  Ksolve. apply (sub_stack Hπ0). now apply (↓y).
  Ksolve. apply (sub_stack Hπ1). apply (↓x). revert Hc Hc0 q1. Qcunfold. lra.
Qed.

(** **  Ring properties of + and -  **)

Definition plus_assoc1 := λ"_" λ"_" λ"p" λ"f" "p" @ λ"x" λ"p'" "p'" @ λ"y" λ"z"
  "f" @ (λ"g" "g" @ "x" @ "y") @ "z".
Definition plus_assoc2 := λ"_" λ"_" λ"p" λ"f" "p" @ λ"p'" λ"z" "p'" @ λ"x" λ"y"
  "f" @ "x" @ (λ"g" "g" @ "y" @ "z").

Theorem plus_comm_realizer : forall x y,
  forall e, (λ"_" λ"_" λ"x" λ"f" "x" @ (swap @ "f"))↓e ⊩ x+y ≤ y+x.
Proof.
unfold Rle, Radd, swap. do 2 Ksolve.
replace (q' - (q - q'0)) with (q'0 + (q' - q))%Qc by ring.
eapply sub_term. eassumption. apply (↓x). revert Hc. Qcunfold. lra.
Qed.

Theorem plus_assoc1_realizer : forall e, plus_assoc1↓e ⊩ ∀x y z, x + (y + z) ≤ (x + y) + z.
Proof.
unfold Rle, Radd. do 2 Ksolve. Kmove. exists (q'0 + q'1)%Qc. Ksolve.
  Ksolve. now replace (q'0 + q'1 - q'0) with q'1 by ring.
  eapply sub_term. eassumption. apply (↓z). revert Hc. Qcunfold. lra.
Qed.

Theorem plus_assoc2_realizer : forall e, plus_assoc2↓e ⊩ ∀x y z, (x + y) + z ≤ x + (y + z).
Proof.
unfold Rle, Radd. do 2 Ksolve. Ksolve. Ksolve.
replace (q' - q'1 - (q'0 - q'1)) with (q' - q'0) by ring.
  eapply sub_term. eassumption. apply (↓z). revert Hc. Qcunfold. lra.
Qed.

Theorem Ropp_involutive_trivial_realizer : forall e, (λ"_" λ"_" λ"x" λ"f" "f" @ "x")↓e ⊩ ∀x, x ≤ -(-x).
Proof.
unfold Rle. Ksolve. apply Qcopp_le_compat; eok. rewrite Qcopp_involutive.
eapply sub_term. eok. now apply (↓x).
Qed.

Theorem Ropp_involutive_realizer : forall e, λ"_" λ"_" callcc↓e ⊩ ∀x, -(- x) ≤ x.
Proof.
unfold Rle, Ropp. intro. do 2 Ksolve. apply Qclt_le_weak. eok.
apply Qcle_lt_or_eq in Hc0. destruct Hc0.
  apply Qcopp_lt_compat in H. eapply (↓x). eassumption. now rewrite Qcopp_involutive.
  apply Qc_is_canon in H. rewrite H. now rewrite Qcopp_involutive.
Qed.
