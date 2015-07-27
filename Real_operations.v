Require Import QArith.
Require Import Psatz.
Require Import ClassicalRealizability.Kbase.
Require Import ClassicalRealizability.Rationals.
Require Import ClassicalRealizability.Real_definitions.
Require Import ClassicalRealizability.Real_relations.


(*********************************)
(** *  Arithmetical operations  **)
(*********************************)

(** Definitions are given in the file [Real_defintions.v].  **)

(** **  Stability of relativisations  **)

(** ***  Addition  **)

Definition addℝ_Total := λ"Tx" λ"Ty" λ"ε" λ"f"
  Qq 2 @ (ℚdiv @ "ε") @ λ"ε/2" (* shared computation *)
  "Tx" @ "ε/2" @ (λ"qx" λ"X"
  "Ty" @ "ε/2" @ (λ"qy" λ"Y"
  ℚadd @ "qx" @ "qy" @ "f" @ (λ"g"
  "g" @ "ε/2" @ "ε/2" @ "qx" @ "qy" @ "X" @ "Y"))).

Theorem addℝ_Total_realizer : forall e, addℝ_Total↓e ⊩ ∀x, ∀y, Total x → Total y → Total (x + y).
Proof.
unfold Total. intro e. start.
apply Qq_realizer. exists (ℚ (ε/2)). find. start. apply ℚdiv_realizer. find.
assert (0 < ε / 2) by now apply half_pos.
do 3 Ksolve.
unfold addℝ. Ksolve. now apply eq_half.
Qed.

Definition addℝ_proper := λ"eqx" λ"eqy" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"XY₁" λ"XY₂"
  "XY₁" @ (λ"ε₁₁" λ"ε₁₂" λ"q₁₁" λ"q₁₂" λ"X₁" λ"Y₁"
  "XY₂" @ (λ"ε₂₁" λ"ε₂₂" λ"q₂₁" λ"q₂₂" λ"X₂" λ"Y₂"
  ("eqx" @ "ε₁₁" @ "ε₂₁" @ "q₁₁" @ "q₂₁" @ "X₁" @ "X₂") @
  ("eqy" @ "ε₁₂" @ "ε₂₂" @ "q₁₂" @ "q₂₂" @ "Y₁" @ "Y₂"))).

Theorem addℝ_proper_realizer : forall e, addℝ_proper↓e ⊩ ∀x₁ x₂ y₁ y₂, (x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ + y₁ ≡ x₂ + y₂)%Re.
Proof.
do 2 Ksolve. startn 7.
(* Guard conditions *)
eapply prop_guard. Kmove. exists ε₁0, ε₁1. Ksolve; now apply Qclt_le_weak. intro Hle₁.
Kmove. repeat eexists; try eok || now apply Qclt_le_weak. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. subst. intro Hle₂.
replace (q₁0 + q₂0 - (q₁1 + q₂1)) with (q₁0 - q₁1 + (q₂0 - q₂1)) by ring.
replace (ε₁0 + ε₂0 + (ε₁1 + ε₂1)) with (ε₁0 + ε₁1 + (ε₂0 + ε₂1)) by ring.
etransitivity. apply Qcabs_triangle. now apply Qcplus_le_compat.
Qed.

Definition addℝ_Cauchy := addℝ_proper.

Theorem addℝ_Cauchy_realizer : forall e, addℝ_Cauchy↓e ⊩ ∀x y, Cauchy x → Cauchy y → Cauchy (x + y)%Re.
Proof. intro e. startn 0. apply addℝ_proper_realizer. unfold Cauchy in *. do 4 eexists. split. eok. split; eok. Qed.

Definition addℝ_Rle_compat := addℝ_proper.

Theorem addℝ_Rle_compat_realizer :
  forall e, addℝ_Rle_compat↓e ⊩ ∀ x₁ x₂ y₁ y₂, (x₁ <= x₂ → y₁ <= y₂ → x₁ + y₁ <= x₂ + y₂)%Re.
Proof.
do 2 Ksolve. startn 7.
(* Guard conditions *)
eapply prop_guard. Kmove. exists ε₁0, ε₁1. Ksolve; now apply Qclt_le_weak. intro Hle₁.
Kmove. repeat eexists; try eok || now apply Qclt_le_weak. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. revert Hle₁. subst. Qcunfold. lra.
Qed.

Definition addℝ_shift := λ"P" λ"f"
  "P" @ (λ"εx" λ"ε" λ"qx" λ"q" λ"X" λ"YZ" "YZ" @ (λ"εy" λ"εz" λ"qy" λ"qz" λ"Y" λ"Z"
  ℚadd @ "qx" @ "qy" @ (ℚadd @ "εx" @ "εy" @ "f" @ "εz") @ "qz"
       @ (λ"h" "h" @ "εx" @ "εy" @ "qx" @ "qy" @ "X" @ "Y")
       @ "Z")).

Lemma addℝ_shift_realizer : forall e, addℝ_shift↓e ⊩ ∀x y z ε q, ((x + (y + z)) ε q → ((x + y) + z) ε q)%Re.
Proof.
unfold addℝ. Kmove. exists Z. split; [| ok]. Ksolve. Kmove. exists (ε₁ + ε₁0). find.
  rewrite <- Qcplus_0_l at 1. now apply Qcplus_lt_compat.
  subst. ring.
  subst. ring.
  Kmove. exists ε₁, ε₁0. find.
Qed.

Definition addℝ_assoc := λ"Cx" λ"Cy" λ"Cz" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X+(Y+Z)" λ"(X+Y)+Z"
  addℝ_Cauchy @ (addℝ_Cauchy @ "Cx" @ "Cy") @ "Cz"
              @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ (addℝ_shift @ "X+(Y+Z)") @ "(X+Y)+Z".

Theorem addℝ_assoc_realizer :
  forall e, addℝ_assoc↓e ⊩ ∀x y z, Cauchy x → Cauchy y → Cauchy z → (x + (y + z) ≡ (x + y) + z)%Re.
Proof.
intro e. startn 17. apply addℝ_Cauchy_realizer. do 2 eexists.
repeat split. startn 2. apply addℝ_Cauchy_realizer. find. eok.
exists ε₁, ε₂. find.
startn 1. apply addℝ_shift_realizer. exists x, y, z, ε₁, q₁. split; assumption.
Qed.

Definition addℝ_0_l := λ"Cx" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X+0" λ"X"
  "X+0" @ (λ"εx" λ"ε₀" λ"qx" λ"q₀" λ"X+" λ"0+"
  "0+" @ "Cx" @ "εx" @ "ε₂" @ "qx" @ "q₂" @ "X+" @ "X").

Theorem addℝ_0_l_realizer : forall e, addℝ_0_l↓e ⊩ ∀x, Cauchy x → (x + 0 ≡ x)%Re.
Proof.
Ksolve. start.
(* Guard conditions *)
apply (prop_guard Ht3). intros [_ ?].
(* Real proof *)
Kmove. exists ε₁0. find. now apply Qclt_le_weak. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. subst. intro Hle. rewrite Qcplus_0_r. etransitivity. eassumption. revert Hc2. Qcunfold. lra.
Qed.

Definition addℝ_switch := λ"XY" "XY" @ λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  λ"f" "f" @ "ε₂" @ "ε₁" @ "q₂" @ "q₁" @ "Y" @ "X".

Lemma addℝ_switch_realizer : forall e, addℝ_switch↓e ⊩ ∀x y ε q, (x + y)%Re ε q → (y + x)%Re ε q.
Proof. unfold addℝ at 1. Ksolve. unfold addℝ. Kmove. exists ε₂, ε₁. find; now rewrite Qcplus_comm. Qed.

Definition addℝ_Eeq_comm := λ"ε" λ"q" λ"f" "f" @ addℝ_switch @ addℝ_switch.

Theorem addℝ_Eeq_comm_realizer : forall e, addℝ_Eeq_comm↓e ⊩ ∀x y, (x + y ≡≡ y + x)%Re.
Proof. Ksolve; startn 0; apply addℝ_switch_realizer; find. Qed.

Definition addℝ_Req_comm := λ"Cx" λ"Cy" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X+Y" λ"Y+X"
  addℝ_Cauchy @ "Cx" @ "Cy" @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ "X+Y" @ (addℝ_switch @ "Y+X").

Theorem addℝ_Req_comm_realizer : forall e, addℝ_Req_comm↓e ⊩ ∀x y, Cauchy x → Cauchy y → (x + y ≡ y + x)%Re.
Proof.
intro e. startn 16. apply addℝ_Cauchy_realizer. exists x, y. repeat split; try ok.
exists ε₁, ε₂, q₁, q₂. find. startn 1. apply addℝ_switch_realizer. find.
Qed.

Definition addℝ_resp_Rlt := λ"Tz" λ"Lt" "Lt" @ λ"ε₁" λ"ε" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  Qq 3 @ (ℚdiv @ "ε") @ λ"ε/3" (* shared computation *)
  "Tz" @ "ε/3" @ λ"q₃" λ"Z"
  λ"f" ℚadd @ "q₂" @ "q₃" @ (ℚadd @ "q₁" @ "q₃" @ (ℚadd @ "ε₂" @ "ε/3" @ (ℚadd @ "ε₁" @ "ε/3" @ "f" @ "ε/3")))
  @ (λ"h" "h" @ "ε₁" @ "ε/3" @ "q₁" @ "q₃" @ "X" @ "Z")
  @ (λ"h" "h" @ "ε₂" @ "ε/3" @ "q₂" @ "q₃" @ "Y" @ "Z").

Theorem addℝ_resp_Rlt_realizer : forall e, addℝ_resp_Rlt↓e ⊩ ∀x y z, Total z → (x << y → x + z << y + z)%Re.
Proof.
intro. unfold Rlt at 1. Opaque Rlt. Ksolve.
Ksolve. apply Qq_realizer. find. start. apply ℚdiv_realizer. find. find.
assert (0 < ε/3) by now apply third_pos.
start. apply Ht. find. Transparent Rlt.
Kmove. exists (ε₁ + ε / 3), (ε / 3), (ε₂ + ε / 3). find.
  change 0 with (0 + 0). apply Qcplus_lt_compat; ok.
  change 0 with (0 + 0). apply Qcplus_lt_compat; ok.
  replace (q₁ + q + (ε₁ + ε / 3) + ε / 3 + (ε₂ + ε / 3)) with (q₁ + ε₁ + ε + ε₂ + q) by (Qcunfold; qc; field).
    now apply Qcplus_le_compat.
  unfold addℝ. Kmove. exists ε₁, (ε / 3%Z). find.
  unfold addℝ. Kmove. exists ε₂, (ε / 3%Z). find.
Qed.

(** ***  Opposite **)

Definition oppℝ_Total := λ"Tx" λ"ε" "Tx" @ "ε" @ (λ"q" λ"X" λ"f" ℚopp @ "q" @ "f" @ "X").

Theorem oppℝ_Total_realizer : forall e, oppℝ_Total↓e ⊩ ∀x, Total x → Total (- x).
Proof. unfold Total,oppℝ. Kmove. findn 3. eexists (_ → Z). find. Ksolve. now rewrite Qcopp_involutive. Qed.

Definition oppℝ_Req_proper := λ"eq" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  ℚopp @ "q₂" @ (ℚopp @ "q₁" @ ("eq" @ "ε₁" @ "ε₂")) @ "X" @ "Y".

Theorem oppℝ_Req_proper_realizer : forall e, oppℝ_Req_proper↓e ⊩ ∀x y, (x ≡ y → -x ≡ -y)%Re.
Proof.
unfold oppℝ. Kmove. exists ε₁. find.
replace (- q₁ - - q₂) with (-(q₁ - q₂)) by ring.
now rewrite Qcabs_opp.
Qed.

Definition oppℝ_Cauchy := oppℝ_Req_proper.

Theorem oppℝ_Cauchy_realizer : forall e, oppℝ_Cauchy↓e ⊩ ∀x, Cauchy x → Cauchy (- x).
Proof. intro e. startn 0. apply oppℝ_Req_proper_realizer. do 2 exists x. Ksolve. Qed.

Definition oppℝ_Eeq_proper := λ"eq" λ"ε" λ"q" ℚopp @ "q" @ ("eq" @ "ε").

Theorem oppℝ_Eeq_proper_realizer : forall e, oppℝ_Eeq_proper↓e ⊩ ∀x y, (x ≡≡ y → -x ≡≡ -y)%Re.
Proof. unfold Eeq. Ksolve. Qed.

Definition oppℝ_Eeq_involutive := Eeq_refl.

Theorem oppℝ_Eeq_involutive_realizer : forall e, oppℝ_Eeq_involutive↓e ⊩ ∀x, (--x ≡≡ x)%Re.
Proof. unfold Eeq, oppℝ. Ksolve; rewrite Qcopp_involutive; Ksolve. Qed.

Definition oppℝ_Req_involutive :=
  λ"Cx" Eeq_implies_Req @ (oppℝ_Cauchy @ (oppℝ_Cauchy @ "Cx")) @ oppℝ_Eeq_involutive.

Opaque Req oppℝ_Cauchy oppℝ_Eeq_involutive Eeq_implies_Req.
Corollary oppℝ_Req_involutive_realizer : forall e, oppℝ_Req_involutive↓e ⊩ ∀x, Cauchy x → (- - x ≡ x)%Re.
Proof.
intro e. start. apply Eeq_implies_Req_realizer. find.
  now do 2 (start; apply oppℝ_Cauchy_realizer; find).
start. apply oppℝ_Eeq_involutive_realizer. find.
Qed.

Transparent Req.
Definition oppℝ_addℝ := λ"Cx" λ"ε" λ"ε₀" λ"q" λ"q₀" λ"X+(-X)" λ"0"
  "0" @ "X+(-X)" @ (λ"ε₁" λ"ε₂" λ"q₁" λ"q₂"
  ℚopp @ "q₂" @ ("Cx" @ "ε₁" @ "ε₂" @ "q₁")).

Theorem oppℝ_addℝ_realizer : forall e, oppℝ_addℝ↓e ⊩ ∀x, Cauchy x → (x + (- x) ≡ embed_ℚ_ℝ 0)%Re.
Proof.
intro e. start.
(* Guard conditions *)
apply (prop_guard Ht1). intros [_ ?]. subst.
(* Decompose q₀ ∈ x+(-x)[ε₀] *)
apply Ht0. eexists; split; [| eok].
(* using Cauchy property of x *)
Kmove. exists ε₁0, ε₂0. Ksolve; try now apply Qclt_le_weak. subst. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. intro Hle. rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat.
  now replace (q₁0 + q₂ - 0) with (q₁0 - - q₂) by ring.
  ok.
Qed.

(** ***  Multiplication  **)

(** [mulℝ_Total] and [mulℝ_Total_realizer] are missing. **)

Definition mulℝ_proper := λ"eqx" λ"eqy" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"XY₁" λ"XY₂"
  "XY₁" @ λ"ε'₁" λ"ε''₁" λ"q'₁" λ"q''₁" λ"X₁" λ"Y₁"
  "XY₂" @ λ"ε'₂" λ"ε''₂" λ"q'₂" λ"q''₂" λ"X₂" λ"Y₂"
  ("eqx" @ "ε'₁" @ "ε'₂" @ "q'₁" @ "q'₂" @ "X₁" @ "X₂") @
  ("eqy" @ "ε''₁" @ "ε''₂" @ "q''₁" @ "q''₂" @ "Y₁" @ "Y₂").

Theorem mulℝ_proper_realizer : forall e, mulℝ_proper↓e ⊩ ∀x₁ x₂ y₁ y₂, (x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ * y₁ ≡ x₂ * y₂)%Re.
Proof.
do 2 Ksolve. startn 7.
(* Guard conditions *)
(* Using the equality premises as guard conditions *)
eapply prop_guard. Kmove. exists ε₁0, ε₁1. Ksolve; now apply Qclt_le_weak. intro Hlex.
Kmove. exists ε₂0, ε₂1, q₂0, q₂1; find; (now apply Qclt_le_weak) || apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. subst. intro Hley.
destruct (Qclt_le_dec ε₁0 ε₁1); destruct (Qclt_le_dec ε₂0 ε₂1).
+ replace (q₁0 * q₂0 - q₁1 * q₂1) with (q₁0 * (q₂0 - q₂1) + (q₁0 - q₁1) * q₂1) by ring.
  transitivity (0 + ε₂).
  - rewrite Qcplus_0_l. etransitivity. now apply Qcabs_triangle. etransitivity; [| eok].
    do 2 rewrite Qcabs_mult. apply Qcplus_le_compat.
    * apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite Qcle_minus_iff. replace (|q₁1| + (ε₁1 + ε₁1) + - |q₁0|) with (ε₁1 + ε₁1 + - (|q₁0| - |q₁1|)) by ring.
        rewrite <- Qcle_minus_iff. etransitivity. apply Qcabs_triangle_reverse.
        etransitivity. eok. apply Qcplus_le_compat. now apply Qclt_le_weak. reflexivity.
        etransitivity. eok. apply Qcplus_le_compat. now apply Qclt_le_weak. reflexivity.
    * rewrite Qcmult_comm. apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc6. Qcunfold. lra.
        etransitivity. eok. apply Qcplus_le_compat. now apply Qclt_le_weak. reflexivity.
  - apply Qcplus_le_compat; ok || reflexivity.
+ replace (q₁0 * q₂0 - q₁1 * q₂1) with (q₁0 * (q₂0 - q₂1) + (q₁0 - q₁1) * q₂1) by ring.
  etransitivity. apply Qcabs_triangle. do 2 rewrite Qcabs_mult. apply Qcplus_le_compat.
  - etransitivity; [| eok]. rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat.
    * apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc1. Qcunfold. lra.
        etransitivity. eok. apply Qcplus_le_compat. reflexivity. assumption.
    * apply Qcmult_resp_nonneg.
        change 0 with (0 + 0). apply Qcplus_le_compat. now apply Qcabs_nonneg. revert Hc2. Qcunfold. lra.
        revert Hc1. Qcunfold. lra.
  - etransitivity; [| eok]. rewrite <- Qcplus_0_l at 1. apply Qcplus_le_compat.
    * apply Qcmult_resp_nonneg.
        change 0 with (0 + 0). apply Qcplus_le_compat. now apply Qcabs_nonneg. revert Hc5. Qcunfold. lra.
        revert Hc6. Qcunfold. lra.
    * rewrite Qcmult_comm. apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc6. Qcunfold. lra.
        etransitivity. eok. apply Qcplus_le_compat. now apply Qclt_le_weak. reflexivity.
+ rewrite Qcabs_minus. replace (q₁1 * q₂1 - q₁0 * q₂0) with (q₁1 * (q₂1 - q₂0) + (q₁1 - q₁0) * q₂0) by ring.
  etransitivity. apply Qcabs_triangle. do 2 rewrite Qcabs_mult. rewrite Qcplus_comm. apply Qcplus_le_compat.
  - etransitivity; [| eok]. rewrite <- Qcplus_0_l at 1. apply Qcplus_le_compat.
    * apply Qcmult_resp_nonneg.
        change 0 with (0 + 0). apply Qcplus_le_compat. now apply Qcabs_nonneg. revert Hc1. Qcunfold. lra.
        revert Hc2. Qcunfold. lra.
    * rewrite Qcmult_comm. apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc2. Qcunfold. lra.
        etransitivity. rewrite Qcabs_minus. eok. apply Qcplus_le_compat. reflexivity. assumption.
  - etransitivity; [| eok]. rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat.
    * apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc5. Qcunfold. lra.
        etransitivity. rewrite Qcabs_minus. eok. apply Qcplus_le_compat. now apply Qclt_le_weak. reflexivity.
    * apply Qcmult_resp_nonneg.
        change 0 with (0 + 0). apply Qcplus_le_compat. now apply Qcabs_nonneg. revert Hc6. Qcunfold. lra.
        revert Hc5. Qcunfold. lra.
+ rewrite Qcabs_minus. replace (q₁1 * q₂1 - q₁0 * q₂0) with (q₁1 * (q₂1 - q₂0) + (q₁1 - q₁0) * q₂0) by ring.
  transitivity (ε₁ + 0).
  - rewrite Qcplus_0_r. etransitivity. now apply Qcabs_triangle. etransitivity; [| eok].
    do 2 rewrite Qcabs_mult. apply Qcplus_le_compat.
    * apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite Qcle_minus_iff. replace (|q₁0| + (ε₁0 + ε₁0) + - |q₁1|) with (ε₁0 + ε₁0 + - (|q₁1| - |q₁0|)) by ring.
        rewrite <- Qcle_minus_iff. etransitivity. apply Qcabs_triangle_reverse.
        etransitivity. rewrite Qcabs_minus. eok. apply Qcplus_le_compat. reflexivity. assumption.
        etransitivity. rewrite Qcabs_minus. eok. apply Qcplus_le_compat. reflexivity. assumption.
    * rewrite Qcmult_comm. apply Qcmult_le_compat.
        now apply Qcabs_nonneg.
        now apply Qcabs_nonneg.
        rewrite <- Qcplus_0_r at 1. apply Qcplus_le_compat. reflexivity. revert Hc2. Qcunfold. lra.
        etransitivity. rewrite Qcabs_minus. eok. apply Qcplus_le_compat. reflexivity. assumption.
  - apply Qcplus_le_compat; ok || reflexivity.
Qed.

Definition mulℝ_Cauchy := mulℝ_proper.

Theorem mulℝ_Cauchy_realizer : forall e, mulℝ_Cauchy↓e ⊩ ∀x y, Cauchy x → Cauchy y → Cauchy (x * y)%Re.
Proof. intro e. startn 0. apply mulℝ_proper_realizer. unfold Cauchy in *. do 4 eexists. split. eok. split; eok. Qed.

Definition mulℝ_switch := addℝ_switch.
(*λ"XY" "XY" @ λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"eqε" λ"eqq" λ"X" λ"Y"
  λ"f" "f" @ "ε₂" @ "ε₁" @ "q₂" @ "q₁" @ "eqε" @ "eqq" @ "Y" @ "X".*)

Lemma mulℝ_switch_realizer : forall e, mulℝ_switch↓e ⊩ ∀x y ε q, (x * y)%Re ε q → (y * x)%Re ε q.
Proof.
unfold mulℝ at 1. Ksolve. unfold mulℝ. Kmove.
exists ε₂, ε₁; find; now rewrite Qcplus_comm || rewrite Qcmult_comm.
Qed.

Definition mulℝ_Eeq_comm := λ"ε" λ"q" λ"f" "f" @ mulℝ_switch @ mulℝ_switch.

Theorem mulℝ_Eeq_comm_realizer : forall e, mulℝ_Eeq_comm↓e ⊩ ∀x y, (x * y ≡≡ y * x)%Re.
Proof. Ksolve; startn 0; apply mulℝ_switch_realizer; find. Qed.

Definition mulℝ_Req_comm := λ"Cx" λ"Cy" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X+Y" λ"Y+X"
  mulℝ_Cauchy @ "Cx" @ "Cy" @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ "X+Y" @ (mulℝ_switch @ "Y+X").

Theorem mulℝ_Req_comm_realizer : forall e, mulℝ_Req_comm↓e ⊩ ∀x y, Cauchy x → Cauchy y → (x * y ≡ y * x)%Re.
Proof.
intro e. startn 16. apply mulℝ_Cauchy_realizer. exists x, y. repeat split; try ok.
exists ε₁, ε₂, q₁, q₂. repeat (split; trivial). find.
startn 1. apply mulℝ_switch_realizer. find.
Qed.

(*
Theorem mulℝ_assoc_realizer :
  forall e, mulℝ_assoc↓e ⊩ ∀x y z, Cauchy x → Cauchy y → Cauchy z → x * (y * z) ≡ (x * y) * z.
Theorem mulℝ_1_l_realizer : forall e, mulℝ_1_l↓e ⊩ ∀x, Cauchy x → 1 * x ≡ x.
Theorem distr_realizer :
  forall e, distr↓e ⊩ ∀ x y z, Cauchy x → Cauchy y → Cauchy z → x * (y + z) ≡ (x * y) + (x *z).
*)

(** ***  Inverse  **)

Definition invℝ_Total := λ"Tx" λ"Cx" λ"n0x" λ"ε" λ"f" "n0x" @ λ"ε₁" λ"ε₀" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"0"
  (* Guard condition *)
  "0" @ 
  (* Shared computation *)
  Qq 2 @ (ℚdiv @ "ε₀") @ λ"ε₀/2"
  (* Getting the value q *)
  (* -- computing q' := 1 / (|q₁| - ε₁ - ε₀/2) *)
  absℚ @ "q₁" @ ℚsub @ "ε₁" @ ℚsub @ "ε₀/2" @ (Qq 1 @ ℚdiv) @ λ"q'"
  (* -- computing the bound := min(ε / (q'² = |q'| * ε), ε₀ / 2) *)
  absℚ @ "q'" @ ℚmul @ "ε" @ (ℚmul @ "q'" @ "q'" @ ℚadd) @ (ℚdiv @ "ε") @ minℚ @ "ε₀/2" @ λ"res"
  (* Making the proof *)
  "Tx" @ "res" @ (λ"q" λ"X'" Qq 1 @ ℚdiv @ "q" @ "f" @ λ"f" "f" @ "res" @ "X'").

Conjecture conjecture1 : forall (x : Re) (ε ε₁ ε0 ε₂ q₁ q : Qc),
  0 < ε -> 0 < ε₁ -> 0 < ε0 -> 0 < ε₂ -> ε₁ + ε0 + ε₂ <= |q₁| ->
  forall (q' := 1 / (|q₁| - ε₁ - ε0 / 2)) (bound := Qcmin (ε / (q' * q' + |q'| * ε)) (ε0 / 2)),
  0 < q' -> 0 < bound ->
  forall t t0 t1 t3 t5 : Λ,
    t ⊩ (∀₁ ε∈ℚ+*, ∃₁ q ∈ ℚ, x ε q) -> t0 ⊩ Cauchy x -> t3 ⊩ x ε₁ q₁ -> t5 ⊩ x bound q -> t1 ⊩ x ≠ (embed_ℚ_ℝ 0)
  -> bound < |q|.

Conjecture conjecture2 : forall ε ε₁ ε0 ε₂ q₁ q : Qc,
  0 < ε -> 0 < ε₁ -> 0 < ε0 -> 0 < ε₂ -> ε₁ + ε0 + ε₂ <= |q₁| ->
  forall (q' := 1 / (|q₁| - ε₁ - ε0 / 2))
         (bound := Qcmin (ε / (q' * q' + |q'| * ε)) (ε0 / 2)),
  0 < q' -> 0 < bound -> bound < |q| -> |1 / q| <= |q'|.

Theorem invℝ_Total_realizer : forall e, invℝ_Total↓e ⊩ ∀x, Total x → Cauchy x → x ≠ (embed_ℚ_ℝ 0) → Total (/ x).
Proof.
unfold Total, apartℝ. Ksolve. start.
(* Guard condition *)
apply (prop_guard Ht4). intros [_ ?]. subst.
(* Shared computation *)
apply Qq_realizer. find. start. apply ℚdiv_realizer. find. find.
(* Give the bound for the precision *)
pose (q' := 1 / (Qcabs q₁ - ε₁ - ε0 / 2)).
pose (bound := Qcmin (ε / (q' * q' + Qcabs q' * ε)) (ε0 / 2)).
(* Prove that the bound is positive *)
assert (Hq' : 0 < q').
{ unfold q'. replace (q₁ - 0) with q₁ in Hc3 by ring. apply Qclt_shift_div_l.
  + replace ((|q₁|) - ε₁ - ε0 / 2) with ((|q₁|) + - (ε₁ + ε0 / 2)) by ring.
    rewrite <- Qclt_minus_iff. apply Qclt_le_trans with (ε₁ + ε0 + ε₂); trivial.
    rewrite Qclt_minus_iff. replace (ε₁ + ε0 + ε₂ + - (ε₁ + ε0 / 2)) with (ε0 - ε0 / 2 + ε₂) by ring.
    rewrite <- Qcplus_0_l at 1. apply Qcplus_lt_compat; trivial.
    unfold Qcminus. rewrite <- Qclt_minus_iff. apply Qclt_shift_div_r. now compute.
    simpl. replace (ε0 * 2%Z) with (ε0 + ε0). rewrite Qclt_minus_iff. ring_simplify. assumption.
    rewrite Qcmult_comm. Qcunfold. simpl. ring.
  + rewrite Qcmult_0_l. now compute. }
assert (Hmin : 0 < bound).
{ apply Qc.min_glb_lt.
  * apply Qclt_shift_div_l.
    + replace 0 with (0 * q' + q' * 0) by ring. apply Qcplus_lt_compat.
      - apply Qcmult_lt_compat_r; assumption.
      - rewrite Qcabs_pos. apply Qcmult_lt_compat_l; assumption. apply Qclt_le_weak; assumption.
    + rewrite Qcmult_0_l. assumption.
  * apply half_pos; ok. }
(* Prove that the bound is a rational number *)
start. apply absℚ_realizer. find. start. apply ℚsub_realizer. find.
  find. start. apply ℚsub_realizer. find. find.
start. apply Qq_realizer. find. start. apply ℚdiv_realizer. find. find. find.
start. apply absℚ_realizer. find. start. apply ℚmul_realizer. find.
find. start. apply ℚadd_realizer. find. find. start. apply ℚdiv_realizer. find.
find. start. apply minℚ_realizer. find. find.
change 2%Z with (Z.of_nat 2). fold q'. fold bound.
(* Introduce the bound *)
start. apply Ht. find.
(* Prove that it is a valid approximation *)
start. apply Qq_realizer. find. start. apply ℚdiv_realizer. find. find. Ksolve. find.
assert (Hq : bound < |q|).
{ replace (q₁ - 0) with q₁ in Hc3 by ring. eapply (conjecture1 x ε ε₁ ε0 ε₂ q₁ q); eassumption. }
unfold invℝ. Ksolve.
* unfold Qcdiv. rewrite Qcmult_1_l. rewrite Qcabs_inv. rewrite Qcinv_involutive. ok.
* clear_realizers.
  assert (Hqq' : |1 / q| <= |q'|).
  { assert (Heq : q₁ - 0 = q₁) by ring. rewrite Heq in *. apply (conjecture2 ε ε₁ ε0 ε₂ q₁ q); assumption. }
  etransitivity. apply Qc.le_min_l.
  assert (0 < q' * q' + |q'| * ε).
  { change 0 with (0 + 0). apply Qcplus_lt_compat. apply Qcsquare_pos. symmetry. apply Qclt_not_eq; ok.
    replace 0 with (0 * ε) by ring. apply Qcmult_lt_compat_r. ok. rewrite Qcabs_pos. ok. apply Qclt_le_weak; ok. }
  apply Qcmult_le_compat.
  + apply Qclt_le_weak; ok.
  + rewrite Qcinv_nonneg. apply Qclt_le_weak. ok.
  + reflexivity.
  + apply Qcinv_pos_le_compat.
    - assert (0 < |1 / q|).
      { unfold Qcdiv. rewrite Qcmult_1_l. rewrite Qcabs_inv. rewrite Qcinv_pos. transitivity bound; ok. }
      change 0 with (0 + 0). apply Qcplus_lt_compat.
        rewrite <- Qcabs_pos.
          rewrite Qcabs_mult. apply Qcsquare_pos. symmetry. apply Qclt_not_eq. ok.
          now apply Qcsquare_nonneg.
        replace 0 with (0 * ε) by ring. apply Qcmult_lt_compat_r; ok.
    - apply Qcplus_le_compat.
        setoid_rewrite <- Qcabs_pos at 1 2; try now apply Qcsquare_nonneg.
        do 2 rewrite Qcabs_mult. apply Qcmult_le_compat; apply Qcabs_nonneg || ok.
        apply Qcmult_le_compat_r. ok. apply Qclt_le_weak. ok.
* unfold Qcdiv. rewrite Qcmult_1_l. rewrite Qcinv_involutive. ok.
Qed.
