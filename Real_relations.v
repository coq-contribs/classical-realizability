Require Import QArith.
Require Import Psatz.
Require Import Kbase.
Require Import Rationals. (* Order matters for Scopes *)
Require Import Real_definitions.

Close Scope Re_scope.


(********************)
(** *  Equalities  **)
(********************)


(** **  Extensional equality is an equivalence  **)

(** Reflexivity **)
Definition Eeq_refl := λ"ε" λ"q" λ"f" ("f" @ Id @ Id).

Theorem Eeq_refl_realizer : forall e, Eeq_refl↓e ⊩ ∀x, (x ≡≡ x)%Re.
Proof. intro e. unfold Eeq. start. apply Ht. repeat split; try start; ok. Qed.

(** Symmetry **)
Definition Eeq_sym :=
  λ"eq" λ"ε" λ"q" λ"f" ("f" @ ("eq" @ "ε" @ "q" @ ff) @ ("eq" @ "ε" @ "q" @ tt)).

Theorem Eeq_sym_realizer : forall e, Eeq_sym↓e ⊩ ∀x, ∀y, (x ≡≡ y → y ≡≡ x)%Re.
Proof.
intro e. unfold Eeq. start. apply Ht0. repeat split; try ok.
  start. apply Ht. find. start. apply Ht3. eok. split; ok.
  start. apply Ht. find. start. apply Ht2. eok. split; ok.
Qed.

(** Transitivity **)
Definition Eeq_trans := λ"eqxy" λ"eqyz" λ"ε" λ"q" λ"f" ("f"
  @ (λ"X" ("eqyz" @ "ε" @ "q" @ tt @ ("eqxy" @ "ε" @ "q" @ tt @ "X")))
  @ (λ"Z" ("eqxy" @ "ε" @ "q" @ ff @ ("eqyz" @ "ε" @ "q" @ ff @ "Z")))).

Theorem Eeq_trans_realizer : forall e, Eeq_trans↓e ⊩ ∀x, ∀y, ∀z, (x ≡≡ y → y ≡≡ z → x ≡≡ z)%Re.
Proof.
intro e. unfold Eeq. start. apply Ht1. repeat split; ok || start.
  repeat Ksolve. eok. repeat Ksolve. eok. now split.
  repeat Ksolve. eok. repeat Ksolve. eok. now split.
Qed.

(** **  Extensional equality implies Cauchy equality  **)

Definition Eeq_implies_Req :=
  λ"Cx" λ"eq" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  "Cx" @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ "X" @ ("eq" @ "ε₂" @ "q₂" @ ff @ "Y").

Theorem Eeq_implies_Req_realizer : forall e, Eeq_implies_Req↓e ⊩ ∀x y, Cauchy x → (x ≡≡ y → x ≡ y)%Re.
Proof. Kmove. exists ε₁. find. repeat Ksolve. eok. now split. Qed.

(** **  Equality is a PER over total predicates  **)

(** Symmetry **)
Definition Req_sym := λ"Eqxy" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  "Eqxy" @ "ε₂" @ "ε₁" @ "q₂" @ "q₁" @ "Y" @ "X".

Lemma Req_sym_realizer : forall e, Req_sym↓e ⊩ ∀x y, (x ≡ y → y ≡ x)%Re.
Proof. intro. start. rewrite Qcabs_minus,Qcplus_comm in Hπ. Kmove. exist2 ε₂ ε₁. Ksolve. Qed.

(** Transitivity **)
Definition Req_trans := λ"Ty" λ"Eqxy" λ"Eqyz" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Z"
  ℚadd @ "ε₁" @ "ε₂" @ (ℚsub @ "q₁" @ "q₂" @ absℚ_tight) @ (λ"ε"
  (ℚdiv @ "ε" @ Rat 2) @ λ"ε/2" (* shared computation *)
    "Ty" @ "ε/2" @ (λ"q" λ"Y"
       ("Eqxy" @ "ε₁" @ "ε/2" @ "q₁" @ "q" @ "X" @ "Y") @
       ("Eqyz" @ "ε/2" @ "ε₂" @ "q" @ "q₂" @ "Y" @ "Z"))).

Lemma Req_trans_realizer : forall e, Req_trans↓e ⊩ ∀x y z, Total y → (x ≡ y → y ≡ z → x ≡ z)%Re.
Proof.
Ksolve. apply absℚ_tight_realizer. find.
start.
assert (0 < ε / 2)%Qc by now apply half_pos.
assert (0 <= ε / 2)%Qc by now apply Qclt_le_weak.
apply Ht. find.
startn 3. eapply prop_guard. start. apply Ht0. exists ε₁. find.
intro Habs. Kevals. apply Ht1. exist2 (ε / 2) ε₂. find.
apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. intro Ha.
replace (q₁ - q₂) with ((q₁ - q) + (q - q₂)) by ring. etransitivity. now apply Qcabs_triangle.
replace (ε₁ + ε₂ + ε) with (ε₁ + ε/2 + (ε/2 + ε₂)). now apply Qcplus_le_compat.
replace (ε₁ + ε / 2 + (ε / 2 + ε₂)) with (ε₁ + ε₂ + (ε / 2+ ε / 2)) by ring. f_equal. now rewrite eq_half.
Qed.


(****************)
(** *  orders  **)
(****************)


(** **  Rle is a large order  **)

Theorem Req_Rle_subtype : forall x y, (x ≡ y ⊆ x <= y)%Re.
Proof.
unfold Req, Rle. intros x y π Hπ. dec π. exists ε₁. find. apply (prop_subst_stack Hπ).
rewrite Qcabs_diff_le_condition. Qcunfold. lra.
Qed.
Hint Resolve Req_Rle_subtype : Ksubtype.

Corollary Req_Rle_proper : forall x y e, Id↓e ⊩ (x ≡ y → x <= y)%Re.
Proof. intros. apply sub_id. apply Req_Rle_subtype. Qed.

(** Reflexivity **)

Definition Rle_refl := Id.

Corollary Rle_refl_realizer : forall e, Rle_refl↓e ⊩ ∀₁x∈Cauchy, (x <= x)%Re.
Proof.
Kmove. exists ε₁. find. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
rewrite Qcabs_diff_le_condition. Qcunfold. lra.
Qed.

(** Transitivity **)
Definition Rle_trans := λ"Ty" λ"Lexy" λ"Leyz" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Z"
  ℚadd @ "q₂" @ "ε₁" @ ℚadd @ "ε₂" @ (leℚ_tight @ "q₁")
             @ (λ"ε" Qq 2 @ (ℚdiv @ "ε") @ "Ty" @ (λ"q" λ"Y"
       (Qq 2 @ (ℚdiv @ "ε") @ ("Lexy" @ "ε₁") @ "q₁" @ "q" @ "X" @ "Y") @
       (Qq 2 @ (ℚdiv @ "ε") @ "Leyz" @ "ε₂" @ "q" @ "q₂" @ "Y" @ "Z"))).

Lemma Rle_trans_realizer : forall e, Rle_trans↓e ⊩ ∀x y z, Total y → (x <= y → y <= z → x <= z)%Re.
Proof.
Ksolve. apply leℚ_tight_realizer. find. find.
start. apply Qq_realizer. find. start. apply ℚdiv_realizer. find.
find. start. apply Ht. exists (ε/2). Kmove. now apply half_pos. find.
find. startn 3. eapply prop_guard. Kmove. apply Qq_realizer.
  find. start. apply ℚdiv_realizer. find.
  find. Kmove. exist2 ε₁ (ε / 2). find. now apply Qclt_le_weak, half_pos. find.
intro Habs. Kmove. apply Qq_realizer. find. start. apply ℚdiv_realizer. find.
find. Kmove. exists (ε / 2). find. now apply Qclt_le_weak, half_pos. Ksolve.
apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers.
intro Ha. etransitivity. apply Habs.
etransitivity. apply Qcplus_le_compat. apply Qcplus_le_compat. apply Ha. reflexivity. reflexivity.
setoid_replace ε with (ε / 2 + ε / 2) at 3 by (Qcunfold; destruct ε; simpl; field).
replace (q₂ + ε / 2 + ε₂ + ε₁ + ε / 2) with (q₂ + ε₁ + ε₂ + (ε / 2 + ε / 2)) by ring. reflexivity.
Qed.

(** Antisymmetry **)
Definition Rle_antisym := λ"Lexy" λ"Leyx" λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  ("Lexy" @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ "X" @ "Y")
  @ ("Leyx" @ "ε₂" @ "ε₁" @ "q₂" @ "q₁" @ "Y" @ "X").

Theorem Rle_antisym_realizer : forall e, Rle_antisym↓e ⊩ ∀ x y, (x <= y → y <= x → x ≡ y)%Re.
Proof.
intro e. startn 9. eapply prop_guard. Kmove. exists ε₁. find. intro Hle₁.
Kmove. exist2 ε₂ ε₁. find. apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear_realizers. intro Hle₂. rewrite Qcabs_diff_le_condition. revert Hle₁ Hle₂. Qcunfold. lra.
Qed.

Definition Rle_proper :=
   λ"Tx₁" λ"Ty₁" λ"eq₁" λ"eq₂" λ"le" Rle_trans @ "Ty₁" @ (Rle_trans @ "Tx₁" @ (Req_sym @ "eq₁") @ "le") @ "eq₂".

Theorem Rle_proper_realizer : forall e,
  Rle_proper↓e ⊩ ∀x₁ x₂ y₁ y₂, Total x₁ → Total y₁ → (x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ <= y₁ → x₂ <= y₂)%Re.
Proof.
Kmove. apply Rle_trans_realizer. exists3 x₂ y₁ y₂. repeat split.
  ok.
  start. apply Rle_trans_realizer. exists3 x₂ x₁ y₁. findn 1.
  eapply sub_term; [| subtyping]. intros π' Hπ'. Kevals. apply Req_sym_realizer. do 2 eexists. split. eapply Ht1. eok.
  exists ε₁0. find.
  now eapply sub_term; [| subtyping].
  exists ε₁. find.
Qed.

(** **  Rlt is a strict order  **)

(** Irreflexivity **)
Definition Rlt_irrefl := λ"Cx" λ"Lt" "Lt" @ (λ"ε₁" λ"ε" λ"ε₂" λ"q₁" λ"q₂" λ"X₁" λ"X₂"
  nId @ ("Cx" @ "ε₁" @ "ε₂" @ "q₁" @ "q₂" @ "X₁" @ "X₂")).

Theorem Rlt_irrefl_realizer : forall e, Rlt_irrefl↓e ⊩ ∀x, Cauchy x → ¬(x << x)%Re.
Proof.
Ksolve. start.
eapply (prop_realizer2 (A := (Qcle (q₂ - q₁) (ε₁ + ε₂)))).
  revert Hc0 Hc2. Qcunfold. lra.
  do 2 Ksolve. now apply Qclt_le_weak. now apply Qclt_le_weak.
  rewrite Qcabs_minus, Qcabs_le_condition. apply (prop_subst_stack Hπ). now intros [_ ?].
Qed.

(** Transitivity **)
Definition Rlt_trans := λ"Cy" λ"Ltxy" λ"Ltyz" λ"f"
  "Ltxy" @ (λ"εx" λ"ε₁" λ"εy₁" λ"qx" λ"qy₁" λ"X" λ"Y₁"
  "Ltyz" @ (λ"εy₂" λ"ε₂" λ"εz" λ"qy₂" λ"qz" λ"Y₂" λ"Z"
  ("Cy" @ "εy₁" @ "εy₂" @ "qy₁" @ "qy₂" @"Y₁" @ "Y₂") @
  (ℚadd @ "ε₁" @ "ε₂") @ ("f" @ "εx") @ "εz" @ "qx" @ "qz" @ "X" @ "Z")).

Theorem Rlt_trans_realizer : forall e, Rlt_trans↓e ⊩ ∀ x y z, Cauchy y → (x << y → y << z → x << z)%Re.
Proof.
intro e. Kmove. exists Z; split; [| ok].
Kmove. exists Z; split; [| ok]. startn 14.
eapply prop_guard. now Ksolve; apply Qclt_le_weak. intro Hle.
Kmove. exist2 ε₁ (ε + ε0). find. rewrite <- Qcplus_0_l at 1. now apply Qcplus_lt_compat.
(* Arithmetical proof *)
rewrite Qcabs_le_condition in Hle. clear_realizers. revert Hc2 Hc6 Hle. clear. Qcunfold. lra.
Qed.

(** Compatibility with equality **)
(* We need to cut ε in 5 *)
Definition Rlt_proper := λ"Tx₂" λ"Ty₂" λ"eqx" λ"eqy" λ"Lt" λ"f"
  "Lt" @ λ"ε₁" λ"ε" λ"ε₂" λ"q₁" λ"q₂" λ"X" λ"Y"
  Qq 5 @ (ℚdiv @ "ε") @ λ"ε/5" (* shared computation *)
  "Tx₂" @ "ε/5" @ λ"qx₂" λ"X₂" "Ty₂" @ "ε/5" @ λ"qy₂" λ"Y₂"
  ("eqx" @ "ε₁" @ "ε/5" @ "q₁" @ "qx₂" @ "X" @ "X₂") @
  ("eqy" @ "ε₂" @ "ε/5" @ "q₂" @ "qy₂" @ "Y" @ "Y₂") @
  "f" @ "ε/5" @ "ε/5" @ "ε/5" @ "qx₂" @ "qy₂" @ "X₂" @ "Y₂".

Theorem Rlt_proper_realizer :
  forall e, Rlt_proper↓e ⊩ ∀x₁ x₂ y₁ y₂, Total x₂ → Total y₂ → (x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ << y₁ → x₂ << y₂)%Re.
Proof.
intro e. Kmove. eexists; split; [| try eok].
Kmove. apply Qq_realizer. exists (ℚ (ε/5)). find. start. apply ℚdiv_realizer. find.
assert (0 < ε / 5) by now apply fifth_pos. assert (0 <= ε / 5)%Qc by now apply Qclt_le_weak.
do 2 Ksolve.
startn 11. eapply prop_guard. Kmove. exists ε₁. find. now apply Qclt_le_weak.
intro Hle₁. eapply prop_guard. Kmove. exists ε₂. find. now apply Qclt_le_weak.
intro Hle₂. Ksolve.
(* Arithmetical proof *)
clear_realizers.
apply Qcabs_diff_le_condition in Hle₁. destruct Hle₁ as [_ Hle₁].
apply Qcabs_diff_le_condition in Hle₂. destruct Hle₂ as [Hle₂ _].
transitivity (q₁ + ε₁ + ε / 5 + ε / 5 + ε / 5 + ε / 5).
  repeat (apply Qcplus_le_compat; [| reflexivity]). now rewrite <- Qcplus_assoc.
transitivity (q₂ - (ε₂ + ε / 5)); [| assumption]. apply Qcle_shift_minus_l.
replace (q₁ + ε₁ + ε / 5 + ε / 5 + ε / 5 + ε / 5 + (ε₂ + ε / 5))
  with (q₁ + ε₁ + (ε / 5 + ε / 5 + ε / 5 + ε / 5 + ε / 5) + ε₂) by ring.
replace (ε / 5 + ε / 5 + ε / 5 + ε / 5 + ε / 5) with ε. assumption.
Qcunfold. simpl. field.
Qed.
