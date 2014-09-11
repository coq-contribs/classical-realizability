Require Import QArith.
Require Export Qcabs.
Require Export Qcminmax.
Require Import Kbase.


(************************************)
(** *  Primitive rational numbers  **)
(************************************)


(** **  Operations on primitive rational numbers  **)

Parameter Rat : Qc -> instruction.
Parameter ℚeq ℚle ℚlt ℚadd ℚsub ℚmul ℚdiv ℚopp : instruction.

Axiom red_ℚeq : forall e e' e'' p q u v π,
  ℚeq↓e ★ Rat p↓e'·Rat q↓e''·u·v·π ≻ (if Qc_eq_dec p q then u else v) ★ π.
Axiom red_ℚle : forall e e' e'' p q u v π,
  ℚle↓e ★ Rat p↓e'·Rat q↓e''·u·v·π ≻ (if Qclt_le_dec q p then v else u) ★ π.
Axiom red_ℚlt : forall e e' e'' p q u v π,
  ℚlt↓e ★ Rat p↓e'·Rat q↓e''·u·v·π ≻ (if Qclt_le_dec p q then u else v) ★ π.
Axiom red_ℚadd : forall e e' e'' p q k π, ℚadd↓e ★ Rat p↓e'·Rat q↓e''·k·π ≻ k ★ Rat (p+q)↓∅·π.
Axiom red_ℚsub : forall e e' e'' p q k π, ℚsub↓e ★ Rat p↓e'·Rat q↓e''·k·π ≻ k ★ Rat (p-q)↓∅·π.
Axiom red_ℚmul : forall e e' e'' p q k π, ℚmul↓e ★ Rat p↓e'·Rat q↓e''·k·π ≻ k ★ Rat (p*q)↓∅·π.
Axiom red_ℚdiv : forall e e' e'' p q k π, ℚdiv↓e ★ Rat p↓e'·Rat q↓e''·k·π ≻ k ★ Rat (p/q)↓∅·π.
Axiom red_ℚopp : forall e e' q k π, ℚopp↓e ★ Rat q↓e'·k·π ≻ k ★ Rat (- q)↓∅·π.

Definition RatArg q F := fun π => exists e, exists π', π = Rat q↓e·π' /\ π' ∈ ‖F‖.
Notation "'[' q ']'  '→'  F" := (RatArg q F) (at level 78, right associativity).

(** **  Sets of rational numbers  **)

Definition ℚ q := ∀Z, ([q] → Z) → Z.
Global Instance Rel_ℚ : Relativisation ℚ := now_Rel ℚ (fun f q => [q] → f q).
Global Hint Unfold Rel_ℚ : Krivine.

Parameter Qq : Qc -> term.
Hypothesis Qq_realizer : forall q e, Qq q↓e ⊩ ℚ q.

(** We do not use [∀Z, [q] → 0 < q ↦ Z) → Z] because we might not want to evaluate [q]
    but just know that it is positive.  Same comment for ℚnneg. **)
Definition ℚpos q := ∀Z, (0 < q ↦ [q] → Z) → Z. (* ℚ q ∧ 0 < q *)
Global Notation "ℚ+*" := ℚpos.
Global Instance Rel_ℚpos : Relativisation ℚpos := now_Rel ℚpos (fun f q => 0 < q ↦ [q] → f q).

Definition ℚnneg q := ∀Z, (0 <= q ↦ [q] → Z) → Z. (* ℚ q ∧ 0 <= q *)
Global Notation "ℚ+" := ℚnneg.
Global Instance Rel_ℚnneg : Relativisation ℚnneg := now_Rel ℚnneg (fun f q => 0 <= q ↦ [q] → f q).
Global Hint Unfold Rel_ℚpos Rel_ℚnneg : Krivine.

(** ** Tactics **)

Global Ltac rat_Keval tac :=
  lazymatch goal with
    | [ |- Cst ℚeq↓ _ ★ (Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?u·?v·?π) ∈ ⫫] =>
         apply anti_evaluation with ((if Qc_eq_dec q₁ q₂ then u else v) ★ π); [now apply red_ℚeq | simpl Qc_eq_dec]
    | [ |- Cst ℚle↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?u·?v·?π ∈ ⫫] =>
         apply anti_evaluation with ((if Qclt_le_dec q₂ q₁ then v else u) ★ π); [now apply red_ℚle |simpl Qclt_le_dec]
    | [ |- Cst ℚlt↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?u·?v·?π ∈ ⫫] =>
         apply anti_evaluation with ((if Qclt_le_dec q₁ q₂ then u else v) ★ π); [now apply red_ℚlt |simpl Qclt_le_dec]
    | [ |- Cst ℚadd↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?k·?π ∈ ⫫] =>
         apply anti_evaluation with (k ★ Rat (q₁+q₂)↓∅·π); [now apply red_ℚadd |]
    | [ |- Cst ℚsub↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?k·?π ∈ ⫫] =>
         apply anti_evaluation with (k ★ Rat (q₁-q₂)↓∅·π); [now apply red_ℚsub |]
    | [ |- Cst ℚmul↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?k·?π ∈ ⫫] =>
         apply anti_evaluation with (k ★ Rat (q₁*q₂)↓∅·π); [now apply red_ℚmul |]
    | [ |- Cst ℚdiv↓ _ ★ Cst(Rat ?q₁)↓ _·Cst(Rat ?q₂)↓ _·?k·?π ∈ ⫫] =>
         apply anti_evaluation with (k ★ Rat (q₁/q₂)↓∅·π); [now apply red_ℚdiv |]
    | [ |- Cst ℚopp↓ _ ★ Cst(Rat ?q)↓ _·?k·?π ∈ ⫫] =>
         apply anti_evaluation with (k ★ Rat (- q)↓∅·π); [now apply red_ℚopp |]
    | _ => tac
end.

Global Ltac rat_dstack tac Hπ :=
  match type of Hπ with
    | ?π ∈ ‖[?e] → ?F‖ =>
      let e := fresh "e" in let t := fresh "t" in let n := fresh "n" in
      let π' := fresh "π" in let Heq := fresh "Heq" in 
      destruct Hπ as [e [π' [Heq Hπ]]]; destruct π as [| t π]; inversion Heq; subst π' t; clear Heq
(*    | ?π ∈ ‖ℚ ?e‖ => unfold ℚ in Hπ; rat_dstack tac Hπ *)
    | ?π ∈ ‖ℚnneg ?e‖ => unfold ℚnneg in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ℚ+* ?e‖ => unfold ℚpos in Hπ; let Hc := fresh "Hc" in destruct Hπ as [Hc Hπ]
    | _ => tac Hπ
  end.

Global Ltac Keval ::= basic_Keval ltac:(rat_Keval fail).
Global Ltac dstack ::= basic_dstack ltac:(rat_dstack ltac:(prop_dstack fail)).

Lemma ℚpos_ℚnoneg_subtype : forall q, ℚ+* q ⊆ ℚ+ q.
Proof. unfold ℚpos. do 2 Ksolve. now apply Qclt_le_weak. Qed.
Lemma ℚnonneg_subtype : forall q, ℚ+ q ⊆ ℚ q.
Proof. unfold ℚ. do 2 Ksolve. Qed.

(** **  Storage operator  **)

Definition Mℚ := λ"f" λ"q" "q" @ "f".

Property Mℚ_storage : forall e, Mℚ↓e ⊩ ∀q Z, ([q] → Z) → (ℚ q → Z).
Proof. Ksolve. Qed.

Definition mℚ := λ"q" λ"f" "f" @ "q".
Property mℚ_storage : forall e, mℚ↓e ⊩ ∀q, [q] → ℚ q.
Proof. unfold ℚ. Ksolve. Qed.

(** **  Realizers for operations on [ℚ]  **)

Lemma ℚadd_realizer : forall e, Cst ℚadd↓e ⊩ ∀p q, [p] → [q] → ℚ (p + q).
Proof. unfold ℚ. Ksolve. Qed.
Lemma ℚopp_realizer : forall e, Cst ℚopp↓e ⊩ ∀q, [q] → ℚ (- q).
Proof. unfold ℚ. Ksolve. Qed.
Lemma ℚsub_realizer : forall e, Cst ℚsub↓e ⊩ ∀p q, [p] → [q] → ℚ (p - q).
Proof. unfold ℚ. Ksolve. Qed.
Lemma ℚmul_realizer : forall e, Cst ℚmul↓e ⊩ ∀p q, [p] → [q] → ℚ (p * q).
Proof. unfold ℚ. Ksolve. Qed.
Lemma ℚdiv_realizer : forall e, Cst ℚdiv↓e ⊩ ∀p q, [p] → [q] → ℚ (p / q).
Proof. unfold ℚ. Ksolve. Qed.

Definition addℚ := caron2 ℚadd.
Definition oppℚ := caron1 ℚopp.
Definition subℚ := caron2 ℚsub.
Definition mulℚ := caron2 ℚmul.
Definition divℚ := caron2 ℚdiv.

Lemma divℚ_realizer : forall p q tp tq e, tp↓e ⊩ ℚ p -> tq↓e ⊩ ℚ q -> (divℚ @ tp @ tq)↓e ⊩ ℚ (p/q).
Proof. unfold divℚ, caron2. Kmove. exists (ℚ q → ℚ (p/q)). do 3 Ksolve. apply ℚdiv_realizer. find. Qed.

Corollary ℚhalf : forall q t e, t↓e ⊩ ℚ q -> (divℚ @ t @ Qq (1+1))↓e ⊩ ℚ (q/(1+1)).
Proof. intros. apply divℚ_realizer. ok. apply Qq_realizer. Qed.

Corollary ℚthird : forall q t e, t↓e ⊩ ℚ q -> (divℚ @ t @ Qq (1+1+1))↓e ⊩ ℚ (q/(1+1+1)).
Proof. intros. apply divℚ_realizer. ok. apply Qq_realizer. Qed.

Corollary ℚquarter : forall q t e, t↓e ⊩ ℚ q -> (divℚ @ t @ Qq (1+1+1+1))↓e ⊩ ℚ (q/(1+1+1+1)).
Proof. intros. apply divℚ_realizer. ok. apply Qq_realizer. Qed.

Corollary ℚfifth : forall q t e, t↓e ⊩ ℚ q -> (divℚ @ t @ Qq (1+1+1+1+1))↓e ⊩ ℚ (q/(1+1+1+1+1)).
Proof. intros. apply divℚ_realizer. ok. apply Qq_realizer. Qed.

(** **  Realizers for comparisons on [ℚ]  **)

Notation "p '≡' q" := (prop (p = q)) (at level 70) : Qc_scope.
Notation "p '≤' q" := (prop (Qcle p q)) (at level 70) : Qc_scope.
Notation "p '<<' q" := (prop (Qclt p q)) (at level 70) : Qc_scope.
Notation "p '≥' q" := (prop (Qcge p q)) (at level 70, only parsing) : Qc_scope.
Notation "p '>>' q" := (prop (Qcgt p q)) (at level 70, only parsing) : Qc_scope.

Theorem addℚ_resp_pos : forall e p q tp tq, (tp↓e ⊩ 0 << p) -> (tq↓e ⊩ 0 << q) -> (tp @ tq)↓e ⊩ 0 << p + q.
Proof.
intros e p q tp tq Htp Htq. start. apply (prop_guard Htp). intro Hp. apply Htq.
apply (prop_subst_stack Hπ). intro. rewrite <- Qcplus_0_r at 1. now apply Qcplus_lt_compat.
Qed.

Opaque inter.

Lemma ℚeq_realizer : forall e, ℚeq↓e ⊩  ∀₂p,q∈ℚ×ℚ, ∀A B, (p = q ↦ A) → (~p = q ↦ B) → (p = q ↦ A) ∩ (~p = q ↦ B).
Proof. intro e. start. destruct (Qc_eq_dec p q); destruct Hπ; Ksolve; contradiction. Qed.

Lemma ℚle_realizer : forall e, ℚle↓e ⊩ ∀₂p,q∈ℚ×ℚ, ∀A B, (p <= q ↦ A) → (q < p ↦ B) → (p <= q ↦ A) ∩ (q < p ↦ B).
Proof.
intro e. start.
destruct (Qclt_le_dec q p) as [Hlt |?]; destruct Hπ;
try apply Qclt_not_le in Hlt; Ksolve; contradiction || now elim (Qle_not_lt p q).
Qed.

Lemma ℚlt_realizer : forall e, ℚlt↓e ⊩ ∀₂p,q∈ℚ×ℚ, ∀A B, (p < q ↦ A) → (q <= p ↦ B) → (p < q ↦ A) ∩ (q <= p ↦ B).
Proof.
intro e. start.
destruct (Qclt_le_dec p q) as [Hlt |?]; destruct Hπ;
try apply Qclt_not_le in Hlt; Ksolve; try contradiction || now elim (Qle_not_lt q p).
Qed.

Global Opaque ℚ addℚ subℚ mulℚ divℚ oppℚ.

(** **  Derived operations  **)

Definition absℚ := λ"q" Qq 0 @ ℚle @ "q" @ (mℚ @ "q") @ (ℚopp @ "q").

Lemma absℚ_realizer : forall e, absℚ↓e ⊩ ∀₁q∈ℚ, ℚ (Qcabs q).
Proof.
Kmove. apply Qq_realizer.
exists ([q] → (0<=q ↦ ℚ (Qcabs q)) → (~0<=q ↦ ℚ (Qcabs q)) → ℚ (Qcabs q)). find.
  start. destruct (Qclt_le_dec q 0); Ksolve. now apply Qclt_not_le.
  start. apply mℚ_storage. findn 3. now rewrite Qcabs_pos in Hπ.
  start. apply ℚopp_realizer. findn 3. rewrite Qcabs_neg in Hπ. ok. apply Qclt_le_weak. now apply Qcnot_le_lt.
Qed.

Definition maxℚ := λ"p" λ"q" ℚle @ "p" @ "q" @ (mℚ @ "q") @ (mℚ @ "p").

Lemma maxℚ_realizer : forall e, maxℚ↓e ⊩ ∀₂p,q∈ℚ×ℚ, ℚ (Qcmax p q).
Proof.
intro e. startn 6. apply ℚle_realizer. find.
  start. apply mℚ_storage. find.
  start. apply mℚ_storage. find.
  eapply sub_stack. eassumption.
  (* Arithmetical proof *)
  start. destruct (Qclt_le_dec q p).
    right. split. ok. rewrite Qc.max_l in *. ok. now apply Qclt_le_weak.
    left. split. ok. rewrite Qc.max_r in *; ok.
Qed.

Definition minℚ := λ"p" λ"q" ℚle @ "p" @ "q" @ (mℚ @ "p") @ (mℚ @ "q").

Lemma minℚ_realizer : forall e, minℚ↓e ⊩ ∀₂p,q∈ℚ×ℚ, ℚ (Qcmin p q).
Proof.
intro e. startn 6. apply ℚle_realizer. find.
  start. apply mℚ_storage. find.
  start. apply mℚ_storage. find.
  eapply sub_stack. eassumption.
  (* Arithmetical proof *)
  start. destruct (Qclt_le_dec q p).
    right. split. ok. rewrite Qc.min_r in *. ok. now apply Qclt_le_weak.
    left. split. ok. rewrite Qc.min_l in *; ok.
Qed.

Definition leℚ_tight :=
  λ"q₁" λ"q₂" λ"f" ℚle @ "q₁" @ "q₂" @ Id @ (Qq 2 @ (ℚsub @ "q₁" @ "q₂" @ ℚdiv) @ "f").

Theorem leℚ_tight_realizer : forall e, leℚ_tight↓e ⊩ ∀₂q₁,q₂∈ℚ×ℚ, (∀₁ε∈ℚ+*, q₁ ≤ q₂ + ε) → q₁ ≤ q₂.
Proof.
intro e. startn 7. apply ℚle_realizer. find.
+ rewrite mapsto_equiv. now apply prop_realizer1.
+ start. apply Qq_realizer. eexists (_ → _). find. Ksolve.
apply Qclt_shift_div_l. now compute. unfold Qcminus. now rewrite <- Qclt_minus_iff.
+ destruct (Qclt_le_dec q₂ q₁) as [Hq | Hq].
  - right. split. ok. right. split.
    apply Qclt_not_le. Qcunfold. field_simplify. apply Qlt_shift_div_r. now compute. simpl. field_simplify.
    setoid_replace ((2 # 1) * q₁ / 1)%Q with (q₁ + q₁)%Q by field.
    setoid_replace ((q₂ + q₁) / 1)%Q with (q₂ + q₁)%Q by field.
    apply Qplus_lt_le_compat. ok. now apply Qle_refl. now compute.
    apply (top_bot_sub_prop Hπ).
  - left. now split.
Qed.

Definition absℚ_tight := λ"q₁" (absℚ @ "q₁") @ leℚ_tight.

Theorem absℚ_tight_realizer : forall e, absℚ_tight↓e ⊩ ∀₂q₁,q₂∈ℚ×ℚ, (∀₁ε∈ℚ+*, |q₁| ≤ q₂ + ε) → |q₁| ≤ q₂.
Proof. Ksolve. apply absℚ_realizer. find. startn 0. apply leℚ_tight_realizer. find. find. Qed.

Global Opaque absℚ maxℚ minℚ leℚ_tight absℚ_tight.
