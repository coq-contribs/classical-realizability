Require Import Kbase.
Require Import Rationals.
Require Import Real_definitions.
Require Import Real_relations.
Require Import Real_operations.


Definition non_trivial := λ"f" Qq 1 @ (Qq 0 @ (Qq (1/3) @ λ"1/3" "f" @ "1/3" @ "1/3" @ "1/3")) @ Id @ Id.

Theorem non_trivial_realizer : forall e, non_trivial↓e ⊩ (0 << 1)%Re.
Proof.
intro e.
start. apply Qq_realizer. eexists (_ → _ → _). find;
repeat (start; apply Qq_realizer; find); [Ksolve |..]; find;
try apply prop_realizer1; now split || compute.
Qed.

(** **  Archimed axiom  **)

Definition Archimedℝ := λ"Tx" λ"Cx" λ"f" Qq 1 @ "Tx" @ (λ"q" λ"X" Qq 1 @ (ℚadd @ "q") @ "f"
  @ λ"ε₁" λ"ε₂" λ"q₁" λ"q₂" λ"X'" λ"eqq" "eqq"
  @ Qq 1 @ ("Cx" @ "ε₁") @ "q₁" @ "q" @ "X'" @ "X").

Theorem Archimed : forall e, Archimedℝ↓e ⊩ ∀₁x∈ℝ, ∃₁q∈ℚ, (x <= q)%Re.
Proof.
intro e. start.
(* Getting one value q ∈ x[ε] *)
apply Qq_realizer. find. start. apply Ht. find. now compute. find.
(* The bound is q + 1 *)
start. apply Qq_realizer. find. start. apply ℚadd_realizer. find. find. Ksolve. find.
(* Guard condition *)
start. apply (prop_guard Ht4). intros [_ ?]. subst.
(* Using Cauchy property of x *)
apply Qq_realizer. find. Kmove. exist2 ε₁ 1. find. now compute. find.
apply (prop_subst_stack Hπ).
(* Arithmetical proof *)
clear -Hc0. rewrite Qcabs_minus, Qcabs_diff_le_condition. intros [_ ?]. rewrite <- Qcplus_0_r at 1.
apply Qcplus_le_compat. rewrite <- Qcplus_assoc. now setoid_rewrite Qcplus_comm at 2. assumption.
Qed.
