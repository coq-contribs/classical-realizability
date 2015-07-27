Require Import Arith.
Require Import Omega.
Require Import ClassicalRealizability.Kbase.
Require Import ClassicalRealizability.Integers.
Require Import ClassicalRealizability.KBool.


Ltac Keval := basic_Keval ltac:(idtac; int_Keval fail).

(** Non deterministic boolean **)

Parameter fork : instruction.

Axiom red_fork1 : forall t u e π, fork↓e ★ t·u·π ≻ t ★ π.
Axiom red_fork2 : forall t u e π, fork↓e ★ t·u·π ≻ u ★ π.

(** We cannot put automatization tactics for evaluating fork,
    as there are two possible choices. **)
Ltac fork1 :=
  match goal with
    | |- Cst fork↓_ ★ ?t·?u·?π ∈ ⫫ => apply anti_evaluation with (t ★ π);
          [now apply red_fork1 |]
  end.

Ltac fork2 :=
  match goal with
    | |- Cst fork↓_ ★ ?t·?u·?π ∈ ⫫ => apply anti_evaluation with (u ★ π);
          [now apply red_fork2 |]
  end.

Transparent inter.

Theorem fork_spec1 : forall A B e, fork↓e ⊩ A → B → (A ∩ B).
Proof. Ksolve; [fork1 | fork2]; Ksolve. Qed.


(** *  Recurrence axiom  **)

(** Proved with primitive integers rather than Krivine ones. **)
Definition rec := Y @ λ"n" fork @ (mℕ @ Int 0) @ ("n" @ succℕ).

Theorem recurrence_axiom : forall x e, rec↓e ⊩ ℕ x.
Proof.
Ksolve. apply (Y_realizer lt_wf). find.
Ksolve. destruct x0.
  fork1. Keval. apply mℕ_storage. now find.
  fork2. Ksolve. now apply lt_n_Sn. start. apply succℕ_realizer.
  replace (S x0) with (x0 + 1) in Hπ. find. ring.
Qed.

(** *  Equivalent statements  **)

(** **  Subtype equivalent statements  **)

Lemma equiv_fork_inter : (∀A B, A → B → (A ∩ B)) ≈ (∀A B, A → B → A) ∩ (∀A B, A → B → B).
Proof.
apply subtype_eqtype.
  apply sub_inter; subtyping.
  intros π Hπ. dec π. left. find. right. find.
Qed. 

Lemma equiv_inter_Bool : (∀A B, A → B → A) ∩ (∀A B, A → B → B) ≈ 𝔹 0 ∩ 𝔹 1.
Proof.
apply subtype_eqtype; apply inter_sub_compat.
  subtyping.
  subtyping.
  apply sub_Forall_add. intro A. apply sub_Forall_add. intro B.
  etransitivity. apply (sub_Forall _ (fun n : nat => if eq_nat_dec n 0 then A else B)). simpl. reflexivity.
  apply sub_Forall_add. intro A. apply sub_Forall_add. intro B.
  etransitivity. apply (sub_Forall _ (fun n : nat => if eq_nat_dec n 0 then A else B)). simpl. reflexivity.
Qed.

Corollary equiv_fork_Bool : (∀A B, A → B → (A ∩ B)) ≈ 𝔹 0 ∩ 𝔹 1.
Proof.
transitivity ((∀A B, A → B → A) ∩ (∀A B, A → B → B)).
  now apply equiv_fork_inter.
  now apply equiv_inter_Bool.
Qed.

(** **  Universally equivalent statements  **)

(** We prove that having a universal realizer for one of these formulæ gives
    one for all the others, according the following chain:

    [𝔹 0 ∩ 𝔹 1]  ⇒  [∀x, x ∈ ℕ]  ⇒  [∀x, x = 0 ∨ ∃y, x = S y]  ⇒  [(⊥ → ⊤ → ⊥) ∩ (⊤ → ⊥ → ⊥)]  ⇒  [𝔹 0 ∩ 𝔹 1]
**)
Definition fork_rec := λ"fork" Y @ λ"n" "fork" @ (mℕ @ Int 0) @ ("n" @ succℕ).

Lemma equiv_fork_rec : forall e, fork_rec↓e ⊩ (𝔹 0 ∩ 𝔹 1) → ∀x, ℕ x.
Proof.
Ksolve. apply (Y_realizer lt_wf). find.
Ksolve. destruct x0.
  left. exists (fun n : nat => if eq_nat_dec n 0 then ℕ 0 else ⊤). Ksolve.
    Ksolve. apply mℕ_storage. exists 0. now find.
    simpl. ok.
  right. exists (fun n : nat => if eq_nat_dec n 0 then ⊤ else ℕ (S x0)). simpl. Ksolve.
  Ksolve. now apply lt_n_Sn. start. apply succℕ_realizer.
  replace (S x0) with (x0 + 1) in Hπ. find. ring.
Qed.

Definition rec_case := λ"rec" λ"left" λ"right" "rec" @ λ"n" (mℕ @ Int 0) @ ℤeq @ "n"
  @ ("left" @ Id)
  @ ("right" @ λ"f" "f" @ Id).

Lemma equiv_rec_case : forall e, rec_case↓e ⊩ (∀x, ℕ x) → (∀x, x ≡ 0 ∨ ∃y, x ≡ S y).
Proof.
do 2 Ksolve. apply mℕ_storage. exists 0. find.
  start. apply ℕeq_realizer2. exists 0. exists x. find.
  Ksolve.
    Ksolve. subst. start. apply Id_realizer. destruct Hπ as [[Hc0 Hπ] | [Hc0 Hπ]].
      ok.
      now elim Hc0.
    Ksolve. Kmove. exists (pred x). Kmove. start. apply Id_realizer. destruct Hπ as [[Hc0 Hπ] | [Hc0 Hπ]].
      ok.
      elim Hc0. apply (S_pred x 0). omega.
Qed.

Definition case_TopBot := λ"t" λ"x" λ"y" "t" @ (λ"f" "f" @ "x") @ (λ"f" "f" @ λ"g" "g" @ "y").

Lemma equiv_case_TopBot : forall e, case_TopBot↓e ⊩ (∀x, x ≡ 0 ∨ ∃y, x ≡ S y) → (⊥ → ⊤ → ⊥) ∩ (⊤ → ⊥ → ⊥).
Proof.
Kmove.
  exists 0. Ksolve.
    Ksolve. left. now find.
    do 2 Ksolve. right. find. omega.
  exists 1. Ksolve.
    Ksolve. right. find. omega.
    Ksolve. Kmove. destruct y.
      left. now find.
      right. find. omega.
Qed.

Definition TopBot_Bool := λ"t" λ"x" λ"y" callcc @ λ"k" "t" @ ("k" @ "x") @ ("k" @ "y").

Lemma equiv_TopBot_Bool : forall e, TopBot_Bool↓e ⊩ (⊥ → ⊤ → ⊥) ∩ (⊤ → ⊥ → ⊥) → 𝔹 0 ∩ 𝔹 1.
Proof. unfold 𝔹. Ksolve. left. do 2 Ksolve. right. do 2 Ksolve. Qed.

(*
Lemma subtype_Bool_TopBot : 𝔹 0 ∩ 𝔹 1 ⊆ (⊥ → ⊤ → ⊥) ∩ (⊤ → ⊥ → ⊥).
Proof. rewrite <- equiv_inter_Bool. subtyping. Qed.

*)
