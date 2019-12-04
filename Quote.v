Require Import ZArith.
Require Import Classical.
Require Import ClassicalRealizability.Kbase.
Require Import ClassicalRealizability.Integers.


(*********************************)
(** *  The instruction [quote]  **)
(*********************************)

Parameter quote : instruction.
Parameter quote' : instruction.
Parameter enumT : Λ -> nat.
Parameter enumP : Π -> nat.
Parameter Tenum : nat -> Λ.
Parameter Penum : nat -> Π.

Axiom enumT_Tenum : forall t, Tenum (enumT t) = t.
Axiom Tenum_enumT : forall n, enumT (Tenum n) = n.
Axiom enumP_Penum : forall π, Penum (enumP π) = π.
Axiom Penum_enumP : forall n, enumP (Penum n) = n.

Parameter pair : nat -> nat -> nat.
Parameter p1 p2 : nat -> nat.

Axiom surjective_pairing : forall p, pair (p1 p) (p2 p) = p.
Axiom p1_pair : forall n m, p1 (pair n m) = n.
Axiom p2_pair : forall n m, p2 (pair n m) = m.


Axiom red_quote : forall t π e, quote↓e ★ t·π ≻ t ★ Int(Z.of_nat (enumT t))↓∅·π.
Axiom red_quote' : forall t π e, quote'↓e ★ t·π ≻ t ★ Int(Z.of_nat (enumP π))↓∅·π.

(** Simulation of [quote] by [quote'] **)

Parameter π₀ : Π.
Parameter kπ₀ : term. (* trick to internalize k[π] *)
Axiom red_kπ₀ : forall e t π', kπ₀↓e ★ t·π' ≻ t ★ π₀.

Definition MyQuote := λ"t" callcc @ λ"k" kπ₀ @ (quote' @ (λ"n" "k" @ ("t" @ "n")) @ "t").

Definition enumT' (t : Λ) : nat := enumP (t·π₀).
Lemma enumT'_Penum : forall t, Penum (enumT' t) = t·π₀.
Proof. intro. unfold enumT'. now rewrite enumP_Penum. Qed.


Property red_MyQuote : forall t e π, MyQuote↓e ★ t·π ≻ t ★ Int(Z.of_nat (enumT' t))↓∅·π.
Proof.
unfold MyQuote. intros t e π.
repeat Kstep. Kred red_kπ₀.
repeat Kstep. simpl get.
Kred red_quote'.
do 5 Kstep. simpl get.
apply red_Var.
Qed.


(** Simulation of [eq] by [quote'] **)

Definition eq :=
  λ"t" λ"t'" λ"u" λ"v" quote' @ (λ"n" λ"_" quote' @ (λ"m" λ"_" ℤeq @ "n" @ "m" @ "u" @ "v") @ "t'") @ "t".

Lemma eq_realizer_aux : forall t t' u v π e,
  eq↓e ★ t·t'·u·v·π ≻(if Z.eq_dec (Z.of_nat (enumP (t·π))) (Z.of_nat (enumP (t'·π))) then u else v) ★ π.
Proof.
unfold eq. intros.
do 4 Kred red_Lam.
Kred red_AppVar. simpl.
Kred red_App.
Kred red_quote'.
do 2 Kred red_Lam.
Kred red_AppVar. simpl.
Kred red_App.
Kred red_quote'.
do 2 Kred red_Lam.
do 4 Kred red_AppVar. simpl.
apply red_ℤeq.
Qed.

Theorem eq_realizer1 : forall t t' u v π e, t = t' -> eq↓e ★ t·t'·u·v·π ≻ u ★ π.
Proof.
intros. subst t'.
replace (u ★ π) with ((if Z.eq_dec (Z.of_nat (enumP (t·π))) (Z.of_nat (enumP (t·π))) then u else v) ★ π).
now apply eq_realizer_aux.
destruct (Z.eq_dec _ _) as [? | Hneq]. reflexivity. now elim Hneq.
Qed. 

Theorem eq_realizer2 : forall t t' u v π e, t <> t' -> eq↓e ★ t·t'·u·v·π ≻ v ★ π.
Proof.
intros.
replace (v ★ π) with ((if Z.eq_dec (Z.of_nat (enumP (t·π))) (Z.of_nat (enumP (t'·π))) then u else v) ★ π).
now apply eq_realizer_aux.
destruct (Z.eq_dec _ _) as [Heq | Hneq].
  assert (t·π = t'·π) as Hπ. setoid_rewrite <- enumP_Penum. f_equal. now apply Nat2Z.inj.
  inversion Hπ. contradiction.
 reflexivity.
Qed.


(************************************************)
(** *  Realizer of the countable choice axiom  **)
(************************************************)

(** To realize it, we need to use it in the semantic, hence we assume it here. **)
Axiom countable_choice : forall (T U : Type) F, exists Z, forall x : nat, (exists X : T -> U, F x X) -> F x (Z x).

Lemma countable_choice' : forall (T U : Type) F,
  (forall x : nat, exists X : T -> U, F x X) ->
  exists Z, forall x : nat, F x (Z x).
Proof.
intros T U F H. destruct (countable_choice T U F) as [Z HZ].
exists Z. intro x. apply HZ. apply H.
Qed.

Theorem quote'_realizer :
  forall (F : nat -> (nat -> formula) -> formula),
  exists U : nat -> nat -> nat -> formula,
  forall e, quote' ↓e ⊩ ∀x, (∀₁n∈ℕ, F x (U x n)) → ∀X, F x X.
Proof.
intro F.
assert (forall x π, exists R, π ∈ ‖∀X, F x X‖ <-> π ∈ ‖F x R‖) as Hc.
  intros x π. apply NNPP. intro Habs. apply Habs. exists (fun _ => ⊤). split.
    intros [R Hπ]. exfalso. apply Habs. exists R. split; intro; now try exists R.
    intro. find.
assert (forall xπ, exists R, Penum (p2 xπ) ∈ ‖∀X, F (p1 xπ) X‖ <-> Penum (p2 xπ) ∈ ‖F (p1 xπ) R‖) as Hc'.
  intro xπ. apply Hc.
assert (exists U, forall x π, π ∈ ‖∀X, F x X‖ <-> π ∈ ‖F x (U x (enumP π))‖) as HU.
  apply (countable_choice' nat formula
    (fun xπ R => (Penum (p2 xπ)) ∈ ‖∀X : nat -> formula, F (p1 xπ) X‖ <-> (Penum (p2 xπ)) ∈ ‖F (p1 xπ) R‖)) in Hc'.
  destruct Hc' as [U' HU].
  exists (fun x nπ => U' (pair x nπ)).
  intros x π. pose (xπ := pair x (enumP π)). fold xπ.
  rewrite <- (enumP_Penum π). rewrite <-(p2_pair x (enumP π)). fold xπ.
  rewrite <- (p1_pair x (enumP π)). fold xπ. apply HU.
destruct HU as [U HU].
exists U. Ksolve.
apply anti_evaluation with (t ★ Int(Z.of_nat (enumP π))↓∅·π). now apply red_quote'.
Ksolve. rewrite <- HU. find.
Qed.


Theorem contrapositive_countable_choice : forall e,
  λ"x" "x" @ quote'↓e ⊩ ∀F, ∃U, ∀x : nat, ((∀₁n∈ℕ, F x (U x n)) → ∀X : nat -> formula, F x X).
Proof. Kmove. destruct (quote'_realizer F) as [U HU]. find. apply HU. Qed.


(** **  Extensionality scheme  **)

Definition star {T : Type} G := fun X => ∀U, (∀y : T, X y → U y) → (∀y, U y → X y) → G U.
Notation "G °" := (star G) (at level 2, format "G °").
Definition Ext {T : Type } G := ∀X : T -> formula, G X → G° X.
Definition ext := λ"g" λ"u" λ"u'" λ"v" λ"v'" "g" @ (λ"x" "v" @ ("u" @ "x")) @ (λ"x" "u'" @ ("v'" @ "x")).


Lemma ext_realizer : forall (T : Type) (G : (T -> formula) -> formula) e, ext↓e ⊩ Ext G°.
Proof. unfold Ext, star. repeat Ksolve. Qed.

Opaque ℤle ℤeq. 
Definition comp := λ"n" λ"m" λ"x" λ"y" λ"z" ℤle @ "n" @ "m" @ (ℤeq @ "n" @ "m" @ "y" @ "x") @ "z".

Lemma comp_realizer : forall n m A e,
  comp↓e ⊩ {Z.of_nat n} → {Z.of_nat m} → (n < m ↦ A) → (n = m ↦ A) → (n > m ↦ A) → A.
Proof.
intros n m A e. startn 9. apply ℤle_realizer2. findn 6. exists A. find.
  startn 4. apply ℤeq_realizer2. find. now rewrite Nat2Z.inj_iff. Ksolve. omega.
  Ksolve. omega.
Qed.

(** **  Realizer of the countable choice axiom  **)
Definition AC := λ"f" quote' @ (Y @ λ"x" λ"n" callcc @ λ"k"
  "f" @ (λ"v" "v" @ "x" @ "n" @ "k")
      @ (λ"u" λ"x'" λ"n'" λ"k'" comp @ "n" @ "n'" @ ("k" @ ("x'" @ "n")) @ "u" @ ("k'" @ ("x" @ "n'")))).

Theorem AC_realizer : forall F, exists V, forall (x : nat) e,
  AC↓e ⊩ (∀X, (∀y : nat, (V x y → X y)) → (∀y : nat, (X y → V x y)) → F x X) → ∀X, F x X.
Proof.
intro F. destruct (quote'_realizer F) as [U HU].
assert (forall x e, Y↓e ⊩ (∀n, (∀m, m < n ↦ {Z.of_nat m} → F x (U x m)) → {Z.of_nat n} → F x (U x n)) →
                          ∀₁n∈ℕ, F x (U x n)) as Y_realizer_F.
  intros. startn 0. fold Y. apply (Y_realizer Wf_nat.lt_wf). find. now apply Ht. find.
pose (V x y := ∀n, (∀m, m < n ↦ {Z.of_nat m} → F x (U x m)) → {Z.of_nat n} → (¬(F x (U x n))) → U x n y).
exists V. intros x e.
Ksolve. apply HU. find. Kmove. eapply Y_realizer_F. find. Ksolve.
  now do 2 Ksolve.
  unfold V. Ksolve. eapply comp_realizer. find.
    now Ksolve.
    Ksolve. now subst.
    now do 2 Ksolve.
Qed.
