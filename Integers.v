Require Import ZArith.
Require Import ClassicalRealizability.Kbase.

Arguments Z.sub !m !n.
Arguments Z.add !x !y.


(***************************)
(** *   Native integers   **)
(***************************)


(** Hypotheses: native operations on primitive integers
    
    We choose to let [Int] return an [intruction] instead of a [Λ]
    in order to be allowed to write constants inside terms.
 **)
Parameter Int : Z -> instruction.
Parameter ℤeq ℤle ℤadd ℤsub ℤmul ℤdiv : instruction.


Section Axioms.
Variables (e e' e'' : env) (n m : Z) (u v k : Λ) (π : Π).

Axiom red_ℤeq : ℤeq↓e ★ Int n↓e'·Int m↓e''·u·v·π ≻ (if Z_eq_dec n m then u else v) ★ π.
Axiom red_ℤle : ℤle↓e ★ Int n↓e'·Int m↓e''·u·v·π ≻ (if Z_le_dec n m then u else v) ★ π.
Axiom red_ℤadd : ℤadd↓e ★ Int n↓e'·Int m↓e''·k·π ≻ k ★ Int (n+m)↓∅ · π.
Axiom red_ℤsub : ℤsub↓e ★ Int n↓e'·Int m↓e''·k·π ≻ k ★ Int (n-m)↓∅ · π.
Axiom red_ℤmul : ℤmul↓e ★ Int n↓e'·Int m↓e''·k·π ≻ k ★ Int (n*m)↓∅ · π.
Axiom red_ℤdiv : ℤdiv↓e ★ Int n↓e'·Int m↓e''·k·π ≻ k ★ Int (n/m)↓∅ · π.
End Axioms.

Definition IntArg n F := fun π => exists e, exists π', π = Int n↓e·π' /\ π' ∈ ‖F‖.
Notation "'{' n '}' '→' F" := (IntArg n F).

Definition ℤ n : formula := ∀Z, ({n} → Z) → Z.

(** ** Tactics for manipulating primitive integers inside specifications **)

Global Ltac int_Keval tac :=
  lazymatch goal with
    | [ |- Cst ℤeq↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?u·?v·?s ∈ ⫫] => Debug "Keval_ℤeq";
         apply anti_evaluation with ((if Z_eq_dec n₁ n₂ then u else v) ★ s); [now apply red_ℤeq | simpl Z_eq_dec]
    | [ |- Cst ℤle↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?u·?v·?s ∈ ⫫] => Debug "Keval_ℤle";
         apply anti_evaluation with ((if Z_le_dec n₁ n₂ then u else v) ★ s); [now apply red_ℤle | simpl Z_le_dec]
    | [ |- Cst ℤadd↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?k·?s ∈ ⫫] => Debug "Keval_ℤadd";
         apply anti_evaluation with (k ★ Cst (Int (n₁+n₂))↓∅·s); [now apply red_ℤadd |]
    | [ |- Cst ℤsub↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?k·?s ∈ ⫫] => Debug "Keval_ℤsub";
         apply anti_evaluation with (k ★ Cst (Int (n₁-n₂))↓∅·s); [now apply red_ℤsub |]
    | [ |- Cst ℤmul↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?k·?s ∈ ⫫] => Debug "Keval_ℤmul";
         apply anti_evaluation with (k ★ Cst (Int (n₁*n₂))↓∅·s); [now apply red_ℤmul |]
    | [ |- Cst ℤdiv↓ _ ★ Cst (Int ?n₁)↓ _·Cst (Int ?n₂)↓ _·?k·?s ∈ ⫫] => Debug "Keval_ℤdiv";
         apply anti_evaluation with (k ★ Cst (Int (n₁/n₂))↓∅·s); [now apply red_ℤdiv |]
(*    | [ |- Zn n↓ _ ★ _ ] => apply Zn_realizer*)
    | _ => Debug "Keval_next"; tac
  end.

Global Ltac int_dstack tac Hπ :=
  lazymatch type of Hπ with
    | ?π ∈ ‖{?e} → ?F‖ =>
      let e := fresh "e" in let t := fresh "t" in let n := fresh "n" in
      let π' := fresh "π" in let Heq := fresh "Heq" in 
      destruct Hπ as [e [π' [Heq Hπ]]]; destruct π as [| t π]; inversion Heq; subst t π'; clear Heq
    | _ => tac Hπ
  end.

Global Ltac Keval ::= basic_Keval ltac:(idtac; int_Keval fail).
Global Ltac dstack ::= basic_dstack ltac:(int_dstack ltac:(prop_dstack fail)).


(** ** Storage operator **)

(** Relativization is trivial **)
Global Instance Rel_ℤ : Relativisation ℤ := now_Rel ℤ (fun f t => {t} → f t).
Global Hint Unfold Rel_ℤ : Krivine.

Lemma ℤrelativization_hint : forall n A, (∀₁x∈ℤ, A x) ⊆ {n} → A n.
Proof. intros n A. start. find. Qed.
Hint Resolve ℤrelativization_hint : Ksubtype.

(** Storage operator **)
Definition Mℤ := λ"f" λ"n" "n" @ "f".

Property Mℤ_storage : forall e, Mℤ↓e ⊩ ∀n, ∀Z, ({n} → Z) → (ℤ n → Z).
Proof. Ksolve. Qed.

Definition mℤ := λ"n" λ"f" "f" @ "n".
Property mℤ_storage : forall e, mℤ↓e ⊩ ∀n, {n} → ℤ n.
Proof. unfold ℤ. Ksolve. Qed.


(** **  Operations on primitive integers  **)

(** Formulæ realized by the native operations **)

Lemma ℤadd_realizer : forall e, ℤadd↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (n+m).
Proof. unfold ℤ. Ksolve. Qed.
Lemma ℤsub_realizer : forall e, ℤsub↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (n-m).
Proof. unfold ℤ. Ksolve. Qed.
Lemma ℤmul_realizer : forall e, ℤmul↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (n*m).
Proof. unfold ℤ. Ksolve. Qed.
Lemma ℤdiv_realizer : forall e, ℤdiv↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (n/m).
Proof. unfold ℤ. Ksolve. Qed.


(** **  Comparisons of primitive integers **)

Notation "n '≡' m" := (prop (Z.eq n m)) (at level 70) : Z_scope.
Notation "n '≤' m" := (prop (Z.le n m)) (at level 70) : Z_scope.
Notation "n '<<' m" := (prop (Z.lt n m)) (at level 70) : Z_scope.
Notation "n '≥' m" := (prop (Z.ge n m)) (at level 70) : Z_scope.
Notation "n '>>' m" := (prop (Z.gt n m)) (at level 70) : Z_scope.

(* We need to choose between two definitions for case distinctions:
   [if Rdec n m then A else B]   or   [R n m ↦ A ∩ (~R n m) ↦ B]
   We choose the second one because it removes the need of decidability in programs *)

Lemma ℤeq_realizer : forall e,
  ℤeq↓e ⊩ ∀₂n,m∈ℤ×ℤ, ∀ A B, (n = m ↦ A) → (~n = m ↦ B) → (n = m ↦ A) ∩ (~n = m ↦ B).
Proof. intro e. start; destruct (Z.eq_dec n m); Ksolve; contradiction. Qed.

Lemma ℤeq_realizer2 : forall e, ℤeq↓e ⊩ ∀₂n,m∈ℤ×ℤ, ∀ A, (n = m ↦ A) → (~n = m ↦ A) → A.
Proof.  intro e. start; destruct (Z.eq_dec n m); Ksolve. Qed.

Lemma ℤle_realizer : forall e,
  ℤle↓e ⊩ ∀₂n,m∈ℤ×ℤ, ∀ A B, ((n <= m)%Z ↦ A) → ((~n <= m)%Z ↦ B) → ((n <= m)%Z ↦ A) ∩ ((~n <= m)%Z ↦ B).
Proof. intro e. start; destruct (Z_le_dec n m); Ksolve; contradiction. Qed.

Lemma ℤle_realizer2 : forall e, ℤle↓e ⊩ ∀₂n,m∈ℤ×ℤ, ∀ A, ((n <= m)%Z ↦ A) → ((~n <= m)%Z ↦ A) → A.
Proof. intro e. start; destruct (Z_le_dec n m); Ksolve. Qed.

Global Opaque inter.


(** ** Derived operations **)

Definition ℤmax := λ"n" λ"m" ℤle @ "n" @ "m" @ (mℤ @ "m") @ (mℤ @ "n").
Definition ℤmin := λ"n" λ"m" ℤle @ "n" @ "m" @ (mℤ @ "n") @ (mℤ @ "m").
Definition ℤopp := ℤsub @ Int 0.
Definition ℤlt := λ"n" λ"m" ℤadd @ Int 1 @ "n" @ ℤle @ "m".

Lemma ℤmax_realizer : forall e, ℤmax↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (Z.max n m).
Proof.
intro e. start. destruct (Z_le_dec n m).
  Kevals. apply mℤ_storage. rewrite Z.max_r in *. find. assumption.
  Kevals. apply mℤ_storage. rewrite Z.max_l in *. find. omega.
Qed.

Lemma ℤmin_realizer : forall e, ℤmin↓e ⊩ ∀₂n,m∈ℤ×ℤ, ℤ (Z.min n m).
Proof.
intro e. start. destruct (Z_le_dec n m).
  Kevals. apply mℤ_storage. rewrite Z.min_l in *. find. assumption.
  Kevals. apply mℤ_storage.  rewrite Z.min_r in *. find. omega.
Qed.

Lemma ℤopp_realizer : forall e, ℤopp↓e ⊩ ∀₁n∈ℤ, ℤ (- n).
Proof. unfold ℤ. Ksolve. Qed.

Lemma ℤlt_realizer : forall e,
  ℤlt↓e ⊩ ∀₂n,m∈ℤ×ℤ, ∀ A B, ((n < m)%Z ↦ A) → ((~n < m)%Z ↦ B) → ((n < m)%Z ↦ A) ∩ ((~n < m)%Z ↦ B).
Proof.
intro. startn 6. apply ℤadd_realizer. find.
  start. apply ℤle_realizer. find. find.
  rewrite mapsto_equiv in Ht |- *. intro. apply Ht. omega.
  rewrite mapsto_equiv in Ht0 |- *. intro. apply Ht0. omega.
  destruct Hπ as [[]|[]]; [left | right]; split; assumption || omega.
Qed.


(*************************)
(** *  Natural numbers  **)
(*************************)


Lemma minus_is_0 : forall n m, n <= m -> n - m = 0.
Proof. intros. omega. Qed.


(** Natural numbers are implemeted as native integers but keep their usual inductive definition in formulæ. **)
Definition ℕ n := ∀Z, ({Z.of_nat n} → Z) → Z.
Instance Rel_ℕ : Relativisation ℕ := now_Rel ℕ (fun f t => {Z.of_nat t} → f t).
Global Hint Unfold Rel_ℕ : Krivine.

Lemma ℕrelativization_hint : forall n A, (∀₁x∈ℕ, A x) ⊆ {Z.of_nat n} → A n.
Proof. intros n A. start. find. Qed.
Hint Resolve ℕrelativization_hint : Ksubtype.

Definition Mℕ := Mℤ.
Property Mℕ_storage : forall e, Mℕ↓e ⊩ ∀n Z, ({Z.of_nat n} → Z) → (ℕ n → Z).
Proof. Ksolve. Qed.

Definition mℕ := mℤ.
Property mℕ_storage : forall e, mℤ↓e ⊩ ∀n, {Z.of_nat n} → ℕ n.
Proof. unfold ℕ. Ksolve. Qed.


(** ** Conversion between ℕ and ℤ **)

Proposition ℕ_ℤ_eqtype : forall k, ℕ k ≈ ℤ (Z.of_nat k).
Proof. reflexivity. Qed.

Lemma ℕ_ℤ_equiv : forall k π, π ∈ ‖ℤ (Z.of_nat k)‖ <-> π ∈ ‖ℕ k‖.
Proof. intros. now rewrite ℕ_ℤ_eqtype. Qed.

Corollary ℕ_ℤ_realizer : forall k t, t ⊩ ℤ (Z.of_nat k) <-> t ⊩ ℕ k.
Proof. intros. now rewrite ℕ_ℤ_eqtype. Qed.

Transparent ℤ.
Lemma ℤ_ℕ_equiv : forall k π, (0 <= k)%Z -> (π ∈ ‖ℕ (Z.to_nat k)‖ <-> π ∈ ‖ℤ k‖).
Proof. intros k π Hk. unfold ℕ,ℤ. now split; Ksolve; rewrite Z2Nat.id in *; try ok. Qed.

Corollary ℤ_ℕ_realizer : forall k t, (0 <= k)%Z -> (t ⊩ ℕ (Z.to_nat k) <-> t ⊩ ℤ k).
Proof. intros k t Hk. unfold ℕ,ℤ. split; Ksolve; rewrite Z2Nat.id in *; ok. Qed.
Opaque ℤ.


(** ** Operations on natural numbers **)

Definition ℕsub := λ"n" λ"m" ℤle @ "n" @ "m" @ (mℕ @ Int 0) @ (ℤsub @ "n" @ "m").

Lemma ℕsub_realizer :  forall e, ℕsub↓e ⊩ ∀₂n,m∈ℕ×ℕ, ℕ (n-m).
Proof.
intro e. start. destruct (Z_le_dec (Z.of_nat n) (Z.of_nat m)).
  rewrite <- Nat2Z.inj_le in *. rewrite minus_is_0 in *. Kevals. apply mℕ_storage. find. easy.
  Kevals. apply ℤsub_realizer. unfold ℕ in *. dec π. find. start. apply Ht.
  find. rewrite <- Nat2Z.inj_sub. reflexivity. omega.
Qed.

Opaque ℤ.
Lemma ℕadd_realizer : forall e, ℤadd↓e ⊩ ∀₂n,m∈ℕ×ℕ, ℕ (n+m).
Proof. unfold ℕ. Ksolve. now rewrite <- Nat2Z.inj_add. Qed.

Lemma ℕmul_realizer : forall e, ℤmul↓e ⊩ ∀₂n,m∈ℕ×ℕ, ℕ (n*m).
Proof. unfold ℕ. Ksolve. now rewrite <- Nat2Z.inj_mul. Qed.


(** **  Comparisons of natural numbers  **)

Lemma ℕeq_realizer : forall e,
  ℤeq↓e ⊩ ∀₂n,m∈ℕ×ℕ, ∀A B, (n = m ↦ A) → (~n = m ↦ B) → (n = m ↦ A) ∩ (~n = m ↦ B).
Proof.
intro e. start. destruct Hπ; destruct (Z.eq_dec (Z.of_nat n) (Z.of_nat m));
rewrite Nat2Z.inj_iff in *; Ksolve; contradiction.
Qed.

Lemma ℕeq_realizer2 : forall e, ℤeq↓e ⊩ ∀₂n,m∈ℕ×ℕ, ∀A, (n = m ↦ A) → (~n = m ↦ A) → A.
Proof.
intro e. start. destruct (Z.eq_dec (Z.of_nat n) (Z.of_nat m));
rewrite Nat2Z.inj_iff in *; Ksolve.
Qed.

Lemma ℕle_realizer : forall e, ℤle↓e ⊩ ∀₂n,m∈ℕ×ℕ,
  ∀A B, (n <= m ↦ A) → (~n <= m ↦ B) → (n <= m ↦ A) ∩ (~n <= m ↦ B).
Proof.
intro e. start. destruct Hπ; destruct (Z_le_dec (Z.of_nat n) (Z.of_nat m));
rewrite <- Nat2Z.inj_le in *; Ksolve; contradiction.
Qed.

Lemma ℕle_realizer2 : forall e, ℤle↓e ⊩ ∀₂n,m∈ℕ×ℕ, ∀A, (n <= m ↦ A) → (~n <= m ↦ A) → A.
Proof.
intro e. start. destruct (Z_le_dec (Z.of_nat n) (Z.of_nat m));
rewrite <- Nat2Z.inj_le in *; Ksolve.
Qed.

Notation "n '≡' m" := (prop (n = m)) (at level 70) : nat_scope.
Notation "n '≤' m" := (prop (n <= m)) (at level 70) : nat_scope.
Notation "n '<<' m" := (prop (n < m)) (at level 70) : nat_scope.
Notation "n ≥ m" := (m ≤ n) (at level 70, only parsing) : nat_scope.
Notation "n '>>' m" := (m < n) (at level 70, only parsing) : nat_scope.


(** ** Derived operations **)

Definition succℕ := λ"n" ℤadd @ "n" @ Int 1.
Definition predℕ := λ"n" ℕsub @ "n" @ Int 1.

Lemma succℕ_realizer : forall e, succℕ↓e ⊩ ∀₁n∈ℕ, ℕ(n+1).
Proof. Ksolve. apply ℕadd_realizer. find. Qed.

Transparent ℤ.
Lemma predℕ_realizer : forall e, predℕ↓e ⊩ ∀₁n∈ℕ, ℕ(n-1).
Proof. Ksolve. apply ℕsub_realizer. find. Qed.

Lemma maxℕ_realizer : forall e, ℤmax↓e ⊩ ∀₂n,m∈ℕ×ℕ, ℕ (max n m).
Proof. Ksolve. unfold ℕ in *. destruct (Z_le_dec _ _).
  Kevals. apply mℤ_storage. findn 3. rewrite Nat2Z.inj_max in *; rewrite Z.max_r in *. now apply Hπ. assumption.
  Kevals. apply mℤ_storage. findn 3. rewrite Nat2Z.inj_max in *. rewrite Z.max_l in *. now apply Hπ. omega.
Qed.

Lemma minℕ_realizer : forall e, ℤmin↓e ⊩ ∀₂n,m∈ℕ×ℕ, ℕ (min n m).
Proof.
intro e. start. unfold ℕ in Hπ. destruct (Z_le_dec _ _).
  Kevals. apply mℤ_storage. rewrite Nat2Z.inj_min in *. rewrite Z.min_l in *. now find. assumption.
  Kevals. apply mℤ_storage. rewrite Nat2Z.inj_min in *. rewrite Z.min_r in *. now find. omega.
Qed.

Global Opaque ℤ ℤmax ℤmin ℤopp ℕ succℕ predℕ.

Definition min_rec f := λ"k" Y @ λ"rec" λ"n" λ"g"
  "g" @ "n" @ (λ"m" @ f @ "m" @ (f @ "n" @ ℤle) @ Id
                                                @ ("k" @ ("rec" @ "m"))).
Definition min_principle f start := callcc @ λ"k" min_rec f @ "k" @ Int (Z.of_nat start).

Theorem min_principle_realizer : forall (f : nat -> nat) (tf : term),
  (forall e, tf↓e ⊩ ∀₁n∈ℕ, ℕ (f n)) ->
  forall start e, (min_principle tf start)↓e ⊩ ∃₁n∈ℕ, ∀₁m∈ℕ, f(n) ≤ f(m).
Proof.
Ksolve. unfold min_rec. Ksolve.
apply (Y_realizer (well_founded_ltof nat f)). unfold ltof.
exists (fun n => {Z.of_nat n} → ∃₁n∈ℕ, ∀₁m∈ℕ, f(n) ≤ f(m)). Ksolve.
start. apply Ht1. find. Ksolve. apply H. find.
  start. apply H. find. start. apply ℤle_realizer2. find. find.
  find. rewrite mapsto_equiv. intro. apply prop_realizer1. omega.
  Ksolve. omega.
Qed.
