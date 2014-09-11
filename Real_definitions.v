Require Import Kbase.
Require Import Rationals.
Close Scope Q_scope.


(************************************)
(** *  Definition of real numbers  **)
(************************************)

Definition Re := Qc -> Qc -> formula.
Delimit Scope Re_scope with Re.
Bind Scope Re_scope with Re.
Open Scope Re_scope.

Definition embed_ℚ_ℝ (q : Qc) : Re := fun ε q' => prop (0 <= ε /\ q = q').
Coercion embed_ℚ_ℝ : Qc >-> Re.

Definition Total (x : Re) := ∀₁ε∈ℚ+*, ∃₁q∈ℚ, x ε q.


(******************************************)
(** *  Usual predicates and comparisons  **)
(******************************************)

Definition RQeq x q := ∀₂ε,q'∈ℚ+×ℚ, x ε q' → |q' - q| ≤ ε.
Definition null x := RQeq x 0.

(** Equalities : syntactic & Cauchy **)
Definition Eeq (x y : Re) := ∀₂ε,q∈ℚ+×ℚ, (x ε q → y ε q) ∧ (y ε q → x ε q).
Infix "≡≡" := Eeq (at level 70) : Re_scope.

Definition Req (x y : Re) := ∀₄ε₁,ε₂,q₁,q₂∈ℚ+×ℚ+×ℚ×ℚ, x ε₁ q₁ → y ε₂ q₂ → |q₁ - q₂| ≤ ε₁ + ε₂.
Infix "≡" := Req : Re_scope.

(** Large order **)
Definition Rle (x y : Re) := ∀₄ε₁,ε₂,q₁,q₂∈ℚ+×ℚ+×ℚ×ℚ, x ε₁ q₁ → y ε₂ q₂ → q₁ ≤ q₂ + ε₁ + ε₂.
Infix "<=" := Rle : Re_scope.

(** Strict order **)
Definition Rlt (x y : Re) :=
  Ex₅ ε₁,ε,ε₂,q₁,q₂ ∈ ℚ+*×ℚ+*×ℚ+*×ℚ×ℚ, {(q₁ + ε₁ + ε + ε₂ <= q₂)%Qc & x ε₁ q₁ ∧ y ε₂ q₂}.
Infix "<<" := Rlt : Re_scope.

(** Apartness (stronger than inequality) **)
Definition apartℝ (x y : Re) :=
  Ex₅ ε₁,ε,ε₂,q₁,q₂ ∈ ℚ+*×ℚ+*×ℚ+*×ℚ×ℚ, {(ε₁ + ε + ε₂ <= |q₁ - q₂|)%Qc & x ε₁ q₁ ∧ y ε₂ q₂}.
Infix "≠" := apartℝ (at level 70, no associativity).

Ltac real_dstack tac Hπ :=
  match type of Hπ with
    | ?π ∈ ‖ ∀r, _ ‖ => destruct Hπ as [r Hπ]
    | ?π ∈ ‖ Eeq _ _ ‖ => unfold Eeq in Hπ
    | ?π ∈ ‖ Req _ _ ‖ => unfold Req in Hπ
    | ?π ∈ ‖ Rlt _ _ ‖ => unfold Rlt in Hπ
    | ?π ∈ ‖ Rle _ _ ‖ => unfold Rle in Hπ
    | _ => tac Hπ
  end.
Ltac dstack ::= basic_dstack ltac:(real_dstack ltac:(rat_dstack ltac:(prop_dstack fail))).

(** **  Relativisation predicates  **)

Definition Cauchy (x : Re) := x ≡ x.

Definition ℝ x := Total x ∧ Cauchy x.
Global Instance Rel_ℝ : Relativisation ℝ := now_Rel ℝ (fun f r => Total r → Cauchy r → f r).
Global Hint Unfold Rel_ℝ : Krivine.

Definition ℝpos r := ℝ r ∧ (0 << r)%Re.
Global Notation "ℝ+*" := ℝpos.
Global Instance Rel_ℝpos : Relativisation ℝpos := now_Rel ℝpos (fun f => Rel (P:= ℝ) (fun r => (0 << r)%Re → f r)).
Global Hint Unfold Rel_ℝpos : Krivine.


Lemma relativize1 : forall A t, (forall e, t↓e ⊩ ∀x, A x) -> forall e, (λ"Tx" λ"Cx" t)↓e ⊩ ∀₁x∈ℝ, A x.
Proof. intros A t Ht e. start. apply Ht. now find. Qed.

Lemma relativize2 : forall A t, (forall e, t↓e ⊩ ∀x, ∀y, A x y) ->
  forall e, (λ"Tx" λ"Cx" λ"Ty" λ"Cy" t)↓e ⊩ ∀₂x,y∈ℝ×ℝ, A x y.
Proof. intros A t Ht e. start. apply Ht. now find. Qed.

Lemma relativize3 : forall A t, (forall e, t↓e ⊩ ∀x, ∀y, ∀z, A x y z) ->
  forall e, (λ"Tx" λ"Cx" λ"Ty" λ"Cy" λ"Tz" λ"Cz" t)↓e ⊩ ∀₃x,y,z∈ℝ×ℝ×ℝ, A x y z.
Proof. intros A t Ht e. start. apply Ht. now find. Qed.

(** **  Definitions of operations  **)

Close Scope Re_scope.

Definition addℝ (x y : Re) : Re := fun ε q =>
  Ex₄ ε₁,ε₂,q₁,q₂ ∈ ℚ+*×ℚ+*×ℚ×ℚ, {ε = ε₁+ε₂ & q = q₁ + q₂ & x ε₁ q₁ ∧ y ε₂ q₂}.
Definition oppℝ (x : Re) : Re := fun ε q => x ε (- q).
Definition mulℝ (x y : Re) : Re := fun ε q => Ex₄ ε₁,ε₂,q₁,q₂ ∈ ℚ+*×ℚ+*×ℚ×ℚ,
  {(|q₁| + (ε₁ + ε₁)) * (ε₂ + ε₂) + (|q₂| + (ε₂ + ε₂)) * (ε₁ + ε₁) <= ε & q = q₁ * q₂ & x ε₁ q₁ ∧ y ε₂ q₂}.
Definition invℝ (x : Re) : Re := fun ε q =>
  Ex₁ ε' ∈ ℚ+*, { ε' < / Qcabs q & ε' <= ε / (q*q + Qcabs q * ε) & x ε' (/q)}.
Infix "+" := addℝ : Re_scope.
Notation "- x" := (oppℝ x) : Re_scope.
Infix "*" := mulℝ : Re_scope.
Notation "/ x" := (invℝ x) : Re_scope.
