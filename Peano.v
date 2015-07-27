(** Realization of Peano arithmetic **)
Require Import Arith_base.
Require Import ClassicalRealizability.Kbase.


Definition Leibniz {T : Type} (a b : T) := ∀Z, Z a → Z b.
Infix "≡" := Leibniz (at level 70).

(** Equality **)

Theorem Peano1 : forall e, Id↓e ⊩ ∀(x : nat), x ≡ x.
Proof. unfold Leibniz. Ksolve. Qed.

Theorem Peano2 : forall e, Id↓e ⊩ ∀(x y : nat), x ≡ y → y ≡ x.
Proof.
unfold Leibniz. Kmove. exists (fun n => if eq_nat_dec n x then Z y else Z x). split.
  destruct (eq_nat_dec x x) as [| Hneq]. ok. now elim Hneq.
  destruct (eq_nat_dec y x); subst; ok.
Qed.

Theorem Peano3 : forall e, Id↓e ⊩ ∀(x y z : nat), x ≡ y → y ≡ z → x ≡ z.
Proof.
unfold Leibniz at 1. Kmove. exists (fun n => if eq_nat_dec n x then y ≡ z else x ≡ z). split.
  destruct (eq_nat_dec x x) as [| Hneq]. ok. now elim Hneq.
  destruct (eq_nat_dec y x); subst; ok.
Qed.

Theorem Peano4 {T : Type} : forall e, Id↓e ⊩ ∀(x y : T), x ≡ y → ∀Z, Z x → Z y.
Proof. Ksolve. Qed.

(** Successor **)

Theorem Peano5 : forall e, Id↓e ⊩ ∀x y, S x ≡ S y → x ≡ y.
Proof. unfold Leibniz. Kmove. exists (fun n => Z (pred n)). do 2 rewrite <- pred_Sn. now split. Qed.

Theorem Peano6 : forall e, nId↓e ⊩ ∀x, ¬(S x ≡ 0).
Proof. unfold Leibniz. Kmove. exists (fun n => if eq_nat_dec n 0 then ⊥ else ⊤). simpl. split; ok. Qed.

(** Addition **)

Theorem Peano7 : forall e, Id↓e ⊩ ∀x, x + 0 ≡ x.
Proof. Ksolve. setoid_rewrite <- plus_n_O in Hπ. unfold Leibniz in *. Ksolve. Qed.

Theorem Peano8 : forall e, Id↓e ⊩ ∀x y, x + S y ≡ S (x + y).
Proof. Ksolve. setoid_rewrite <- plus_n_Sm in Hπ. unfold Leibniz in *. Ksolve. Qed.

(** Multiplication **)

Theorem Peano9 : forall e, Id↓e ⊩ ∀x, x * 0 ≡ 0.
Proof. Ksolve. setoid_rewrite <- mult_n_O in Hπ. unfold Leibniz in *. Ksolve. Qed.

Theorem Peano10 : forall e, Id↓e ⊩ ∀x y, x * S y ≡ x * y + x.
Proof. Ksolve. setoid_rewrite <- mult_n_Sm in Hπ. unfold Leibniz in *. Ksolve. Qed.

(** Recurrence axiom **)

Definition Nat n := ∀Z, Z 0 → (∀m, Z m → Z (S m)) → Z n.
Notation "n ∈ 'Nat'" := (Nat n) (at level 0, no associativity).

(**  Cannot be proven directly as we do not have access to two realizability models at once. **)
Theorem noRealizer : (forall p p₁ p₂, p ≻ p₁ -> p ≻ p₂ -> p₁ ⪰ p₂ \/ p₂ ⪰ p₁) -> forall t, ~(t ⊩ ∀n, n ∈ Nat).
Proof.
intros determinism t Habs.
pose (P π n := if eq_nat_dec n 0 then dot π else ⊤).
pose (Q π n := if eq_nat_dec n 0 then ⊤ else dot π).
Abort.
