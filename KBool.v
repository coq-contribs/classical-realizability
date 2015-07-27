Require Import Setoid.
Require Import Arith.Peano_dec.
Require Import ClassicalRealizability.Kbase.


Definition 𝔹 b := ∀Z, Z 0 → Z 1 → Z b.
Definition Bool := ∀Z, Z → Z → Z.
Definition Ktrue := λ"x" λ"y" "y".
Definition Kfalse := λ"x" λ"y" "x".

Lemma 𝔹_Bool_subtype : forall b, 𝔹 b ⊆ Bool.
Proof. unfold 𝔹, Bool. intro b. apply sub_Forall_add. intro Z. intros π Hπ. now exists (fun _ => Z). Qed.

Lemma Ktrue_realizer : forall e, Ktrue↓e ⊩ 𝔹 1.
Proof. unfold 𝔹. Ksolve. Qed.

Lemma Kfalse_realizer : forall e, Kfalse↓e ⊩ 𝔹 0.
Proof. unfold 𝔹. Ksolve. Qed.

(** **  Specification of Booleans  **)

(** ***  True-like booleans  **)

Theorem specification_true_like_easy : forall t, (forall u v π, t ★ u·v·π ≻ v ★ π) -> t ⊩ 𝔹 1.
Proof. intros t Ht. unfold 𝔹. Kmove. eapply anti_evaluation. apply Ht. Kmove. Qed.

Section Spec_True_like.
  Variables (u v : Λ) (π : Π).
  Hypothesis Hpole : forall p, p ∈ ⫫ <-> p ⪰ v ★ π.
  
  Theorem specification_true_like : forall t, t ⊩ 𝔹 1 -> t ★ u·v·π ≻ v ★ π.
  Proof.
  intros t Ht. apply redeq_red. intro Habs. inversion Habs. eelim non_confusion2. eassumption.
  rewrite <- Hpole. apply Ht. exists (fun n => if eq_nat_dec n 0 then ⊤ else dot π). simpl. Ksolve.
  Ksolve. rewrite Hpole. left. compute in Hπ. now subst.
  Qed.
End Spec_True_like.

(** ***  False-like booleans  **)

Theorem specification_false_like_easy : forall t, (forall u v π, t ★ u·v·π ≻ u ★ π) -> t ⊩ 𝔹 0.
Proof. intros t Ht. unfold 𝔹. Kmove. eapply anti_evaluation. apply Ht. Kmove. Qed.

Section Spec_False_like.
  Variables (u v : Λ) (π : Π).
  Hypothesis Hpole : forall p, p ∈ ⫫ <-> p ⪰ u ★ π.
  
  Theorem specification_false_like : forall t, t ⊩ 𝔹 0 -> t ★ u·v·π ≻ u ★ π.
  Proof.
  intros t Ht. apply redeq_red. intro Habs. inversion Habs. eelim non_confusion2. eassumption.
  rewrite <- Hpole. apply Ht. exists (fun n => if eq_nat_dec n 0 then dot π else ⊤). simpl. Ksolve.
  Ksolve. rewrite Hpole. left. compute in Hπ. now subst.
  Qed.
End Spec_False_like.

(** ***  General type Bool  **)

Theorem specification_Bool_easy : forall t,
  (forall u v π, t ★ u·v·π ≻ u ★ π \/ t ★ u·v·π ≻ v ★ π) -> t ⊩ Bool.
Proof.
intros t Ht. unfold Bool. Ksolve.
destruct (Ht t0 t1 π) as [Hred | Hred]; eapply anti_evaluation; now apply Hred || Ksolve.
Qed.

Section Spec_Bool.
  Variables (u v : Λ) (π : Π).
  Hypothesis Hpole : forall p, p ∈ ⫫ <-> p ⪰ u ★ π \/ p ⪰ v ★ π.
  
  Theorem specification_Bool : forall t, t ⊩ Bool -> t ★ u·v·π ≻ u ★ π \/ t ★ u·v·π ≻ v ★ π.
  Proof.
  intros t Ht.
  setoid_replace (t ★ u·v·π ≻ u ★ π) with (t ★ u·v·π ⪰ u ★ π).
  setoid_replace (t ★ u·v·π ≻ v ★ π) with (t ★ u·v·π ⪰ v ★ π).
  rewrite <- Hpole. apply Ht. exists (dot π). Ksolve.
  Ksolve. compute in Hπ. subst. rewrite Hpole. now do 2 left.
  Ksolve. compute in Hπ. subst. rewrite Hpole. now right; left.
  unfold redeq. intuition. inversion H0. eelim non_confusion2. eassumption.
  unfold redeq. intuition. inversion H0. eelim non_confusion2. eassumption.
  Qed.
End Spec_Bool.
