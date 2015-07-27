Require Import ClassicalRealizability.Tactics.


(*************************************)
(** *  First realizability results  **)
(*************************************)

Lemma Fvalue_Bot : forall π, π ∈ ‖⊥‖.
Proof. intro. ok. Qed.

Lemma Tvalue_Top : forall t, t ⊩ ⊤.
Proof. intro. ok. Qed.

Lemma Id_realizer_by_hand : forall e, Id↓e ⊩ one.
Proof.
unfold one, Id.
intros e π Hπ.
destruct Hπ as [Z Hπ].
destruct π as [|t π'].
  contradiction Hπ.
  destruct Hπ as [Ht Hπ'].
  apply anti_evaluation with (t★π').
    apply red_trans with ("x"↓("x"←t;e) ★ π').
      apply red_Lam.
      apply red_Var.
    apply Ht.
    assumption.
Qed.

Lemma Id_realizer_intermediate : forall e, Id↓e ⊩ one.
Proof.
unfold one, Id.
intros e π Hπ.
dec π.
Kevals.
apply Ht.
assumption.
Qed.

Theorem Id_realizer : forall e, Id↓e ⊩ one.
Proof. unfold one. Ksolve. Qed.

Theorem modus_ponens : forall A B, forall t t' e, t↓e ⊩ A → B -> t'↓e ⊩ A -> t @ t'↓e ⊩ B.
Proof. Ksolve. Qed.

Theorem Impl_eta_realizer :
  forall A B t e, (forall t' e, t'↓e ⊩ A -> t @ t'↓e ⊩ B) -> (λ"x" t @ "x")↓e ⊩ A → B.
Proof. intros A B t e Ht. startn 1. apply (Ht "x"); Ksolve. Qed.

Theorem uniform_Forall : forall (T : Type) (F : T -> formula) t, (t ⊩ ∀n, F n) <-> forall n, t ⊩ F n.
Proof. intros F t. split; intro Ht; Ksolve. now apply (Ht n). Qed.

Lemma k_realizer : forall A B, forall π, π ∈ ‖A‖ -> k[π] ⊩ A → B.
Proof. Ksolve. Qed.

Lemma ex_falso : forall t, forall A, t ⊩ ⊥ -> t ⊩ A.
Proof. Ksolve. Qed.

Theorem callcc_realizes_Peirce : forall e, callcc↓e ⊩ ∀A B, ((A → B) → A) → A.
Proof. Ksolve. now apply k_realizer. Qed.

Theorem excluded_middle : forall e, em↓e ⊩ ∀F, F ∨ ¬F.
Proof. repeat Ksolve. Qed.

Lemma mapsto_equiv : forall c A t, (t ⊩ c ↦ A) <-> (c -> t ⊩ A).
Proof. intros c A t. split; intro Ht. Ksolve. start. now apply Ht. Qed.


(** Turing's fixpoint **)
Theorem Y_realizer T (R : T -> T -> Prop) (Hwf : well_founded R) :
  forall e, Y↓e ⊩ ∀P, (∀x, (∀y, R y x ↦ P y) → P x) → ∀z, P z.
Proof.
intro e. start. revert z π Hπ. induction z as [z Hrec] using (well_founded_ind Hwf); intros.
apply Ht. find. start. eapply Hrec; eok.
Qed.
Arguments Y_realizer [T R] Hwf e π _.

(** Relativized version of Y **)
Definition Y_rel := λ"f" Y @ (λ"x" λ"y" "f" @ "y" @ "x").

Theorem Y_rel_realizer (T : Type) (R : T -> T -> Prop) (Hwf : well_founded R) (rel : T -> formula) :
  forall e, Y_rel↓e ⊩ ∀P, (∀x, rel x → (∀y, rel y → R y x ↦ P y) → P x) → ∀z, rel z → P z.
Proof. intro. startn 2. apply (Y_realizer Hwf). exists (fun t => rel t → P t). repeat Ksolve. Qed.
Arguments Y_rel_realizer [T R] Hwf rel e π _.


(** **  Some specification results  **)

Definition redeq := fun p p' => p = p' \/ p ≻ p'.
Notation "p ⪰ p'" := (redeq p p') (at level 70).
Definition dot (π : Π) : formula := fun π' => π' = π.

Lemma  non_confusion : forall t π, t·π <> π.
Proof.
intros t π. induction π.
  discriminate.
  intro Habs. apply IHπ. inversion Habs. now rewrite H1.
Qed.

Lemma non_confusion2 : forall t u π, t·u·π <> π.
Proof.
intros t u π. revert t u. induction π.
  discriminate.
  intros t u Habs. inversion Habs. subst t. apply (IHπ _ _ H1).
Qed.

Lemma redeq_red : forall p p', p <> p' -> p ⪰ p' -> p ≻ p'.
Proof. intros p p' Hp []; intuition. Qed.

(** ***  Specification of [one]  **)

Theorem specification_1_easy : forall t, (forall u π, t ★ u·π ≻ u ★ π) -> t ⊩ one.
Proof. intros t Ht. unfold one. Kmove. eapply anti_evaluation. apply Ht. ok. Qed.

Section Spec_1.
  Variables (u : Λ) (π : Π).
  Hypothesis Hpole : forall p, p ∈ ⫫ <-> p ⪰ u ★ π.
  
  Theorem specification_1 : forall t, (t ⊩ one) -> t ★ u·π ≻ u ★ π.
  Proof.
  intros t Ht.
  apply redeq_red. intro H. inversion H. eelim non_confusion. eassumption.
  rewrite <- Hpole. apply Ht. exists (dot π). Ksolve.
  Ksolve. compute in Hπ. subst. rewrite Hpole. now left.
  Qed.
End Spec_1.

(** *** Specification of [⊥ → ⊥]  **)

Theorem specification_bot_impl_bot_easy : forall t, (forall u π, exists π', t ★ u·π ⪰ u ★ π') -> t ⊩ ⊥ → ⊥.
Proof.
intros t Ht. Ksolve. destruct (Ht t0 π) as [π' [Hπ' | Hπ']].
  rewrite Hπ'. Kmove.
  eapply anti_evaluation. apply Hπ'. Kmove.
Qed.

Section Spec_bot_impl_bot.
  Variables (u : Λ) (π : Π).
  Hypothesis Hpole : forall p, p ∈ ⫫ <-> exists π', p ⪰ u ★ π'.
  
  Lemma specification_bot_impl_bot_with_eq : forall t, (t ⊩ ⊥ → ⊥) -> exists π', t ★ u·π ⪰ u ★ π'.
  Proof.
  intros t Ht.
  assert (t ★ u·π ∈ ⫫) as Hbot.
    Ksolve. start. rewrite Hpole. exists π. now left.
  rewrite Hpole in Hbot. destruct Hbot as [π' Hbot].
  now exists π'.
  Qed.
End Spec_bot_impl_bot.

