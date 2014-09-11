Require Import ShallowEmbedding.
Require Import Tactics.
Require Import BasicResults.
Require Import RelationClasses.
Require Import Morphisms.
Set Implicit Arguments.


(****************************)
(** *  Subtyping relation  **)
(****************************)

(** **  Definition of the subtype and subtyping equivalence relations  **)

Definition subtype F F' := forall π, π ∈ ‖F'‖ -> π ∈ ‖F‖.
Notation  "A '⊆' B" := (subtype A B) (at level 80, no associativity).
Transparent subtype.

Definition eqtype F F' := forall π, π ∈ ‖F‖ <-> π ∈ ‖F'‖.

Notation "A '≈' B" := (eqtype A B) (at level 80, no associativity).

(** ** Instances for rewriting **)

(** [A ≈ B] is the equivalence associated with the preorder [A ⊆ B] **)
Instance Eqtype_extensional : Proper (eqtype ==> eq ==> iff) Fval.
Proof. intros A B Heq π π' Heqπ. split; intros Hπ; subst; now rewrite (Heq π') || rewrite <- (Heq π'). Qed.

Instance realizes_iff_compat : Proper (eq ==> eqtype ==> iff) realizes.
Proof.
intros t t' Heqt A B Heq.
split; intros Ht π Hπ; subst; apply Ht; now apply (Eqtype_extensional Heq eq_refl).
Qed.

Instance realizes_impl_compat : Proper (eq ==> subtype ==> Basics.impl) realizes.
Proof. intros t t' Heqt A B Hsub Ht. intros π Hπ. subst. apply Ht. now apply Hsub. Qed.

Instance Subtype_PreOrder : PreOrder subtype.
Proof. repeat split. now intros ? ? ?. intros A B C HAB HBC π Hπ. apply HAB. now apply HBC. Qed.

Instance Eqtype_equiv : Equivalence eqtype.
Proof.
split.
  intros F s. reflexivity.
  intros A B Heq s. now rewrite Heq.
  intros A B C HAB HBC s. rewrite HAB. now rewrite HBC.
Qed.

Instance Subtype_PO : PartialOrder eqtype subtype.
Proof.
intros x y; split; intro Heq.
  split; intros π Hπ. now rewrite Heq. now rewrite <- Heq.
  destruct Heq as [H₁ H₂]. split; now apply H₁ || apply H₂.
Qed.

Lemma eqtype_subtype : forall A B, A ≈ B -> A ⊆ B.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma subtype_eqtype : forall A B, A ⊆ B -> B ⊆ A -> A ≈ B.
Proof. intros A B HAB HBA s. split; intro Hπ; now (apply HAB || apply HBA). Qed.

(*
(** The connectives respects subtyping. **)
Instance Forall_proper (T : Type) : Proper (pointwise_relation T subtype ==> subtype) (Forall T).
Proof. intros A B HAB π [t Hπ]. exists t. now apply (HAB t). Qed.

Instance mapsto_Proper : Proper (Impl ==> subtype ==> subtype) mapsto.
Proof. intros c₁ c₂ Hcs A B HAB π [Hc Hπ]. split. now rewrite Hcs. now apply HAB. Qed.

Lemma eqtype_subtype : forall A B, A ≈ B -> A ⊆ B.
Proof. intros. rewrite H. reflexivity. Qed.
*)


(** ** Usual properties of a subtyping relation **)

(** Propositional constants **)
Lemma sub_bot : forall F, ⊥ ⊆ F.
Proof. Ksolve. Qed.

Lemma sub_top : forall F, F ⊆ ⊤.
Proof. Ksolve. Qed.

Lemma top_bot_sub_one : (⊤ → ⊥) ⊆ one.
Proof. unfold one. Ksolve. Qed.

(** Implication **)
Lemma sub_Impl : forall A A' B B', A ⊆ A' -> B ⊆ B' -> A' → B ⊆ A → B'.
Proof. intros A A' B B' HA HB. start. split. start. apply Ht. now apply HA. now apply HB. Qed.

(** Universal quantification **)
Lemma sub_Forall : forall T A (t : T), (∀x, A x) ⊆ A t.
Proof. Ksolve. Qed.

Lemma Forall_sub_compat : forall T A B, (forall x : T, A x ⊆ B x) -> (∀x, A x) ⊆ ∀x, B x.
Proof. intros T A B Hsub π [n Hn]. exists n. now apply Hsub. Qed.

Lemma sub_Forall_add : forall T A (B : T -> formula), (forall t, A ⊆ B t) -> A ⊆ ∀t, B t.
Proof. intros T A B HAB π [t Hπ]. now apply (HAB t). Qed.

Lemma sub_Forall_cross : forall T A (B : T -> formula), (∀t, A → B t) ≈ A → ∀t, B t.
Proof. intros; split; Ksolve. Qed.

Lemma Forall_comm : forall T₁ T₂ (A : T₁ -> T₂ -> formula), (∀t, ∀u, A t u) ≈ ∀u, ∀t, A t u.
Proof. intros ? ? ? π; split; intro; dec π; find. Qed.

Lemma Forall_cancel : forall T A, inhabited T -> (∀t : T, A) ≈ A.
Proof. intros T A [] π; split; intro; dec π; find; ok. Qed.

(** Semantic implication **)
Lemma sub_mapsto : forall A c, A ⊆ c ↦ A.
Proof. now intros ? ? ? []. Qed.

Lemma mapsto_sub_compat : forall (c c' : Prop) A B, (c' -> c) -> A ⊆ B -> c ↦ A ⊆ c' ↦ B.
Proof. intros c c' A B Hcs HAB π [Hc Hπ]. split. now apply Hcs. now apply HAB. Qed. 

Lemma mapsto_cancel : forall c A, (c ↦ A) ∩ (~c ↦ A) ≈ A.
Proof.
intros c A π. split; intro Hπ.
  now destruct Hπ as [[]|[]].
  elim (Classical_Prop.classic c); intro Hc; (now left; split) || (now right; split).
Qed.

Lemma mapsto_idempotent : forall c A, c ↦ c ↦ A ≈ c ↦ A.
Proof. intros. apply subtype_eqtype. now intros ? []; repeat split. apply sub_mapsto. Qed.

Instance mapsto_eqtype_compat : Proper (iff ==> eqtype ==> eqtype) mapsto.
Proof.
intros c c' Hc A B HAB π.
split; (apply mapsto_sub_compat; [now intuition | apply eqtype_subtype]); assumption || now symmetry.
Qed.

Instance mapsto_subtype_compat : Proper (Basics.flip Basics.impl ==> subtype ==> subtype) mapsto.
Proof. intros c c' Hc A B HAB. now apply mapsto_sub_compat. Qed.

(** Intersection type **)
Lemma sub_inter_l : forall A B, A ∩ B ⊆ A.
Proof. intros. now left. Qed.

Lemma sub_inter_r : forall A B, A ∩ B ⊆ B.
Proof. intros. now right. Qed.

Lemma sub_inter : forall A B C, C ⊆ A -> C ⊆ B -> C ⊆ A ∩ B.
Proof. intros A B C HA HB ? [? | ?]. now apply HA. now apply HB. Qed.

Lemma inter_sub_compat : forall A A' B B', A ⊆ A' -> B ⊆ B' -> A ∩ B ⊆ A' ∩ B'.
Proof. intros A A' B B' HA HB ? [? | ?]. now left; apply HA. now right; apply HB. Qed.

Lemma inter_mapsto_distr : forall c A B, c ↦ (A ∩ B) ≈ (c ↦ A) ∩ (c ↦ B).
Proof.
intros c A B s. split; intro Hπ.
  destruct Hπ as [Hc [Hπ | Hπ]]. now left; split. now right; split.
  destruct Hπ as [[Hc Hπ] | [Hc Hπ]]. now split; try left. now split; try right.
Qed.

(** Interactions between subtpying and realizability **)
Theorem sub_stack : forall A B π, π ∈ ‖B‖ -> A ⊆ B -> π ∈ ‖A‖.
Proof. auto. Qed.
Arguments sub_stack [A] [B] [π] Hπ HAB.

Theorem sub_term : forall A B t, t ⊩ A -> A ⊆ B -> t ⊩ B.
Proof. intros A B t Ht HAB. start. apply Ht. now apply HAB. Qed.

Theorem sub_id : forall A B, A ⊆ B -> forall e, Id↓e ⊩ A → B.
Proof. intros ? ? H. Ksolve. now apply H. Qed.


(** ** Automatization **)

(* FIXME(speedup): use Hint Extern to speclialize the patterns on which each case is used
   BUG 3199 !! *)
Create HintDb Ksubtype.
Hint Opaque subtype eqtype : Ksubtype.
Hint Immediate (@reflexivity _ subtype _) (@reflexivity _ eqtype _) sub_Forall sub_bot sub_mapsto : Ksubtype.
Hint Immediate mapsto_cancel mapsto_idempotent inter_mapsto_distr : Ksubtype.

Hint Resolve sub_Impl sub_inter_l sub_inter_r sub_inter sub_Forall_add sub_Forall_cross : Ksubtype.
Hint Resolve Forall_sub_compat mapsto_sub_compat inter_sub_compat : Ksubtype.
(*
Check sub_Impl.
Hint Extern 2 ((_ → _) ⊆ (_ → _)) => eapply sub_Impl : Ksubtype.
Hint Extern 0 ((_ ∩ _) ⊆ _) => apply sub_inter_l : Ksubtype.
Hint Extern 0 ((_ ∩ _) ⊆ _) => apply sub_inter_r : Ksubtype.
Hint Extern 2 (_ ⊆ (_ ∩ _)) => apply sub_inter : Ksubtype.
Hint Extern 1 (_ ⊆ (∀_, _)) => apply sub_Forall_add : Ksubtype.
Hint Resolve sub_Forall_cross : Ksubtype.
Hint Extern 1 ((∀_, _) ⊆ (∀_, _)) => apply Forall_sub_proper : Ksubtype.
Hint Extern 2 ((_ ↦ _) ⊆ (_ ↦ _)) => apply mapsto_sub_proper : Ksubtype.
Hint Extern 2 ((_ ∩ _) ⊆ (_ ∩ _)) => apply inter_sub_proper : Ksubtype.
*)
Hint Resolve sub_term sub_stack (@transitivity _ subtype _) : Ksubtype.
Hint Extern 1 (_ ⊆ _) => apply top_bot_sub_one; trivial : Ksubtype. (* avoid unfolding of ⊆ *)
Hint Extern 5 (_ ⊆ _) => apply eqtype_subtype : Ksubtype.
Hint Extern 6 (_ ≈ _) => apply subtype_eqtype : Ksubtype.
Hint Extern 7 (_ ≈ _) => apply (@symmetry _ eqtype _) : Ksubtype.   (* high cost to avoid excessive use *)
(* Currently useless because of bug 3199 *)

(** The tactic solving subtyping goals **)
Ltac subtyping := progress eauto 6 with Ksubtype.

(** Same as [subtyping] but displays proof search information **)
Ltac info_subtyping := progress info_eauto 6 with Ksubtype.


(** **  Some examples  **)

Example inter_idempotent : forall A, A ∩ A ≈ A.
Proof. subtyping. Qed. (* BUG 3199: symmetry used twice for nothing *) 

Example callcc_realizes_NNPP : forall e, callcc↓e ⊩ ∀P, (¬¬P) → P.
Proof. intro e. apply (sub_term (callcc_realizes_Peirce e)). subtyping. Qed.

Lemma inter_realizer : forall A B t e, t↓e ⊩ A∩B <-> t↓e ⊩ A /\ t↓e ⊩ B.
Proof.
intros A B t e. split; intro Ht.
  split; subtyping.
  destruct Ht as [Ht₁ Ht₂]. start; (now apply Ht₁) || (now apply Ht₂).
Qed.
