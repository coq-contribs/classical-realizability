Require Import Tactics.
Require Import BasicResults.
Require Import Subtyping.
Require Import LogicalEquivalences.
Require Import Morphisms.


(***********************************)
(** *  Prop embedding into stacks  *)
(***********************************)


Set Implicit Arguments.
(* prop (A -> B) ≤ prop A → prop B  and  prop (∀x A(x)) ≡ ∀x, prop (A(x)) *)
(* I ⊩ prop (∀x, E₁(x) -> ... -> E_n(x)) ≤ ∀x, prop E₁(x) → ... → prop E_n(x)
   and prop E_i(x) = prop (∀Z, Z(e1) -> Z(e2)) = ∀Z, prop (Z(e1)) → prop (Z(e2)) *)

(** If [c] holds, then [prop c] is [one], otherwise it is [⊤ → ⊥]. **)
Definition prop (c : Prop) : formula := fun π => (c /\ π ∈ ‖one‖) \/ (~c /\ π ∈ ‖⊤ → ⊥‖).

Instance prop_eqtype_compat : Proper (iff ==> eqtype) prop.
Proof. intros A B Heq; repeat split; intros; abstract (compute; rewrite Heq || rewrite <- Heq; assumption). Qed.

Ltac prop_dstack tac Hπ :=
  lazymatch type of Hπ with
    | ?π ∈ ‖prop ?c‖ =>
      unfold prop in Hπ; let HA := fresh "HF" in destruct Hπ as [[HA Hπ] | [HA Hπ]]; try contradiction
    | _ => tac Hπ
  end.
Ltac dstack ::= basic_dstack ltac:(prop_dstack fail).

Lemma distr_subtype : forall A B : Prop, prop (A -> B) ⊆ (prop A → prop B).
Proof.
intros A B. start.
  left. split. easy. elim (Classical_Prop.classic A); intro HA.
    exists one. split. start. apply Ht. left. now split. ok.
    exists (⊤ → ⊥). unfold one in *. Ksolve. start. apply Ht. right. repeat split; ok.
 elim (Classical_Prop.classic A); intro HA.
    right. split. tauto. split; ok.
    left. split. tauto. exists (⊤ → ⊥). Ksolve. Ksolve. right. repeat split; ok.
Qed.

Lemma Beckman_eqtype : forall A : nat -> Prop, prop (forall n, A n) ≈ (∀n, prop (A n)).
Proof.
intro A. intros s; split; intro Hs; dec s.
  exists 0. left. split. now apply HF. ok.
  apply not_all_ex_not_proof in HF. destruct HF as [n Hn]. exists n. right. repeat split; ok.
  elim (Classical_Prop.classic (forall n, A n)); intro HA.
    left. now split.
    right. unfold one in Hs. dec s. repeat split; ok.
  right. split. intro Habs. elim HF. now apply Habs. split; ok.
Qed.

Lemma stack_prop_iff : forall c t π, t·π ∈ ‖prop c‖ <-> c /\ t★π ∈ ⫫ \/ ~c.
Proof.
intros c t π. split; intro Hπ.
  dec (t·π); try now right. left. split. ok. unfold one in Hπ. dec (t·π). destruct Hπ as [Ht Hπ]. now apply Ht.
  destruct Hπ as [[Hc Hπ] | Hc].
    left. split. ok. exists (fun s => s = π). split. start. compute in Hπ0. now subst. reflexivity.
    right. repeat split; ok.
Qed.

Theorem prop_realizer1 : forall A : Prop, forall e, A -> Id↓e ⊩ prop A.
Proof. intros. start. now apply Id_realizer. Qed.

Theorem prop_realizer2 : forall A : Prop, forall e, ~A -> nId↓e ⊩ ¬(prop A).
Proof. intros A e HA. start. apply Ht. right. repeat split; ok. Qed.

Theorem prop_realizer1' : forall c : Prop, forall t, c -> t ⊩ prop c -> t ⊩ one.
Proof. intros c t Hc Ht. start. apply Ht. left. now split. Qed.

Theorem prop_realizer2' : forall c t, ~c -> t ⊩ prop c -> t ⊩ ⊤ → ⊥.
Proof. intros c t Hc Ht. start. apply Ht. right. repeat split; ok. Qed.

(** Just like Leibniz equalities, we can use them as guard conditions. **)
Theorem prop_guard : forall c t t' s, (t ⊩ prop c) -> (c -> t' ★ s ∈ ⫫) -> t ★ t'·s ∈ ⫫.
Proof.
intros c t t' s Ht Ht'. elim (Classical_Prop.classic c); intro Hc.
  apply (prop_realizer1' Hc) in Ht. apply Ht. exists (fun s' => s' = s). split.
  start. compute in Hπ. subst. now apply Ht'. reflexivity.
  apply (prop_realizer2' Hc) in Ht. apply Ht. split; ok.
Qed.

Theorem guard : forall c F t t' e, (t↓e ⊩ prop c) -> (t'↓e ⊩ F) -> (t @ t')↓e ⊩ (c ↦ F).
Proof. intros c F t t' e Ht Ht'. start. apply Ht. left. split. ok. exists F. split. ok. now apply Hπ. Qed.

Theorem guard_sub : forall c F e π , π ∈ ‖c ↦ F‖ -> Id↓e·π ∈ ‖prop c → F‖.
Proof. intros c F e π Hπ. destruct Hπ as [Hc Hπ]. split; try ok. now apply prop_realizer1. Qed.

(** Some subtyping results **)
Lemma prop_sub_one : forall c, prop c ⊆ one.
Proof. intro c. start. elim (Classical_Prop.classic c); intro Hc. now left; split. right. split; subtyping. Qed.

Lemma top_bot_sub_prop : forall c, (⊤ → ⊥) ⊆ prop c.
Proof. intro c. start. subtyping. split; ok. Qed.

Theorem prop_subst_stack : forall c c' : Prop, forall s, s ∈ ‖prop c'‖ -> (c -> c') -> s ∈ ‖prop c‖.
Proof.
intros c c' s Hs Hcc'. elim (Classical_Prop.classic c); intro Hc.
  left. split. ok. dec s. ok. absurd c'; tauto.
  right. split. ok. apply (top_bot_sub_prop Hs).
Qed.

Theorem prop_subtype : forall c c' : Prop, (c -> c') -> prop c ⊆ prop c'.
Proof.
intros c c' Hcc' s [[Hc' Hs] | [Hc' Hs]].
  elim (Classical_Prop.classic c); intro Hc. left. split; ok. right. unfold one in *. Ksolve.
  right. split. now auto. ok.
Qed.

Hint Immediate prop_sub_one top_bot_sub_prop : Ksubtype.
Hint Resolve distr_subtype prop_subtype Beckman_eqtype : Ksubtype.

Theorem prop_subst_term : forall c c' : Prop, forall t, t ⊩ prop c -> (c -> c') -> t ⊩ prop c'.
Proof. subtyping. Qed.


Lemma prop_term_destruct : forall t F, t ⊩ prop F -> F /\ t ⊩ one \/ ~F /\ t ⊩ ⊤ → ⊥.
Proof.
intros t F Ht. elim (Classical_Prop.classic F); intro.
  left. subtyping.
  right. split. ok. eapply prop_realizer2'; eassumption.
Qed.

Ltac destruct_prop Ht :=
  match type of Ht with
    | ?t ⊩ prop ?a =>
      apply prop_term_destruct in Ht; let Hc := fresh "Hc" in destruct Ht as [[Hc Ht] | [Hc Ht]]; try contradiction
  end.

Example chain2_prop : forall c₁ c₂ : Prop, forall e, (c₁ -> c₂) -> Id↓e ⊩ prop c₁ → prop c₂.
Proof. intros c₁ c₂ e Hcs. apply (sub_term (prop_realizer1 _ Hcs)). subtyping. Qed.

Example chain3_prop : forall c₁ c₂ c₃ : Prop, forall e, (c₁ -> c₂ -> c₃) -> Id↓e ⊩ prop c₁ → prop c₂ → prop c₃.
Proof. intros c₁ c₂ c₃ e Hcs. apply (sub_term (prop_realizer1 _ Hcs)). subtyping. Qed.

Example chain4_prop :
  forall c₁ c₂ c₃ c₄ : Prop, forall e, (c₁ -> c₂ -> c₃ -> c₄) -> Id↓e ⊩ prop c₁ → prop c₂ → prop c₃ → prop c₄.
Proof. intros c₁ c₂ c₃ c₄ e Hcs. apply (sub_term (prop_realizer1 _ Hcs)). subtyping. Qed.

(** The converse is false because [t ⊩ c₁ → c₂] and [~(c₁ -> c₂)] does not implies [t ⊩ ⊤ → ⊥]
   ([⫫]  is not closed under reduction). **)
Global Opaque prop.
