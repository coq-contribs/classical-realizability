Require Import ClassicalRealizability.Kbase.


(**********************************)
(** *  Primitive pairs and sums  **)
(**********************************)

(** **  Hypotheses: new instructions and their evaluation rules  **)

Parameter cpl : Λ -> Λ -> Λ.
Parameter ι₁ ι₂ : Λ -> Λ.
Parameter pair proj1 proj2 inj1 inj2 case : instruction.
Notation "<| t , u |>" := (cpl t u).

Axiom red_pair : forall t u k π e, pair↓e ★ t·u·k·π ≻ k ★ <|t, u|>·π.
Axiom red_proj1 : forall t u k π e, proj1↓e ★ <|t, u|>·k·π ≻ k ★ t·π.
Axiom red_proj2 : forall t u k π e, proj2↓e ★ <|t, u|>·k·π ≻ k ★ u·π.
Axiom red_inj1 : forall t k π e, inj1↓e ★ t·k·π ≻ k ★ ι₁ t·π.
Axiom red_inj2 : forall u k π e, inj2↓e ★ u·k·π ≻ k ★ ι₂ u·π.
Axiom red_case1 : forall t k₁ k₂ π e, case↓e ★ ι₁ t·k₁·k₂·π ≻ k₁ ★ t·π.
Axiom red_case2 : forall u k₁ k₂ π e, case↓e ★ ι₂ u·k₁·k₂·π ≻ k₂ ★ u·π.

Definition prod A B F := fun π => exists t, exists u, exists π', π = <|t, u|>·π' /\ t ⊩ A /\ u ⊩ B /\ π' ∈ ‖F‖.
Notation "A ** B ⇒ F" := (prod A B F) (at level 40).
Definition sum A B F := fun π =>
  exists t, exists π', ((π = ι₁ t·π' /\ t ⊩ A) \/ (π = ι₂ t·π' /\ t ⊩ B)) /\ π' ∈ ‖F‖.
Notation "A ++ B ⇒ F" := (sum A B F) (at level 40).

(** **  Tactics  **)

Global Ltac pair_sum_Keval tac :=
  lazymatch goal with
    | [ |- Cst pair↓ _ ★ ?t·?u·?k·?π ∈ ⫫] => Debug "Keval_pair";
         apply anti_evaluation with (k ★ <|t, u|>·π); [now apply red_pair |]
    | [ |- Cst proj1↓ _ ★ <|?t, ?u|>·?k·?π ∈ ⫫] => Debug "Keval_proj1";
         apply anti_evaluation with (k ★ t·π); [now apply red_proj1 |]
    | [ |- Cst proj2↓ _ ★ <|?t, ?u|>·?k·?π ∈ ⫫] => Debug "Keval_proj2";
         apply anti_evaluation with (k ★ u·π); [now apply red_proj2 |]
    | [ |- Cst inj1↓ _ ★ ?t·?k·?π ∈ ⫫] => Debug "Keval_inj1";
         apply anti_evaluation with (k ★ ι₁ t·π); [now apply red_inj1 |]
    | [ |- Cst inj2↓ _ ★ ?u·?k·?π ∈ ⫫] => Debug "Keval_inj2";
         apply anti_evaluation with (k ★ ι₂ u·π); [now apply red_inj2 |]
    | [ |- Cst case↓ _ ★ ι₁ ?t·?k₁·?k₂·?π ∈ ⫫] => Debug "Keval_case1";
         apply anti_evaluation with (k₁ ★ t·π); [now apply red_case1 |]
    | [ |- Cst case↓ _ ★ ι₂ ?u·?k₁·?k₂·?π ∈ ⫫] => Debug "Keval_case2";
         apply anti_evaluation with (k₂ ★ u·π); [now apply red_case2 |]
    | _ => Debug "Keval_next"; tac
  end.

Ltac Keval ::= basic_Keval ltac:(idtac; pair_sum_Keval fail).

Global Ltac pair_sum_dstack tac Hπ :=
  lazymatch type of Hπ with
    | ?π ∈ ‖?A ** ?B ⇒ ?F‖ =>
      let t := fresh "t" in let Ht := fresh "Ht" in let u := fresh "u" in let Hu := fresh "Hu" in
      let π' := fresh "π" in let t' := fresh "t" in let u' := fresh "u" in let Heq := fresh "Heq" in 
      destruct Hπ as [t' [u' [π' [Heq [Ht [Hu Hπ]]]]]]; destruct π as [| t π]; inversion Heq
    | ?π ∈ ‖?A ++ ?B ⇒ ?F‖ =>
      let t := fresh "t" in let t' := fresh "t" in let π' := fresh "π" in
      let Ht := fresh "Ht" in let Heq := fresh "Heq" in 
      destruct Hπ as [t [π' [Hcase Hπ]]]; destruct π as [| t' π]; (destruct Hcase as [[Heq Ht] | [Heq Ht]];
      inversion Heq; subst π' t'; clear Heq)
    | _ => tac Hπ
  end.

Ltac dstack ::= basic_dstack ltac:(pair_sum_dstack fail).

(** **  Specifications  **)

Theorem pair_realizer : forall e, pair↓e ⊩ ∀A B, A → B → ∀Z, (A ** B ⇒ Z) → Z.
Proof. Ksolve. Qed.

Theorem proj1_realizer : forall e, proj1↓e ⊩ ∀A B Z, (A ** B ⇒ ((A → Z) → Z)).
Proof. Ksolve. Qed.

Theorem proj2_realizer : forall e, proj2↓e ⊩ ∀A B Z, (A ** B ⇒ ((B → Z) → Z)).
Proof. Ksolve. Qed.

Theorem inj1_realizer : forall e, inj1↓e ⊩ ∀A B, A → ∀Z, (A ++ B ⇒ Z) → Z.
Proof. Ksolve. intuition. Qed.

Theorem inj2_realizer : forall e, inj2↓e ⊩ ∀A B, B → ∀Z, (A ++ B ⇒ Z) → Z.
Proof. Ksolve. intuition. Qed.

Theorem case_realizer : forall e, case↓e ⊩ ∀A B, A ++ B ⇒ ∀Z, (A → Z) → (B → Z) → Z.
Proof. Ksolve. Qed.


(*********************************************************)
(** *  Equivalence between e₁ = e₂ ⇒ A and e₁ = e₂ ↦ A  **)
(*********************************************************)

Lemma eq_equiv1 : forall T (a a' : T) A e, λ"x" λ"e" "e" @ "x"↓e ⊩ (a = a' ↦ A) → prop (a = a') → A.
Proof.
Ksolve. elim (Classical_Prop.classic (a = a')); intro H.
  left. find.
  right. find.
Qed.

Lemma eq_equiv2 : forall T (a a' : T) A e, λ"x" "x" @ Id↓e ⊩ (prop (a = a') → A) → a = a' ↦ A.
Proof. Ksolve. start. destruct Hπ as [[] | []]. now apply Id_realizer. contradiction. Qed.


(****************************************************)
(** *  Equivalence between e₁ ≠ e₂ and ¬(e₁ = e₂)  **)
(****************************************************)

Notation "a ≠ a'" := (if Peano_dec.eq_nat_dec a a' then ⊥ else ⊤) (at level 10).
(*Definition neq_equiv1 := λ"x" "x" @ Id.
Definition neq_equiv2 := λ"x" λ"y" "y" @ "x".*)

Transparent prop.
Lemma neq_equiv1 : forall e, λ"x" "x" @ Id↓e ⊩ ∀a a', ¬(prop (a = a')) → a ≠ a'.
Proof.
Ksolve. destruct (Peano_dec.eq_nat_dec a a').
  unfold prop in *. start. destruct Hπ as [[_ Hπ] | [Hc _]]. unfold one in *. Ksolve. contradiction.
  elim Hπ.
Qed. 

Lemma neq_equiv2 : forall e, λ"x" λ"y" "y" @ "x"↓e ⊩ ∀a a', a ≠ a' → ¬(prop (a = a')).
Proof.
Ksolve. unfold prop. destruct (Peano_dec.eq_nat_dec a a').
  left. split. ok. find.
  right. repeat split; ok.
Qed.
Opaque prop.


(***********************************)
(** *  Weak Recurrence Principle  **)
(***********************************)

Notation "x ==  0" := (∀y, x ≠ (S y)) (at level 11).

Lemma S_wf : well_founded (fun y x => S y = x).
Proof.
intros n. induction n; constructor; intros m Hm.
  discriminate Hm.
  now inversion Hm.
Qed.

Lemma Y_wra : forall e, Y↓e ⊩ ∀P, (∀x, (∀y, S y = x ↦ P y) → P x) → ∀x, P x.
Proof. intros ? ? ?. apply (Y_realizer S_wf). exact H. Qed.

Definition WRA := λ"x" λ"y" Y @ (λ"z" callcc @ (λ"k" "x" @ ("k" @ ("y" @ "z")))).

Theorem WRA_realizer : forall e, WRA↓e ⊩ ∀P, (∀x, x == 0 → P x) → (∀y, P y → P (S y)) → ∀x, P x.
Proof.
Ksolve. apply Y_wra. do 2 Ksolve. Ksolve.
  destruct (Peano_dec.eq_nat_dec (S y) x0) as [Heq | Heq]. Ksolve.
  destruct (Peano_dec.eq_nat_dec x0 (S y)) as [Heq2 | Heq2].
    subst. now elim Heq.
    ok.
  destruct (Peano_dec.eq_nat_dec x0 (S y)).
    now subst.
    ok.
Qed.
