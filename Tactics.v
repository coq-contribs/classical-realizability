Require Export ShallowEmbedding.


(********************************)
(** *  Automatisation tactics  **)
(********************************)

(** The tactics meant to be used are:
    - [ok]/[eok] for solving very simple goals
    - [Keval] for performing a one-step reduction by the KAM
    - [Kevals] to evaluate as much as possible
    - [dstack] to exhibit the first element of a stack when there is one
    - [dec] to exhibit all elements of a stack
    - [start] to start a proof, basically combines dec and Kevals
    - [find] to guess witnesses by meta-variables and try to solve the immediate goals
    - [Ksolve] automatic procedure that can solve simple proof
    - [Kmove] same as [Ksolve] but does not make guesses with [find]

    The tactics [start] and [find] have variants [startn] and [findn] where you indicate the number of steps/guesses.
    This avoids too eager unfolding and bad guesses.

    When introducing new connectives, you need to extend (through redefinition) the tactics [dstack] and
    [Keval] for dealing with them.  They are written in CPS style so that you can choose the order of basic tactics
    to improve performance.
    All the other tactics will take advantage of the modifications.
**)

Lemma Var_subst : forall n e t F, t ⊩ F -> get n e = t -> n↓e ⊩ F.
Proof. intros n e t F Ht Hget π Hπ. eapply anti_evaluation. apply red_Var. rewrite Hget. now apply Ht. Qed.

(** A closing tactic which proves obvious statements:
    - [t ⊩ A,  π ∈ ‖A‖  |-  t ★ π ∈ ⫫]
    - [_  |-  π ∈ ‖⊥‖]
    - [_  |-  t ⊩ ⊤]
    - [π ∈ ‖⊤‖ |- _]
    - anything solved by [tac]
**)
Ltac end_tac tac :=
  lazymatch goal with
    | [H : ?t ⊩ ?A |- Closed (Var _) _ ⊩ ?A] => apply Var_subst with t; reflexivity || now apply H
    | [H₁ : ?t ⊩ ?A, H₂ : ?π ∈ ‖?A‖ |- ?t ★ ?π ∈ ⫫] => now apply H₁
    | [ |- ?π ∈ ‖⊥‖] => now exists (fun _ : Π => True)
    | [ |- ?t ⊩ ⊤] => intros ? ?; contradiction
    | [H : ?π ∈ ‖⊤‖ |- _] => elim H
    | _ => tac
  end.

Ltac ok := end_tac assumption.

(** The same as the previous one but uses eassumption instead of assumption **)
Ltac eok := end_tac eassumption.

(** Automatically fill in existentials and try to realize them with [eok] **)
Ltac find := repeat (eexists; repeat split; try eok).
Tactic Notation "findn" integer(n) := do n (eexists; repeat split; try eok).

(** For debugging purpose: redefine it as [idtac str] to print the debug strings. **)
Ltac Debug str := idtac.

(** **  Internal tactics  **)

(** Basic fragment of a tactic for applying anti_evaluation

    We choose not to unfold definitions because they usually have their own realizability lemmas.
**)
Ltac basic_Keval tac :=
  lazymatch goal with
    | [ |- (Lam ?n ?t)↓ ?e ★ ?t₁·?s ∈ ⫫] =>
         Debug "Keval_Lam"; apply anti_evaluation with (t↓(n←t₁;e) ★ s); [now apply red_Lam |]
    | [ |- (App ?t₁ (Var ?n))↓ ?e ★ ?s ∈ ⫫] =>
         Debug "Keval_AppVar"; apply anti_evaluation with (t₁↓e ★ (get n e · s)); [now apply red_AppVar | simpl get]
    | [ |- (App ?t₁ ?t₂)↓ ?e ★ ?s ∈ ⫫] =>
         Debug "Keval_Var"; apply anti_evaluation with (t₁↓e ★ (t₂↓e · s)); [now apply red_App |]
    | [ |- Cst callcc↓ ?e ★ ?t·?s ∈ ⫫] =>
         Debug "Keval_callcc"; apply anti_evaluation with (t ★ k[s] · s); [now apply red_cc |]
    | [ |- (Cont ?s) ★ ?t·_ ∈ ⫫] =>
         Debug "Keval_k"; apply anti_evaluation with (t ★ s); [now apply red_k |]
    | [ |- (Var ?n)↓ ?e ★ ?s ∈ ⫫] =>
         Debug "Keval_Var"; apply anti_evaluation with (get n e ★ s); [now apply red_Var | simpl get]
    | _ => tac
  end.

(** Basic fragment of a tactic for destructing stack depending on its falsity value **)
Ltac basic_dstack tac Hπ :=
  lazymatch type of Hπ with
    | context[Rel _ _] => repeat autounfold with Krivine in Hπ
    | ?π ∈ ‖ _ → _ ‖ =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      destruct π as [| t π]; [contradiction | simpl in Hπ; destruct Hπ as [Ht Hπ]]
    | ?π ∈ ‖ ∀ t, _ ‖ => let tt := fresh t in destruct Hπ as [tt Hπ]
    | ?π ∈ ‖ ∃ _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ ∀₁ t ∈ _, _ ‖ => let tt := fresh t in destruct Hπ as [tt Hπ]
    | ?π ∈ ‖ ∃₁ _ ∈ _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ ∀₂ t₁, t₂ ∈ _ × _, _ ‖ => let tt₁ := fresh t₁ in let tt₂ := fresh t₂ in destruct Hπ as [tt₁ [tt₂ Hπ]]
    | ?π ∈ ‖ ∃₂ _, _ ∈ _ × _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ ∀₃ t₁, t₂, t₃ ∈ _ × _ × _, _ ‖ =>
      let tt₁ := fresh t₁ in let tt₂ := fresh t₂ in let tt₃ := fresh t₃ in destruct Hπ as [tt₁ [tt₂ [tt₃ Hπ]]]
    | ?π ∈ ‖ ∃₃ _, _, _ ∈ _ × _ × _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ ∀₄ t₁, t₂, t₃, t₄ ∈ _ × _ × _ × _, _ ‖ =>
      let tt₁ := fresh t₁ in let tt₂ := fresh t₂ in let tt₃ := fresh t₃ in let tt₄ := fresh t₄ in
      destruct Hπ as [tt₁ [tt₂ [tt₃ [tt₄ Hπ]]]]
    | ?π ∈ ‖ ∃₄ _, _, _, _ ∈ _ × _ × _ × _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ ∀₅ t₁, t₂, t₃, t₄, t₅ ∈ _ × _ × _ × _ × _, _ ‖ =>
      let tt₁ := fresh t₁ in let tt₂ := fresh t₂ in let tt₃ := fresh t₃ in let tt₄ := fresh t₄ in
      let tt₅ := fresh t₅ in destruct Hπ as [tt₁ [tt₂ [tt₃ [tt₄ [tt₅ Hπ]]]]]
    | ?π ∈ ‖ ∃₅ _, _, _, _, _ ∈ _ × _ × _ × _ × _, _ ‖ => let Z := fresh "Z" in destruct Hπ as [Z Hπ]
    | ?π ∈ ‖ and2 _ _ ‖ => unfold and2 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ and3 _ _ _ ‖ => unfold and3 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ and4 _ _ _ _ ‖ => unfold and4 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ and5 _ _ _ _ _ ‖ => unfold and5 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ and6 _ _ _ _ _ ‖ => unfold and6 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ or2 _ _ ‖ => unfold or2 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ or3 _ _ _ ‖ => unfold or3 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ or4 _ _ _ _ ‖ => unfold or4 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ or5 _ _ _ _ _ ‖ => unfold or5 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ or6 _ _ _ _ _ _ ‖ => unfold or6 in Hπ; basic_dstack tac Hπ
    | ?π ∈ ‖ ?c ↦ ?F ‖ => let Hc := fresh "Hc" in destruct Hπ as [Hc Hπ]
    | ?π ∈ ‖ ?A ∩ ?B ‖ => unfold inter in Hπ; destruct Hπ as [Hπ | Hπ]
    | _ => tac Hπ
  end.

(** **  User tactics using the above fragments **)
    
(** They are meant to be redefined when extending the reduction rules / realizability connectives. **)
Ltac Keval := basic_Keval fail.
Ltac dstack := basic_dstack fail.
(** User decomposition tactics. Will work with new definition of Keval and dstack **)
Ltac Kevals := progress (repeat Keval).
Ltac dec π := match goal with | [Hπ : π ∈ ‖ _ ‖ |- _] => repeat dstack Hπ end.

(** Removing useless stacks from context **)
Ltac remove_stacks :=
  try match goal with
    | Hπ : ?π ∈ ‖_‖ |- _ =>
       match goal with
         | |- context[π] => fail 1 (* can appear outside a k[_·s], like for instance π ∈ ‖_‖ *)
         | |- _ => try clear dependent π; remove_stacks
       end
    | π : Π |- _ => (clear dependent π; remove_stacks) || fail 1
    | _ => idtac
  end.

Ltac unfold_def :=
  match goal with
    | |- (Lam _ _)↓ _ ★ _ ∈ ⫫ => idtac
    | |- (App _ _)↓ _ ★ _ ∈ ⫫ => idtac
    | |- Cst callcc↓ _ ★ _ ∈ ⫫ => idtac
    | |- (Cont _) ★ _ ∈ ⫫ => idtac
    | |- ?t↓ _ ★ _ ∈ ⫫ => unfold t at 1; unfold_def
    | |- ?t _↓ _ ★ _ ∈ ⫫ => unfold t at 1; unfold_def
    | |- ?t _ _↓ _ ★ _ ∈ ⫫ => unfold t at 1; unfold_def
    | |- ?t _ _ _↓ _ ★ _ ∈ ⫫ => unfold t at 1; unfold_def
    | |- ?t _ _ _ _↓ _ ★ _ ∈ ⫫ => unfold t at 1; unfold_def
    | |- _ => idtac
  end.

Ltac start :=
  remove_stacks; let π := fresh "π" in let Hπ := fresh "Hπ" in intros π Hπ;
  dec π; unfold_def; try Kevals.

Tactic Notation "startn" integer(n) :=
  remove_stacks; let π := fresh "π" in let Hπ := fresh "Hπ" in intros π Hπ;
  dec π; unfold_def; do n Keval.

Ltac Kprogress := (* TODO: optimize the case of H : ?s ∈ ‖?A‖ |- _ ∈ ‖∃ _‖ with exists A; split; [| exact H] *)
  match goal with
    | Ht : ?t ⊩ ?A |- ?t ★ _ ∈ ⫫ => apply Ht
    | Hπ : ?s ∈ ‖_‖ |- _ => progress dec s
    | _ => ok || Kevals || (repeat split)
  end.

(** Most high-level and automated tactics **)
Ltac Kmove := intros; try start; repeat Kprogress.

Ltac Ksolve := Kmove; find; repeat Kprogress.
