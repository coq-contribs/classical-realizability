Require Import Tactics.
Require Import BasicResults.
Require Import Subtyping.

(******************************)
(** *  Logical equivalences  **)
(******************************)

(** ** Propositional equivalences **)

(* This lemma is used to have the equivalence between both presentations of equalitiy: = or ≠ primitive *)
Lemma neg_equiv : forall e, (λ"t" λ"c" callcc @ λ"k" "t" @ ("k" @ "c"))↓e ⊩ (⊥ → ⊥) → ∀X, X → X.
Proof. do 2 Ksolve. Qed.

Lemma callcc_other_realizer : forall A B e, callcc↓e ⊩ ((A → B) → ⊥) → A.
Proof. intros A B e. apply (sub_term (callcc_realizes_Peirce e)). subtyping. Qed.

Definition not_impl := λ"t" λ"f" "f" @ (callcc @ "t") @ λ"b" "t" @ λ"a" "b".

Lemma not_impl_realizer : forall e, not_impl↓e ⊩ ∀A B, ¬(A → B) → (A ∧ ¬B).
Proof. Ksolve. startn 1. now eapply callcc_other_realizer; find. do 2 Ksolve. Qed.

Definition not_impl2 :=
  λ"t" λ"f" "f" @ (callcc @ "t") @ (callcc @ λ"g" "t" @ λ"a" "g") @ λ"c" "t" @ λ"a" λ"b" "c".

Lemma not_impl2_realizer : forall e, not_impl2↓e ⊩ ∀A B C, ¬(A → B → C) → (A ∧ B ∧ ¬C).
Proof.
Ksolve.
  startn 1. now eapply callcc_other_realizer; find.
  startn 1. eapply callcc_other_realizer; find. do 2 Ksolve. eok.
  do 2 Ksolve.
Qed.

Definition not_impl3 := λ"t" λ"f" "f" @ (callcc @ "t")
                                      @ (callcc @ (λ"g" "t" @ λ"a" "g"))
                                      @ (callcc @ (λ"g" "t" @ λ"a" λ"b" "g"))
                                      @ λ"d" "t" @ λ"a" λ"b" λ"c" "d".

Lemma not_impl3_realizer : forall e, not_impl3↓e ⊩ ∀A B C D, ¬(A → B → C → D) → (A ∧ B ∧ C ∧ ¬D).
Proof.
Ksolve.
  startn 1. now eapply callcc_other_realizer; find.
  startn 1. eapply (callcc_other_realizer _ (C → D)); find. do 2 Ksolve.
  startn 1. eapply callcc_other_realizer; find. do 2 Ksolve. eok.
  do 2 Ksolve.
Qed.

Definition not_impl4 := λ"t" λ"f" "f" @ (callcc @ "t")
                                      @ (callcc @ (λ"g" "t" @ λ"a" "g"))
                                      @ (callcc @ (λ"g" "t" @ λ"a" λ"b" "g"))
                                      @ (callcc @ (λ"g" "t" @ λ"a" λ"b" λ"c" "g"))
                                      @ λ"e" "t" @ λ"a" λ"b" λ"c" λ"d" "e".

Lemma not_impl4_realizer : forall e, not_impl4↓e ⊩ ∀A B C D E, ¬(A → B → C → D → E) → (A ∧ B ∧ C ∧ D ∧ ¬E).
Proof.
Ksolve.
  startn 1. now eapply callcc_other_realizer; find.
  startn 1. eapply (callcc_other_realizer _ (C → D → E)); find. do 2 Ksolve.
  startn 1. eapply (callcc_other_realizer _ (D → E)); find. do 2 Ksolve.
  startn 1. eapply callcc_other_realizer; find. do 2 Ksolve. eok.
  do 2 Ksolve.
Qed.


Definition De_Morgan_nor := λ"nor" λ"f" "f" @ (λ"a" "nor" @ λ"AZ" λ"BZ" "AZ" @ "a")
                                            @ (λ"b" "nor" @ λ"AZ" λ"BZ" "BZ" @ "b").

Lemma De_Morgan_nor_realizer : forall e, De_Morgan_nor↓e ⊩ ∀A B C, ((A ∨ B) → C) → ((A → C) ∧ (B → C)).
Proof. do 3 Ksolve. Qed.

Corollary De_Morgan_nor_realizer_not : forall e, De_Morgan_nor↓e ⊩ ∀A B, ¬(A ∨ B) → (¬A ∧ ¬B).
Proof. intro e. apply (sub_term (De_Morgan_nor_realizer e)). subtyping. Qed.

Definition De_Morgan_nand :=
  λ"nand" λ"nAZ" λ"nBZ" callcc @ λ"k" "nAZ" @ λ"a" "nand" @ (λ"f" callcc @ λ"k'"
                               ("k" @ ("nBZ" @ λ"b" "k'" @ ("f" @ "a" @ "b")))).

Lemma De_Morgan_nand_realizer : forall e, De_Morgan_nand↓e ⊩ ∀A B C, ((A ∧ B) → C) → ((A → C) ∨ (B → C)).
Proof. do 4 Ksolve. Qed.


(** **  Negation and quantifiers  **)

(** ***  ¬∃x F -> ∀x ¬F  **)
Theorem not_ex_all_not_proof : forall A (B : A -> Prop), ~(exists x, B x) -> forall x, ~B x.
Proof. intros A B H x Hx. elim H. now exists x. Qed.

Definition not_ex_all_not := λ"Ex" λ"F" "Ex" @ (λ"f" "f" @ "F").

Theorem not_ex_all_not_realizer : forall T (F : T -> formula),
  forall e, not_ex_all_not↓e ⊩ ¬(∃x, F x) → ∀x, ¬F x.
Proof. repeat Ksolve. Qed.

Corollary not_ex_all_not_realizer2 : forall T S (F : T -> S -> formula),
  forall e, not_ex_all_not↓e ⊩ ¬(∃x y, F x y) → ∀x y, ¬F x y.
Proof. repeat Ksolve. Qed.

Corollary not_ex_all_not_realizer3 : forall T S R (F : T -> S -> R -> formula),
  forall e, not_ex_all_not↓e ⊩ ¬(∃x y z, F x y z) → ∀x y z, ¬F x y z.
Proof. repeat Ksolve. Qed.

Corollary not_ex_all_not_realizer4 : forall T S R Q (F : T -> S -> R -> Q -> formula),
  forall e, not_ex_all_not↓e ⊩ ¬(∃x y z t, F x y z t) → ∀x y z t, ¬F x y z t.
Proof. repeat Ksolve. Qed.

(** Relativised version of the preceding theorems **)
Definition not_ex_all_not_rel1 := λ"nEx" λ"x" λ"F" "nEx" @ (λ"f" "f" @ "x" @ "F").

Theorem not_ex_all_not_rel1_realizer : forall T (P F : T -> formula),
  forall e, not_ex_all_not_rel1↓e ⊩ ¬(∃₁x∈P, F x) → ∀₁x∈P, ¬F x.
Proof. repeat Ksolve. Qed.

Definition not_ex_all_not_rel2 :=
  λ"nEx" λ"x" λ"y" λ"F" "nEx" @ (λ"f" "f" @ "x" @ "y" @ "F").

Theorem not_ex_all_not_rel2_realizer :
  forall T₁ T₂ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula) (F : T₁ -> T₂ -> formula),
  forall e, not_ex_all_not_rel2↓e ⊩ ¬(∃₂x,y∈P₁×P₂, F x y) → ∀₂x,y∈P₁×P₂, ¬F x y.
Proof. repeat Ksolve. Qed.

Definition not_ex_all_not_rel3 :=
  λ"nEx" λ"x" λ"y" λ"z" λ"F" "nEx" @ (λ"f" "f" @ "x" @ "y" @ "z" @ "F").

Theorem not_ex_all_not_rel3_realizer :
  forall T₁ T₂ T₃ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula) (P₃ : T₃ -> formula) (F : T₁ -> T₂ -> T₃ -> formula),
  forall e, not_ex_all_not_rel3↓e ⊩ ¬(∃₃x,y,z∈P₁×P₂×P₃, F x y z) → ∀₃x,y,z∈P₁×P₂×P₃, ¬F x y z.
Proof. repeat Ksolve. Qed.

Definition not_ex_all_not_rel4 := λ"nEx" λ"x" λ"y" λ"z" λ"t" λ"F"
  "nEx" @ (λ"f" "f" @ "x" @ "y" @ "z" @ "t" @ "F").

Theorem not_ex_all_not_rel4_realizer : forall T₁ T₂ T₃ T₄ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula)
     (P₃ : T₃ -> formula) (P₄ : T₄ -> formula) (F : T₁ -> T₂ -> T₃ -> T₄ -> formula),
  forall e, not_ex_all_not_rel4↓e ⊩ ¬(∃₄x,y,z,t∈P₁×P₂×P₃×P₄, F x y z t) → ∀₄x,y,z,t∈P₁×P₂×P₃×P₄, ¬F x y z t.
Proof. repeat Ksolve. Qed.


(** ***  ¬∀x F -> ∃x ¬F  **)
Theorem not_all_ex_not_proof : forall A (B : A -> Prop), ~(forall x, B x) -> exists x, ~B x.
Proof.
intros A B H. apply Classical_Prop.NNPP. intros Habs. elim H.
intro x. apply Classical_Prop.NNPP. intro. elim Habs. now exists x.
Qed.

Definition not_all_ex_not := (* λf. cc (λg. f (cc (λh. g (λi. i h)))) *)
  λ"f" callcc @ (λ"g" "f" @ (callcc @ (λ"h" "g" @ (λ"i" "i" @ "h")))).

Theorem not_all_ex_not_realizer : forall T (F : T -> formula),
  forall e, not_all_ex_not↓e ⊩ ¬(∀x, F x) → ∃x, ¬F x.
Proof. do 3 Ksolve. eok. Qed.

Corollary not_all_ex_not_realizer2 : forall T S (F : T -> S -> formula),
  forall e, not_all_ex_not↓e ⊩ ¬(∀x y, F x y) → ∃x y, ¬F x y.
Proof. do 3 Ksolve. eok. Qed.

Corollary not_all_ex_not_realizer3 : forall T S R (F : T -> S -> R -> formula),
  forall e, not_all_ex_not↓e ⊩ ¬(∀x y z, F x y z) → ∃x y z, ¬F x y z.
Proof. do 3 Ksolve. eok. Qed.

Corollary not_all_ex_not_realizer4 : forall T S R Q (F : T -> S -> R -> Q -> formula),
  forall e, not_all_ex_not↓e ⊩ ¬(∀x y z t, F x y z t) → ∃x y z t, ¬F x y z t.
Proof. do 3 Ksolve. eok. Qed.

(** Relativised version of the preceding theorem **)
Definition not_all_ex_not_rel1 :=
  λ"f" callcc @ (λ"g" ("f" @ (λ"r" callcc @ (λ"h" ("g" @ (λ"i" ("i" @ "r" @ "h"))))))).

Theorem not_all_ex_not_rel1_realizer : forall T (P F : T -> formula),
  forall e, not_all_ex_not_rel1↓e ⊩ ¬(∀₁x∈P, F x) → ∃₁x∈P, ¬F x.
Proof. repeat Ksolve. Qed.

Definition not_all_ex_not_rel2 := λ"f" callcc @ (λ"g" "f" @ (λ"r₁" λ"r₂"
  callcc @ (λ"h" "g" @ (λ"i" "i" @ "r₁" @ "r₂" @ "h")))).

Theorem not_all_ex_not_rel2_realizer :
  forall T₁ T₂ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula) (F : T₁ -> T₂ -> formula),
  forall e, not_all_ex_not_rel2↓e ⊩ ¬(∀₂x,y∈P₁×P₂, F x y) → ∃₂x,y∈P₁×P₂, ¬F x y.
Proof. repeat Ksolve. Qed.

Definition not_all_ex_not_rel3 := λ"f" callcc @ (λ"g" "f" @ (λ"r₁" λ"r₂" λ"r₃"
  callcc @ (λ"h" "g" @ (λ"i" "i" @ "r₁" @ "r₂" @ "r₃" @ "h")))).

Theorem not_all_ex_not_rel3_realizer :
  forall T₁ T₂ T₃ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula) (P₃ : T₃ -> formula) (F : T₁ -> T₂ -> T₃ -> formula),
  forall e, not_all_ex_not_rel3↓e ⊩ ¬(∀₃x,y,z∈P₁×P₂×P₃, F x y z) → ∃₃x,y,z∈P₁×P₂×P₃, ¬F x y z.
Proof. repeat Ksolve. Qed.

Definition not_all_ex_not_rel4 := λ"f" callcc @ (λ"g" "f" @ (λ"r₁" λ"r₂" λ"r₃" λ"r₄"
  callcc @ (λ"h" "g" @ (λ"i" "i" @ "r₁" @ "r₂" @ "r₃" @ "r₄" @ "h")))).

Theorem not_all_ex_not_rel4_realizer : forall T₁ T₂ T₃ T₄ (P₁ : T₁ -> formula) (P₂ : T₂ -> formula)
              (P₃ : T₃ -> formula) (P₄ : T₄ -> formula) (F : T₁ -> T₂ -> T₃ -> T₄ -> formula),
  forall e, not_all_ex_not_rel4↓e ⊩ ¬(∀₄x,y,z,t∈P₁×P₂×P₃×P₄, F x y z t) → ∃₄x,y,z,t∈P₁×P₂×P₃×P₄, ¬F x y z t.
Proof. repeat Ksolve. Qed.

Definition not_all_not_ex := λ"f" λ"g" callcc @ λ"k" "f" @ (λ"a" "k" @ ("g" @ "a")).

Theorem  not_all_not_ex_realizer : forall T (A : T -> formula) e, not_all_not_ex↓e ⊩ (¬(∀x, ¬A x)) → ∃x, A x.
Proof. do 2 Ksolve. Qed.
