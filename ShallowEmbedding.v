Require Import Bool.
Require Import String.
Require Classical.
Require Import Coq.Classes.RelationClasses.
Require Coq.Setoids.Setoid.

Open Scope string_scope.

(* To solve bug 2630. *)
Ltac easy ::=
  let rec use_hyp H :=
   (match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try (solve [ inversion H ])
    end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro) in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end) in
  let rec do_atom :=
   ((solve [ reflexivity | symmetry; trivial ]) || (* the only modified line *)
      contradiction || (split; do_atom))
  with do_ccl := (trivial with eq_true; do_atom || (repeat do_intro; do_atom)) in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".


(***************************)
(** *  Krivine's machine  **)
(***************************)


(** An abstract set of instructions, containing callcc **)
Parameter instruction : Set.
Parameter callcc : instruction.

(** A set of stack constants **)
Parameter stack_const : Set.

(** λ_c terms **)
Inductive term : Set :=
  | Cst : instruction -> term
  | Lam : string -> term -> term
  | Var : string -> term
  | App : term -> term -> term.
Coercion Cst : instruction >-> term.
Coercion Var : string >-> term.
Notation "'λ' n t" := (Lam n t) (at level 16, n at level 0, t at level 41, format "'λ' n '/  '  t").
Notation "t @ s" := (App t s) (at level 15, left associativity).


(** Closures, stacks and environments **)
Inductive Λ : Set :=
  | Closed : term -> env -> Λ
  | Cont : Π -> Λ
with Π : Set :=
  | Scst : stack_const -> Π
  | Scons : Λ -> Π -> Π
with env : Set :=
  | Enil : env
  | Econs : string -> Λ -> env -> env.
Coercion Scst : stack_const >-> Π.
Notation "t ↓ e" := (Closed t e) (at level 45, no associativity, format "t '/  ' '↓' e").
Notation "k[ π ]" := (Cont π).
Notation "t · s" := (Scons t s) (at level 47, right associativity).
Notation "e ← t ; f" := (Econs e t f) (at level 49, right associativity, format "e '←' t ';'  '/' f").
Notation "∅" := Enil.

Bind Scope Env_scope with env.
Bind Scope Stack_scope with Π.
Bind Scope Clos_scope with Λ.

Arguments Scope Cont [Stack_scope].
Arguments Scope Scons [Clos_scope Stack_scope].
Arguments Scope Econs [Clos_scope Env_scope].

(* Extracting a closure from an environment *)
Fixpoint get s (e : env) : Λ :=
  match e with
    | c←t;e' => if string_dec s c then t else get s e'
    | Enil => "environment too small"↓Enil (* dummy case *)
  end.

(** Checking wether a term is closed.
    Useful for eliminating typos in big λ_c-terms.  **)
Fixpoint closed_aux acc t :=
  match t with
    | Cst _ => true
    | Lam s t' => closed_aux (cons s acc) t'
    | Var n => if List.in_dec string_dec n acc then true else false
    | App t₁ t₂ => closed_aux acc t₁ && closed_aux acc t₂
  end.

Definition closed := closed_aux nil.


(** Processes **)
Inductive process := Process : Λ -> Π -> process.
Notation "c '★' s" := (Process c s) (at level 55).

(** **  Reduction rules  **)

Parameter red : process -> process -> Prop.
Notation "p₁ ≻ p₂" := (red p₁ p₂) (at level 70).
Axiom red_trans : forall p₁ p₂ p₃, p₁ ≻ p₂ -> p₂ ≻ p₃ -> p₁ ≻ p₃.

(** Reduction rules: grab, push, save, restore plus one for variables.
    
    The last rule is necessary for native data: we unbox it to expose it to the operators.
**)
Axiom red_Lam : forall n t c e π, (λ n t)↓e ★ c·π ≻ t↓(n←c;e) ★ π.
Axiom red_App : forall t t' e π, t @ t'↓e ★ π ≻ t↓e ★ t'↓e · π.
Axiom red_cc : forall t e π, callcc↓e ★ t·π ≻ t ★ k[π]·π.
Axiom red_k : forall t π π', k[π] ★ t·π' ≻ t ★ π.
Axiom red_Var : forall n e π, Var n↓e ★ π ≻ get n e ★ π.
Axiom red_AppVar : forall t n e π, t @ Var n↓e ★ π ≻ t↓e ★ get n e·π.

(** Tactics to perform one step of evaluation in the KAM **)
Ltac Kred tac := eapply red_trans; [now apply tac |].
Ltac Kstep := Kred red_Lam || (Kred red_Var; simpl get) || (Kred red_AppVar; simpl get) || Kred red_cc
             || Kred red_k || (Kred red_App; simpl get).

(** Printing command for λ_c terms. **)
Section Printing.
  Variable print_const : instruction -> string.
  Variable print_sconst : stack_const -> string.

  Fixpoint print_term (t : term) : string :=
    match t with
      | Cst c => print_const c
      | Lam n t => "λ" ++ n ++ " " ++ print_term t
      | Var n => n
      | App t₁ t₂ => print_term t₁ ++ " " ++ print_term t₂
    end.
  
  Fixpoint print_clos c :=
    match c with
      | Closed t e => (print_term t ++ "↓" ++ print_env e)%string
      | Cont s => "k[" ++ print_stack s ++ "]"
    end
  with print_stack s :=
    match s with
      | Scst α => print_sconst α
      | Scons c s' => print_clos c ++ "°" ++ print_stack s'
    end
  with print_env e :=
    match e with
      | Enil => "∅"%string
      | Econs n c Enil => n ++ " ↦ " ++ print_clos c
      | Econs n c e' => n ++ " ↦ " ++ print_clos c ++ ", " ++ print_env e'
    end.
End Printing.

(** **  Some usual terms  **)

Definition Id := λ"x" "x".
Definition nId := λ"x" ("x" @ "x"). (* or any λx. x u *) 
Definition tt := λ"x" λ"y" "x".
Definition ff := λ"x" λ"y" "y".
Definition δ := λ"x" "x" @ "x".
Definition Ω := δ @ δ.
(** A universal realizer of excluded middle **)
Definition em := λ"f" λ"g" callcc @ λ"k" "g" @ λ"i" "k" @ ("f" @ "i").
(** Turing's fixpoint operator **)
Definition Y := (λ"x" λ"y" "y" @ ("x" @ "x" @ "y")) @ (λ"x" λ"y" "y" @ ("x" @ "x" @ "y")).

Example Ω_red : forall e π, δ↓e ★ δ↓e·π ≻ δ↓e ★ δ↓e·π.
Proof. unfold δ at 1. intros e π. do 2 Kstep. apply red_Var. Qed.

(** Storage operators for functions.
    We impose the presence of the continuation(s) k (or u and v)
    to ensure that reduction can only occur when it is present.
**)
Definition caron1 op := λ"Mx" "Mx" @ λ"x" op @ "x".
Definition caron2 op := λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" op @ "x" @ "y".
Definition caron3 op := λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" λ"Mz" "Mz" @ λ"z" op @ "x" @ "y" @ "z".
Definition caron4 op := λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" λ"Mz" "Mz" @ λ"z"
  λ"Mt" "Mt" @ λ"t" op @ "x" @ "y" @ "z" @ "t".

(** Same thing for relations. **)
Definition rel_caron1 rel := λ"Mx" "Mx" @ λ"x" rel @ "x".
Definition rel_caron2 rel := λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" rel @ "x" @ "y".
Definition rel_caron3 rel :=
  λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" λ"Mz" "Mz" @ λ"z" rel @ "x" @ "y" @ "z".
Definition rel_caron4 rel := λ"Mx" "Mx" @ λ"x" λ"My" "My" @ λ"y" λ"Mz" "Mz" @ λ"z" λ"Mt" "Mt" @ λ"t"
  rel @ "x" @ "y" @ "z" @ "t".


(***********************)
(** *  Realizability  **)
(***********************)


Parameter pole : process -> Prop.
Notation "p ∈ ⫫" := (pole p) (at level 69, format "p  '∈'  '⫫'").
Axiom anti_evaluation : forall p p', p ≻ p' -> p' ∈ ⫫ -> p ∈ ⫫.

Definition formula := Π -> Prop.

Definition Fval (F : formula) (π : Π) := F π.
Notation "π '∈' '‖' F '‖'" := (Fval F π) (at level 70, format "'[hv' π  '∈' '/'  '‖' F '‖' ']'").

Definition realizes t F := forall π, π ∈ ‖F‖ -> t★π ∈ ⫫.
Notation "t ⊩ F" := (realizes t F) (at level 79).

Definition Impl A B := fun π => match π with Scst _ => False | t·π' => t ⊩ A /\ π' ∈ ‖B‖ end.
Notation "A '→' B" := (Impl A B) (at level 78, right associativity).


Ltac clear_realizers :=
  repeat lazymatch goal with
    | H : _ ⊩ _ |- _ => clear H
    | H : _ ∈ ‖_‖ |- _ => clear H
    | π : Π |- _ => clear π
    | t : Λ |- _ => clear t
    | e : env |- _ => clear e
  end.

(** **  Quantifications  **)

(** There is a lot of boilerplate code here because the notation mecanism of Coq is not powerful enough to handle
    relativized quantification of arbitrary arity sot we have to define it for every arity.
    In addition, we also take advantage of these definitions to optimize relativization predicates,
    so that relativzing to [A x ∧ B x] can be defined as [∀x, A x → B x → …].
    
    In a nutshell, we can use [∀ x y … z, A] or [∃ x y … z, A] for unrelativized quantifications and
    [∀₂ x, y ∈ P₁ × P₂, A] or [∃₃ x, y, z ∈ P₁ × P₂ × P₃] for relatized one, where the indices [₂] and [₃] are
    the number of variables you quantify over.  Currently, it goes from 1 to 5.
**)

(** *** Without relativization **)

Definition Forall T f : formula := fun π => exists t : T, π ∈ ‖f t‖.
Global Notation "'∀' t₁ .. t₂ ',' F" := (Forall _ (fun t₁ => .. (Forall _ (fun t₂ => F)) .. ))
  (at level 99, t₁ binder, t₂ binder, right associativity).
Global Notation "'∃' t₁ .. t₂ ',' F" :=
  (Forall formula (fun Z => (Forall _ (fun t₁ => .. (Forall _ (fun t₂ => F → Z)) ..)) → Z))
  (at level 99, t₁ binder, t₂ binder, right associativity).

(** *** With relativization **)

(** Relativization is defined as an operator of formulæ depending on an argument.
    The simplest such operator on a predicate [P] is [fun A x => P x -> A x] built by [make_Rel]
    but in some cases we may want to define optimized ones, using [now_Rel].
**)
Class Relativisation {T : Type} (P : T -> formula) := Rel : (T -> formula) -> T -> formula.
Global Instance now_Rel {T} P f : @Relativisation T P := {Rel := f}.
Global Instance make_Rel {T} P : @Relativisation T P := {Rel := fun f t => P t → f t}.
Global Hint Unfold Rel now_Rel make_Rel : Krivine.
(* Note: We cannot add the equivalence between relativized formula and the formula with the predicate
         as a precondition because the idea is precisely to modify the number of arguments
         so that terms cannot be equivalent.
         We could add the existence of terms performing the translation in both directions as a way to ensure
         correctness but this could not be used in practice. *)

(** Binding 1 variable **)
Definition ForallR {T} P `{@Relativisation T P} (f : T -> formula) : formula :=
  fun π => exists t : T, π ∈ ‖Rel f t‖.
Global Notation "'∀₁' t '∈' P ',' F" := (ForallR P (fun t => F)) (at level 99, right associativity).
Global Notation "'∃₁' t '∈' P ',' F" :=
  (Forall formula (fun Z => (ForallR P (fun t => F → Z)) → Z)) (at level 99, t at next level).

(** Binding 2 variables **)
Definition ForallR2 {T₁ T₂} P₁ P₂ `{@Relativisation T₁ P₁, @Relativisation T₂ P₂} (f : T₁ -> T₂ -> formula)
  : formula := fun π => exists t₁ : T₁, exists t₂ : T₂, π ∈ ‖Rel (fun t => Rel (f t) t₂) t₁‖.
Global Notation "'∀₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' F" :=
  (ForallR2 P₁ P₂ (fun t₁ t₂ => F)) (at level 99, right associativity).
Global Notation "'∃₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' F" :=
  (Forall formula (fun Z => (ForallR2 P₁ P₂ (fun t₁ t₂ => F → Z)) → Z)) (at level 99, right associativity).

(** Binding 3 variables **)
Definition ForallR3 {T₁ T₂ T₃} P₁ P₂ P₃ `{@Relativisation T₁ P₁, @Relativisation T₂ P₂, @Relativisation T₃ P₃}
                    (f : T₁ -> T₂ -> T₃ -> formula) : formula :=
  fun π => exists t₁ : T₁, exists t₂ : T₂, exists t₃ : T₃,
           π ∈ ‖Rel (fun t => Rel (fun t' => Rel (f t t') t₃) t₂) t₁‖.
Global Notation "'∀₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' F" :=
  (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => F)) (at level 99,  right associativity).
Global Notation "'∃₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' F" :=
  (Forall formula (fun Z => (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => F → Z)) → Z))
  (at level 99, right associativity).

(** Binding 4 variables **)
Definition ForallR4 {T₁ T₂ T₃ T₄} P₁ P₂ P₃ P₄
                    `{@Relativisation T₁ P₁, @Relativisation T₂ P₂, @Relativisation T₃ P₃, @Relativisation T₄ P₄}
                    (f : T₁ -> T₂ -> T₃ -> T₄ -> formula) : formula :=
  fun π => exists t₁ : T₁, exists t₂ : T₂, exists t₃ : T₃, exists t₄ : T₄,
           π ∈ ‖Rel (fun t => Rel (fun t' => Rel (fun t'' => Rel (f t t' t'') t₄) t₃) t₂) t₁‖.
Global Notation "'∀₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' F" :=
  (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => F)) (at level 99,  right associativity).
Global Notation "'∃₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' F" :=
  (Forall formula (fun Z => (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => F → Z)) → Z))
  (at level 99, right associativity).

(** Binding 5 variables **)
Definition ForallR5 {T₁ T₂ T₃ T₄ T₅} P₁ P₂ P₃ P₄ P₅
  `{@Relativisation T₁ P₁, @Relativisation T₂ P₂, @Relativisation T₃ P₃, @Relativisation T₄ P₄,
    @Relativisation T₅ P₅} (f : T₁ -> T₂ -> T₃ -> T₄ -> T₅ -> formula) : formula :=
  fun π => exists t₁ : T₁, exists t₂ : T₂, exists t₃ : T₃, exists t₄ : T₄, exists t₅ : T₅,
    π ∈ ‖Rel (fun t => Rel (fun t' => Rel (fun t'' => Rel (fun t''' => Rel (f t t' t'' t''') t₅) t₄) t₃) t₂) t₁‖.
Global Notation "'∀₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' F" :=
  (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => F)) (at level 99,  right associativity).
Global Notation "'∃₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' F" :=
  (Forall formula (fun Z => (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => F → Z)) → Z))
  (at level 99, right associativity).

(** ***  Function relativisation  **)

Definition fun_Pred {T T'} P P' (f : T -> T') := ∀₁x∈P, P' (f x).
Global Instance fun_Rel {T T'} P P' `{Relativisation T P} : @Relativisation (T -> T') (fun_Pred P P') :=
  now_Rel (fun_Pred P P') (fun f t => (∀₁x∈P, P'(t x)) → f t).
Notation "A '~>' B" := (fun_Pred A B) (at level 80, right associativity).


(** ** Usual connectives **)

Definition Top : formula := fun _ => False.
Notation "⊤" := Top.

Definition bot := ∀ Z, Z.
Notation "⊥" := bot.

Notation "¬ F" := (F → ⊥) (at level 25, only parsing).

Definition one := ∀ Z, (Z → Z).


(** Semantic implication **)

(** Be careful that the equivalence between c → A and c ↦ A can only be realized when c is realized
    by the identity. This means that taking c = n <> m does not provide the equivalence.
    In this case, it is better to take a boolean equality eqb since x <> y then amounts to eqb(x,y) = 0.
**)
Definition mapsto (c : Prop) F := fun π => c /\ π ∈ ‖F‖.
Notation "c '↦' F" := (mapsto c F) (at level 78, right associativity).

(** Intersection type **)
Definition inter A B := fun π => π ∈ ‖A‖ \/ π ∈ ‖B‖.
Notation "A '∩' B" := (inter A B) (at level 71, right associativity).


(** Optimized version for n-ary and **)
Definition and2 A B := ∀ Z, (A → B → Z) → Z.
Notation "A ∧ B" := (and2 A B) (at level 80, no associativity).
Definition and3 A B C := ∀ Z, (A → B → C → Z) → Z.
Notation "A ∧ B ∧ C" := (and3 A B C) (at level 80, B at next level, no associativity).
Definition and4 A B C D := ∀ Z, (A → B → C → D → Z) → Z.
Notation "A ∧ B ∧ C ∧ D" := (and4 A B C D) (at level 80, B at next level, C at next level, no associativity).
Definition and5 A B C D E := ∀ Z, (A → B → C → D → E → Z) → Z.
Notation "A ∧ B ∧ C ∧ D ∧ E" := (and5 A B C D E)
  (at level 80, B at next level, C at next level, D at next level, no associativity).
Definition and6 A B C D E F := ∀ Z, (A → B → C → D → E → F → Z) → Z.
Notation "A ∧ B ∧ C ∧ D ∧ E ∧ F" := (and6 A B C D E F)
  (at level 80, B at next level, C at next level, D at next level, E at next level, no associativity).

(** Optimized versions for n-ary or **)
Definition or2 A B := ∀ Z, (A → Z) → (B → Z) → Z.
Notation "A ∨ B" := (or2 A B) (at level 85, no associativity).
Definition or3 A B C := ∀ Z, (A → Z) → (B → Z) → (C → Z) → Z.
Notation "A ∨ B ∨ C" := (or3 A B C) (at level 85, B at next level, no associativity).
Definition or4 A B C D := ∀ Z, (A → Z) → (B → Z) → (C → Z) → (D → Z) → Z.
Notation "A ∨ B ∨ C ∨ D" := (or4 A B C D) (at level 85, B at next level, C at next level, no associativity).
Definition or5 A B C D E := ∀ Z, (A → Z) → (B → Z) → (C → Z) → (D → Z) → (E → Z) → Z.
Notation "A ∨ B ∨ C ∨ D ∨ E" := (or5 A B C D E)
  (at level 85, B at next level, C at next level, D at next level, no associativity).
Definition or6 A B C D E F := ∀ Z, (A → Z) → (B → Z) → (C → Z) → (D → Z) → (E → Z) → (F → Z) → Z.
Notation "A ∨ B ∨ C ∨ D ∨ E ∨ F" := (or6 A B C D E F)
  (at level 85, B at next level, C at next level, D at next level, E at next level, no associativity).

(** Combining existential quantifiers and conjonction
    
    We optimize existential qunatifiers and conjunctions [∃x, A x ∧ B x] into [∀Z, (∀x, A x → B x → Z) → Z]
    rather than [∀Z, (∀x, (∀Y, (A x → B x → Y) → Y)) → Z].

    We can also use the semantic implication to get [∀Z, (∀x, A x ↦ B x → Z) → Z]. To do so, use [&] instead of [∧].
    Such semantic conjunctions (at most 2) must be put at the begginning of the conjunct.
**)
(* Conflict with the other ∀_/∃_ notation without { } *)

(** Without ↦ **)
Global Notation "'Ex₁' t '∈' P ',' '{' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR P (fun t => F₁ → .. (F₂ → Z) .. )) → Z))
  (at level 98, t at next level, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' '{' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR2 P₁ P₂ (fun t₁ t₂ => F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' '{' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' '{' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation
  "'Ex₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' '{' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).

(** With one ↦ **)
Global Notation "'Ex₁' t '∈' P ',' '{' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR P (fun t => F₀ ↦ F₁ → .. (F₂ → Z) .. )) → Z))
  (at level 98, t at next level, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' '{' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR2 P₁ P₂ (fun t₁ t₂ => F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' '{' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' '{' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation
  "'Ex₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' '{' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F₀ at level 79, F₁ at level 79, F₂ at level 79).

(** With two ↦ **)
Global Notation "'Ex₁' t '∈' P ',' '{' F '&' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR P (fun t => F ↦ F₀ ↦ F₁ → .. (F₂ → Z) .. )) → Z))
  (at level 98, t at next level, F at level 79, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' '{' F '&' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR2 P₁ P₂ (fun t₁ t₂ => F ↦ F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F at level 79, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' '{' F '&' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => F ↦ F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F at level 79, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' '{' F '&' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => F ↦ F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F at level 79, F₀ at level 79, F₁ at level 79, F₂ at level 79).
Global Notation
  "'Ex₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' '{' F '&' F₀ '&' F₁ '∧' .. '∧' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => F ↦ F₀ ↦ F₁ → .. (F₂ → Z) ..)) → Z))
  (at level 98, right associativity, F at level 79, F₀ at level 79, F₁ at level 79, F₂ at level 79).

(** Combining existential quantifiers and disjonction **)
Global Notation "'Ex₁' t '∈' P ',' '{' F₁ '∨' .. '∨' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR P (fun t => (F₁ → Z) → .. ((F₂ → Z) → Z) .. )) → Z))
  (at level 98, t at next level, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₂' t₁ ',' t₂ '∈' P₁ '×' P₂ ',' '{' F₁ '∨' .. '∨' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR2 P₁ P₂ (fun t₁ t₂ => (F₁ → Z) → .. ((F₂ → Z) → Z) .. )) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₃' t₁ ',' t₂ ',' t₃ '∈' P₁ '×' P₂ '×' P₃ ',' '{' F₁ '∨' .. '∨' F₂ '}'" :=
  (Forall formula (fun Z => (ForallR3 P₁ P₂ P₃ (fun t₁ t₂ t₃ => (F₁ → Z) → .. ((F₂ → Z) → Z) .. )) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation "'Ex₄' t₁ ',' t₂ ',' t₃ ',' t₄ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ ',' '{' F₁ '∨' .. '∨' F₂ '}'" :=
  (Forall formula
    (fun Z => (ForallR4 P₁ P₂ P₃ P₄ (fun t₁ t₂ t₃ t₄ => (F₁ → Z) → .. ((F₂ → Z) → Z) .. )) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
Global Notation
  "'Ex₅' t₁ ',' t₂ ',' t₃ ',' t₄ ',' t₅ '∈' P₁ '×' P₂ '×' P₃ '×' P₄ '×' P₅ ',' '{' F₁ '∨' .. '∨' F₂ '}'" :=
  (Forall formula
    (fun Z => (ForallR5 P₁ P₂ P₃ P₄ P₅ (fun t₁ t₂ t₃ t₄ t₅ => (F₁ → Z) → ..((F₂ → Z) → Z)..)) → Z))
  (at level 98, right associativity, F₁ at level 79, F₂ at level 79).
