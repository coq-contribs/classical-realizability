(** Rewriting of the Qabs library for the [Qc] type **)

Require Import Qreduction.
Require Qabs.
Require Export ClassicalRealizability.Qccomplement.

Hint Unfold Qcle Qcplus Qcminus Qcmult Qcdiv Qclt : qarith.


(** ** Absolute value over [Qc] **)

Definition Qcabs (x:Qc) := let (n,d) := x.(this) in (* Qcmake (Qabs.Qabs x.(this)) (Qcanon_abs _). *)
  match n with
    | Z0 => x
    | Zpos m => x
    | Zneg m => (-x)
  end.
Global Notation "| q |" := (Qcabs q) (at level 29, format "| q |", no associativity) : Qc_scope.

Lemma Qcabs_case : forall (x:Qc) (P : Qc -> Type), (0 <= x -> P x) -> (x <= 0 -> P (- x)) -> P (Qcabs x).
Proof.
intros x P H1 H2. unfold Qcabs.
destruct x as [[[|xn|xn] xd] Hx]; simpl; (apply H1 || apply H2; abstract (compute; discriminate)).
Qed.

Instance Qcabs_wd : Proper ((fun x y : Qc => Qeq x y) ==> eq) Qcabs.
intros [[[|xn|xn] xd] Hx] [[[|yn|yn] yd] Hy] H; apply Qc_is_canon; try now simpl in *; rewrite H || inversion H.
change (Qcopp {| this := Zneg xn # xd; canon := Hx |} == Qcopp {| this := Zneg yn # yd; canon := Hy |}).
unfold Qcopp. rewrite H. reflexivity.
Qed.

Lemma Qcabs_0 : forall q, Qcabs q = 0 <-> q = 0.
Proof.
intros [[[] ?] ?].
  reflexivity.
  reflexivity.
  unfold Qcabs. simpl. Qcunfold. do 2 rewrite Qceq_Qeq. rewrite Q2Qc_correct. now split; intro H; inversion H.
Qed.

Lemma Qcabs_pos : forall x, 0 <= x -> Qcabs x = x.
Proof. intros [[[|xn|xn] xd] Hx] H; try reflexivity. unfold Qcle in H. abstract (compute in H; now elim H). Qed.

Lemma Qcabs_neg : forall x, x <= 0 -> Qcabs x = - x.
Proof. intros [[[|xn|xn] xd] Hx] H; apply Qc_is_canon; try reflexivity; abstract (compute in H; now elim H). Qed.

Lemma Qcabs_nonneg : forall x, 0 <= (Qcabs x).
Proof. intro x. apply Qcabs_case. auto. apply (Qcopp_le_compat x 0). Qed.

Lemma Qcabs_Q : forall q, Qcabs q == Qabs.Qabs q.
Proof.
intro q. apply Qcabs_case; unfold Qcle,Qcopp; repeat rewrite Q2Qc_correct;
intro; (now rewrite Qabs.Qabs_pos) || now rewrite Qabs.Qabs_neg.
Qed.

Lemma Zabs_Qcabs : forall n d, Q2Qc (Zabs n#d) = Qcabs (Q2Qc (n#d)).
Proof. intros n d. apply Qc_is_canon. rewrite Qcabs_Q. repeat rewrite Q2Qc_correct. apply Qabs.Zabs_Qabs. Qed.

Lemma Qcabs_opp : forall x, Qcabs (-x) = Qcabs x.
Proof.
intros x. apply Qcabs_case; intro Hx. rewrite Qcabs_neg. reflexivity.
rewrite Qcle_minus_iff in *. now rewrite Qcplus_comm.
rewrite Qcle_minus_iff in *. rewrite Qcopp_involutive in *. rewrite Qcplus_0_l in Hx; now rewrite Qcabs_pos. 
Qed.

Lemma Qcabs_triangle : forall x y : Qc, Qcabs (x+y) <= Qcabs x + Qcabs y.
Proof.
intros x y. unfold Qcle,Qcplus. do 3 apply Qcabs_case; intros Hy Hx Hxy.
- apply Zmult_le_compat_r;auto with *.
- apply Qcplus_le_compat; apply Qcle_refl ||
    (abstract (transitivity 0; easy || now rewrite Qcle_minus_iff in Hy,Hx; rewrite Qcplus_0_l in *)).
- apply Qcplus_le_compat; apply Qcle_refl ||
    (abstract (transitivity 0; easy || now rewrite Qcle_minus_iff in Hy,Hx; rewrite Qcplus_0_l in *)).
- apply Qcplus_le_compat; apply Qcle_refl ||
    (abstract (transitivity 0; easy || now rewrite Qcle_minus_iff in Hy,Hx; rewrite Qcplus_0_l in *)).
- change (- (x + y) <= x + y). transitivity 0.
    rewrite Qcle_minus_iff. rewrite Qcopp_involutive.
      rewrite Qcplus_0_l. rewrite <- Qcplus_0_r at 1. now apply Qcplus_le_compat.
    rewrite <- Qcplus_0_r at 1. now apply Qcplus_le_compat.
- change (- (x + y) <= x + (- y)). rewrite Qcopp_distr_plus. apply Qcplus_le_compat.
  transitivity 0. change 0 with (-0). now apply Qcopp_le_compat. easy. reflexivity.
- change (- (x + y) <= (- x) + y). rewrite Qcopp_distr_plus. apply Qcplus_le_compat.
  reflexivity. transitivity 0. change 0 with (-0). now apply Qcopp_le_compat. easy.
- change (- (x + y) <= (- x) + (- y)). rewrite Qcopp_distr_plus. reflexivity.
Qed.

Lemma Qcabs_mult : forall a b, Qcabs (a*b) = (Qcabs a)*(Qcabs b).
Proof.
intros x y. apply (Qcabs_case x); apply (Qcabs_case y); intros Hy Hx.
- apply Qcabs_pos. now apply Qcmult_resp_nonneg.
- replace (x * (- y)) with (- (x * y)) by ring. apply Qcabs_neg.
  replace (x * y) with (- (x * (- y))) by ring. replace 0 with (- 0) by ring. apply Qcopp_le_compat.
  apply Qcopp_le_compat in Hy. now apply Qcmult_resp_nonneg.
- replace ((- x) * y) with (- (x * y)) by ring. apply Qcabs_neg.
  replace (x * y) with (- ((- x) * y)) by ring. replace 0 with (- 0) by ring. apply Qcopp_le_compat.
  apply Qcopp_le_compat in Hx. now apply Qcmult_resp_nonneg.
- apply Qcopp_le_compat in Hx. apply Qcopp_le_compat in Hy.
  replace (x * y) with (- x * - y) by ring. apply Qcabs_pos. now apply Qcmult_resp_nonneg.
Qed.

Lemma Qcabs_inv : forall a, Qcabs (/ a) = / Qcabs a.
Proof.
intro a. apply (Qcabs_case a); intro Ha.
  apply Qcabs_pos. now rewrite Qcinv_nonneg.
  rewrite Qcinv_opp_comm. apply Qcabs_neg. now rewrite Qcinv_nonpos.
Qed.

Corollary Qcabs_div : forall a b, Qcabs (a / b) = Qcabs a / Qcabs b.
Proof.
intros a b. unfold Qcdiv. rewrite Qcabs_mult. now rewrite Qcabs_inv.
Qed.

Lemma Qcabs_minus x y: Qcabs (x - y) = Qcabs (y - x).
Proof.
setoid_rewrite <- Qcopp_involutive at 2. rewrite Qcabs_opp. unfold Qcminus. rewrite Qcopp_distr_plus.
rewrite Qcopp_involutive. now rewrite Qcplus_comm.
Qed.

Lemma Qcle_abs : forall a, a <= Qcabs a.
Proof.
intro a. apply Qcabs_case; auto with *.
intro. apply Qle_trans with 0; try assumption. change 0 with (-0). now apply Qcopp_le_compat.
Qed.

Lemma Qcabs_triangle_reverse : forall x y, Qcabs x - Qcabs y <= Qcabs (x - y).
Proof.
intros x y.
rewrite Qcle_minus_iff.
setoid_replace (Qcabs (x - y) + - (Qcabs x - Qcabs y)) with ((Qcabs (x - y) + Qcabs y) + - Qcabs x) by ring.
rewrite <- Qcle_minus_iff.
setoid_replace (Qcabs x) with (Qcabs (x-y+y)).
apply Qcabs_triangle.
f_equal. ring.
Qed.

Lemma Qcabs_le_condition x y: Qcabs x <= y <-> -y <= x <= y.
Proof.
split.
  split.
    rewrite <- (Qcopp_involutive x). apply Qcopp_le_compat.
    apply Qcle_trans with (Qcabs (-x)). now apply Qcle_abs. now rewrite Qcabs_opp.
    transitivity (Qcabs x); auto using Qcle_abs.
  intros [? ?]. unfold Qcle. apply Qcabs_case; trivial.
  intros. rewrite <- (Qcopp_involutive y). now apply Qcopp_le_compat.
Qed.

Lemma Qcabs_diff_le_condition x y r: Qcabs (x - y) <= r <-> x - r <= y <= x + r.
Proof.
intros. unfold Qcminus. rewrite Qcabs_le_condition. split; intros [Hle₁ Hle₂]; split;
rewrite Qcle_minus_iff in *; ring_simplify in Hle₁; ring_simplify in Hle₂; ring_simplify.
  now replace (y - x + r) with (r - x + y) by ring.
  now replace (x + r - y) with (x - y + r) by ring.
  now replace (x - y + r) with (x + r - y) by ring.
  now replace (r - x + y) with (y - x + r) by ring.
Qed.

Lemma Qcabs_close : forall x y r, Qcabs (x - y) <= r -> Qcabs x <= Qcabs y + r.
Proof.
intros x y r Hle. rewrite Qcle_minus_iff.
replace (Qcabs y + r + - Qcabs x) with (r + - (Qcabs x - Qcabs y)) by ring.
rewrite <- Qcle_minus_iff. transitivity (Qcabs (x - y)). apply Qcabs_triangle_reverse. easy.
Qed.

Lemma Qabs_pos_not_0 : forall q, 0 < Qcabs q -> q <> 0.
Proof. intros q Hq ?. subst. discriminate Hq. Qed.

Lemma Qcabs_not_0 : forall q, Qcabs q <> 0 -> q <> 0.
Proof. intros q Hq ?. subst. elim Hq. reflexivity. Qed.
