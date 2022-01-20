Set Warnings "-notation-overriden,-parsing".
From Coq Require Import Arith.Arith.
Require Nat.

Inductive euclid : nat -> nat -> nat -> Prop :=
  | stop : forall z, euclid z z z
  | step_a : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
  | step_b : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z
.

Inductive gcd : nat -> nat -> nat -> Prop :=
  | base : forall z, gcd z z z
  | step_a' : forall a b z, gcd a b z -> gcd (a + b) b z
  | step_b' : forall a b z, gcd a b z -> gcd a (a + b) z
.

Theorem plus_n_O : forall (n : nat),
  n = n + 0.
Proof.
  intros. induction n; simpl.
  - reflexivity.
  - f_equal. exact IHn.
Qed.

Theorem add_succ_r : forall (n m : nat),
  n + S m = S (n + m).
Proof.
  intros n. induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

Theorem plus_comm :
  forall (n m : nat), n + m = m + n.
Proof.
  intros n. induction n; intros; simpl.
  - apply plus_n_O.
  - symmetry. rewrite -> IHn. apply add_succ_r.
Qed.

Theorem nat_lte_0_then_eq_0 : forall (b : nat),
  b <= 0 -> b = 0.
Proof.
  intros. destruct b.
  - reflexivity.
  - inversion H.
Qed.

Theorem nat_le_S_implies_le : forall (a b : nat),
  S a <= S b -> a <= b.
Proof.
  intros a b; generalize dependent a.
  induction b as [| b' IHb']; intros; inversion H; subst.
  (* b = 0 *)
  - apply le_n.
  - apply nat_lte_0_then_eq_0 in H1. discriminate H1.
  (* b = S b' *)
  - apply le_n.
  - apply le_S. apply IHb'. exact H1.
Qed.

Theorem nat_gt_implies_gte : forall (a b : nat),
  a > b -> a >= b.
Proof.
  intros a. destruct a; intros.
  - inversion H.
  - unfold ge in *. unfold gt in *.  unfold lt in *.
    apply le_S. apply nat_le_S_implies_le in H.
    exact H.
Qed.

Theorem nat_minus_split : forall (a b : nat),
  a >= b -> a = (a - b) + b.
Proof.
  intros a. induction a as [| a' IHa']; intros.
  - unfold ge in H. rewrite -> (nat_lte_0_then_eq_0 b H).
    reflexivity.
  - destruct b as [| b'].
    + simpl. rewrite <- plus_n_O. reflexivity.
    + simpl. rewrite -> add_succ_r. f_equal.
      apply nat_le_S_implies_le in H. apply IHa'.
      unfold ge. exact H.
Qed.

Theorem euclid_gcd : forall a b z, euclid a b z -> gcd a b z.
Proof.
  intros. induction H as [
    z
    | a b z H_a_gt_b H_step_a IH
    | a b z H_a_lt_b H_step_b IH
  ].
  - constructor.
  - rewrite -> (nat_minus_split a b).
    + apply step_a'. exact IH.
    + apply nat_gt_implies_gte. exact H_a_gt_b.
  - rewrite -> (nat_minus_split b a).
    + rewrite plus_comm. apply step_b'. exact IH.
    + apply nat_gt_implies_gte. unfold gt. exact H_a_lt_b.
Qed.

Lemma noehter_max P :
  (forall a b, (forall a' b', max a' b' < max a b -> P a' b') -> P a b) ->
  forall a b, P a b.
Admitted.

Lemma case_split_3way P : forall a b,
  (a < b -> P a b) -> (a = b -> P a b) -> (a > b -> P a b) -> P a b.
Proof.
(* FILL IN HERE *)
Admitted.

Theorem euclid_terminates : forall a b,
  a > 0 -> b > 0 -> exists z, euclid a b z.
Proof.
(* FILL IN HERE *)
Admitted.
