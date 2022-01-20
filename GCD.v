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

Theorem nat_le_0 : forall (b : nat),
  b <= 0 -> b = 0.
Proof.
  intros. destruct b.
  - reflexivity.
  - inversion H.
Qed.

Theorem le_n_S : forall (a b : nat),
  a <= b -> S a <= S b.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. exact IHle.
Qed.

Theorem le_S_n : forall (a b : nat),
  S a <= S b -> a <= b.
Proof.
  intros a b; generalize dependent a.
  induction b as [| b' IHb']; intros; inversion H; subst.
  (* b = 0 *)
  - apply le_n.
  - apply nat_le_0 in H1. discriminate H1.
  (* b = S b' *)
  - apply le_n.
  - apply le_S. apply IHb'. exact H1.
Qed.

Theorem le_0_n : forall (b : nat),
  0 <= b.
Proof.
  intros. induction b.
  - apply le_n.
  - apply le_S. exact IHb.
Qed.

Theorem lt_le_incl : forall (a b : nat),
  a < b -> a <= b.
Proof.
  intros a. destruct a; intros.
  - apply le_0_n.
  - unfold lt in *. destruct b.
    + inversion H.
    + apply le_S_n in H.
      apply le_S. exact H.
Qed.

Theorem gt_ge_incl : forall (a b : nat),
  a > b -> a >= b.
Proof.
  intros a. destruct a; intros.
  - inversion H.
  - unfold ge in *. unfold gt in *.
    apply lt_le_incl. exact H.
Qed.

Theorem nat_minus_split : forall (a b : nat),
  a >= b -> a = (a - b) + b.
Proof.
  intros a. induction a as [| a' IHa']; intros.
  - unfold ge in H. rewrite -> (nat_le_0 b H).
    reflexivity.
  - destruct b as [| b'].
    + simpl. rewrite <- plus_n_O. reflexivity.
    + simpl. rewrite -> add_succ_r. f_equal.
      apply le_S_n in H. apply IHa'.
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
    + apply gt_ge_incl. exact H_a_gt_b.
  - rewrite -> (nat_minus_split b a).
    + rewrite plus_comm. apply step_b'. exact IH.
    + apply gt_ge_incl. unfold gt. exact H_a_lt_b.
Qed.

Definition noether_max_h P a b :=
  (forall a' b', max a' b' < max a b -> P a' b') -> P a b.

Lemma noehter_max P :
  (forall a b, (forall a' b', max a' b' < max a b -> P a' b') -> P a b) ->
  forall a b, P a b.
Admitted.

Lemma case_split_3way P : forall a b,
  (a < b -> P a b) -> (a = b -> P a b) -> (a > b -> P a b) -> P a b.
Proof.
(* FILL IN HERE *)
Admitted.

Definition euclid_terminates_prop   (a b : nat) := exists z, euclid a b z.
Definition euclid_terminates_prop_S (a b : nat) := exists z, euclid (S a) (S b) z.

Theorem max_lt : forall (a b : nat),
  a <= b -> b = max a b.
Proof.
  intros a b; generalize dependent a.
  induction b; intros; simpl.
  - rewrite -> (nat_le_0 a H). reflexivity.
  - destruct a.
    + reflexivity.
    + simpl. f_equal. apply IHb. apply le_S_n. exact H.
Qed.


Theorem noether_max_euclid_terminates : forall (a b : nat),
  noether_max_h euclid_terminates_prop_S a b.
Proof.
(*
  unfold noether_max_h. pose (P := euclid_terminates_prop).
  unfold euclid_terminates_prop.
  intros a b H_a H_b H_noether_max.
  destruct a.
  - inversion H_a.
  - destruct b.
    + inversion H_b.
    +
  apply (case_split_3way P).
  - intros H_lt. (*rewrite <- (max_lt a b (lt_le_incl a b H_lt)) in *.*)
  - intros H_eq. symmetry in H_eq. subst.
    exists a. apply stop.
  - intros H_gt. give_up.
*)
Admitted.

Theorem euclid_terminates : forall a b,
  a > 0 -> b > 0 -> exists z, euclid a b z.
Proof.
  intros a b H_a H_b.
  pose (P := euclid_terminates_prop_S).
  destruct a.
  - inversion H_a.
  - destruct b.
    + inversion H_b.
    + apply (noehter_max P). apply noether_max_euclid_terminates.
Admitted.
