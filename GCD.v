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
  n + 0 = n.
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
  intros n. induction n; intros; simpl; symmetry.
  - apply plus_n_O.
  - rewrite -> IHn. apply add_succ_r.
Qed.

Theorem minus_n_O : forall (n : nat),
  n - 0 = n.
Proof.
  intros. destruct n; reflexivity.
Qed.

Theorem nat_le_0 : forall (b : nat),
  b <= 0 -> b = 0.
Proof.
  intros. destruct b.
  - reflexivity.
  - inversion H.
Qed.

Theorem le_0_n : forall (b : nat),
  0 <= b.
Proof.
  intros. induction b.
  - apply le_n.
  - apply le_S. exact IHb.
Qed.

Theorem le_n_S : forall (a b : nat),
  a <= b -> S a <= S b.
Proof.
  intros. induction H as [| b H IHle].
  - apply le_n.
  - apply le_S. exact IHle.
Qed.

Tactic Notation "le_inversion" constr(H) "H1" "a'" "H_S" :=
  inversion H as [H1 | a' H1 H_S]; clear H; rename H1 into H; subst
.

Theorem le_S_n : forall (a b : nat),
  S a <= S b -> a <= b.
Proof.
  intros a b; generalize dependent a.
  induction b as [| b' IHb']; intros; le_inversion H H1 a' H_S.
  (* b = 0 *)
  - (* a = b *)
    apply le_n.
  - (* a = S a *)
    inversion H.
  (* b = S b' *)
  - (* a = b *)
    apply le_n.
  - (* a = S a *)
    apply le_S. apply IHb'. exact H.
Qed.

Theorem lt_le_incl : forall (a b : nat),
  a < b -> a <= b.
Proof.
  intros. unfold lt in *. destruct b.
  - inversion H.
  - apply le_S. apply le_S_n. exact H.
Qed.

Theorem lt_n_S : forall (a b : nat),
  a < b -> S a < S b.
Proof.
  intros. unfold lt in *.
  apply le_n_S. exact H.
Qed.

Theorem lt_S_n : forall (a b : nat),
  S a < S b -> a < b.
Proof.
  intros. unfold lt in *.
  apply le_S_n. exact H.
Qed.

Theorem lt_lt_succ_r : forall (a b : nat),
  a < b -> a < S b.
Proof.
  intros a b H.
  unfold lt. apply le_n_S. apply lt_le_incl. exact H.
Qed.

Theorem lt_0_n : forall (n : nat),
  0 < S n.
Proof.
  intros. unfold lt. apply le_n_S. apply le_0_n.
Qed.

Theorem eq_le_incl : forall (a b : nat),
  a = b -> a <= b.
Proof.
  intros. subst. apply le_n.
Qed.

(* sub_lt *)
Theorem minus_lt : forall (a b : nat),
  b <= a -> 0 < b -> a - b < a.
Proof.
  intros a b H_le H_b; generalize dependent a. unfold lt.
  induction b; intros; [inversion H_b |].
  destruct a; simpl; clear H_b; [inversion H_le | destruct b].
  - rewrite -> minus_n_O. apply le_n.
  - apply le_S. apply IHb.
    + apply lt_0_n.
    + apply le_S_n. exact H_le.
Qed.

Theorem minus_lt_S : forall (a b : nat),
  b < a -> a - S b < a.
Proof.
  intros. apply minus_lt.
  - fold (lt b a). exact H.
  - unfold lt. apply le_n_S. apply le_0_n.
Qed.

(* le_plus_minus *)
Theorem nat_minus_split : forall (a b : nat),
  b <= a -> a = (a - b) + b.
Proof.
  intros a. induction a; intros.
  - rewrite -> (nat_le_0 b).
    + reflexivity.
    + exact H.
  - destruct b; simpl.
    + rewrite -> plus_n_O. reflexivity.
    + rewrite -> add_succ_r. f_equal.
      apply IHa. apply le_S_n. exact H.
Qed.

(* ********** End of basic Nat properties ********** *)

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
    + unfold gt in H_a_gt_b. apply lt_le_incl. exact H_a_gt_b.
  - rewrite -> (nat_minus_split b a).
    + rewrite plus_comm. apply step_b'. exact IH.
    + apply lt_le_incl. exact H_a_lt_b.
Qed.

Lemma noehter_max P :
  (forall a b, (forall a' b', max a' b' < max a b -> P a' b') -> P a b) ->
  forall a b, P a b.
Admitted.

Definition noether_max_h P a b :=
  (forall a' b', max a' b' < max a b -> P a' b') -> P a b.

Theorem leb_S_n : forall (a b : nat),
  (S a <=? S b) = true -> (a <=? b) = true.
Proof.
  intros a b.
  destruct b; simpl; intros; exact H.
Qed.

Theorem ltb_S_n : forall (a b : nat),
  (S a <? S b) = true -> (a <? b) = true.
Proof.
  intros a b. unfold Nat.ltb.
  apply (leb_S_n (S a) b).
Qed.

Theorem leb_S_n_false : forall (a b : nat),
  (S a <=? S b) = false -> (a <=? b) = false.
Proof.
  intros a b H.
  simpl in H. exact H.
Qed.

Theorem ltb_S_n_false : forall (a b : nat),
  (S a <? S b) = false -> (a <? b) = false.
Proof.
  unfold Nat.ltb; intros a b H.
  apply (leb_S_n_false (S a) b). exact H.
Qed.

Theorem nat_ltb_eqb_false_leb_false : forall (a b : nat),
  (a <? b) = false -> (a =? b) = false -> (a <=? b) = false.
Proof.
  intros a b H_lt H_eq; generalize dependent a.
  induction b; intros.
  - destruct a.
    + discriminate H_eq.
    + reflexivity.
  - destruct a.
    + discriminate H_lt.
    + simpl. apply IHb.
      * apply ltb_S_n_false. exact H_lt.
      * simpl in H_eq. exact H_eq.
Qed.

Definition nat_order_bool_prop (a b : nat) :=
  orb (a <? b) (orb (a =? b) (negb (a <=? b))) = true.

Theorem nat_order_decidable_b : forall (a b : nat),
  nat_order_bool_prop a b.
Proof.
  intros a b; unfold nat_order_bool_prop.
  destruct (a <? b) eqn:E_lt; try reflexivity; simpl.
  destruct (a =? b) eqn:E_eq; try reflexivity; simpl.
  destruct (a <=? b) eqn: E_leb; try reflexivity; simpl.
  pose (H_leb_false := (nat_ltb_eqb_false_leb_false a b E_lt E_eq)).
  rewrite -> H_leb_false in E_leb.
  discriminate E_leb.
Qed.

Theorem nat_ltb_lt : forall (a b : nat),
  (a <? b) = true -> a < b.
Proof.
  intros a b H; generalize dependent a.
  induction b; simpl; intros.
  - destruct a; discriminate H.
  - destruct a.
    + apply lt_0_n.
    + apply lt_n_S. apply IHb. apply ltb_S_n. exact H.
Qed.

Theorem nat_leb_le : forall (a b : nat),
  (a =? b) = true -> a = b.
Proof.
  intros a b H; generalize dependent b.
  induction a; intros.
  - destruct b.
    + reflexivity.
    + discriminate H.
  - destruct b.
    + discriminate H.
    + f_equal. apply IHa. simpl in H. exact H.
Qed.

Theorem nat_gtb_gt : forall (a b : nat),
  negb (a <=? b) = true -> a > b.
Proof.
  intros a b H. destruct (a <=? b) eqn:H_leb.
  + discriminate H.
  + clear H; rename H_leb into H. unfold gt. generalize dependent b.
    induction a; intros.
    - discriminate H.
    - destruct b.
      * apply lt_0_n.
      * simpl in H. apply lt_n_S. apply IHa. exact H.
Qed.

Lemma case_split_3way P : forall a b,
  (a < b -> P a b) -> (a = b -> P a b) -> (a > b -> P a b) -> P a b.
Proof.
  intros a b H_P_lt H_P_eq H_P_gt.
  destruct (a <? b) eqn:H_ltb;
  [| destruct (a =? b) eqn:H_eqb;
  [| destruct (negb (a <=? b)) eqn:H_gtb]].
  - apply H_P_lt. apply nat_ltb_lt. exact H_ltb.
  - apply H_P_eq. apply nat_leb_le. exact H_eqb.
  - apply H_P_gt. apply nat_gtb_gt. exact H_gtb.
  - pose (H_nat_order_bool := (nat_order_decidable_b a b));
    unfold nat_order_bool_prop in H_nat_order_bool.
    rewrite -> H_ltb in H_nat_order_bool.
    rewrite -> H_eqb in H_nat_order_bool.
    rewrite -> H_gtb in H_nat_order_bool.
    discriminate H_nat_order_bool.
Qed.

Definition euclid_terminates_prop_S (a b : nat) :=
  exists z, euclid (S a) (S b) z.

Theorem euclid_symm_aux : forall (a b z : nat),
  euclid a b z -> euclid b a z.
Proof.
  intros. induction H as [
    z
    | a b z H_order H_euclid
    | a b z H_order H_euclid
  ]; simpl;
  [apply stop | apply step_b | apply step_a];
  try (apply H_order; exact H_order);
  try exact IHH_euclid.
Qed.

Theorem max_symm : forall (a b : nat),
  max a b = max b a.
Proof.
  intros a. induction a; simpl; intros.
  - destruct b; reflexivity.
  - destruct b; simpl.
    + reflexivity.
    + f_equal. apply IHa.
Qed.

Theorem max_le_r : forall (a b : nat),
  a <= b -> max a b = b.
Proof.
  intros a b; generalize dependent a.
  induction b; intros; simpl.
  - rewrite -> (nat_le_0 a).
    + reflexivity.
    + exact H.
  - destruct a; simpl.
    + reflexivity.
    + f_equal. apply IHb. apply le_S_n. exact H.
Qed.

Theorem max_le_l : forall (a b : nat),
  b <= a -> max a b = a.
Proof.
  intros. rewrite -> max_symm. apply max_le_r. exact H.
Qed.

Definition max_either_prop (a b : nat) := max a b = a \/ max a b = b.

Theorem max_either : forall (a b : nat),
  max_either_prop a b.
Proof.
  intros. apply (case_split_3way max_either_prop); unfold max_either_prop;
  intros H; [right | left; symmetry in H | left; unfold gt in H].
  - apply max_le_r. apply lt_le_incl. exact H.
  - apply max_le_l. apply eq_le_incl. exact H.
  - apply max_le_l. apply lt_le_incl. exact H.
Qed.

Theorem max_lt_n : forall (a b n : nat),
  a < n /\ b < n -> max a b < n.
Proof.
  intros a b n [H_a H_b].
  destruct (max_either a b) as [H_max | H_max];
  rewrite -> H_max; assumption.
Qed.

Theorem lt_max_lt_S_r : forall (a b : nat),
  a < b -> max a (b - S a) < max a b.
Proof.
  intros a b H.
  rewrite -> (max_le_r a b).
  - apply max_lt_n. split; [| apply minus_lt_S]; exact H.
  - apply lt_le_incl. exact H.
Qed.

Theorem nat_minus_1 : forall (b : nat),
  b > 0 -> S (b - 1) = b.
Proof.
  intros b H. destruct b.
  - inversion H.
  - clear H. simpl. rewrite -> minus_n_O. reflexivity.
Qed.

Theorem nat_S_of_minus_S : forall (a b : nat),
  a < b -> S (b - S a) = b - a.
Proof.
  intros a b H; generalize dependent b.
  induction a; intros.
  - rewrite -> nat_minus_1.
    + rewrite -> minus_n_O. reflexivity.
    + unfold gt. exact H.
  - destruct b.
    + inversion H.
    + simpl. apply IHa. apply lt_S_n. exact H.
Qed.

Theorem find_euclid_n_lt : forall (a b : nat),
  a < b -> noether_max_h euclid_terminates_prop_S a b.
Proof.
  unfold noether_max_h. unfold euclid_terminates_prop_S.
  intros a b H_order H_noether_max.
  destruct (H_noether_max a (b - S a)) as [x H_euclid].
  - apply lt_max_lt_S_r. exact H_order.
  - exists x. apply step_b.
    + apply lt_n_S. exact H_order.
    + simpl. rewrite <- nat_S_of_minus_S; assumption.
Qed.

Theorem find_euclid_n_eq : forall (a b : nat),
  a = b -> noether_max_h euclid_terminates_prop_S a b.
Proof.
  unfold noether_max_h. unfold euclid_terminates_prop_S.
  intros a b H_order H_noether_max. subst b.
  exists (S a). apply stop.
Qed.

Theorem find_euclid_n_gt : forall (a b : nat),
  a > b -> noether_max_h euclid_terminates_prop_S a b.
Proof.
  intros a b H_order H_noether_max.
  rewrite -> max_symm in H_noether_max.
  pose (H_z := find_euclid_n_lt b a).
  destruct H_z; auto. unfold euclid_terminates_prop_S.
  exists x. apply (euclid_symm_aux (S b) (S a) x). exact H.
Qed.

Theorem find_euclid_n : forall (a b : nat),
  noether_max_h euclid_terminates_prop_S a b.
Proof.
  unfold noether_max_h. unfold euclid_terminates_prop_S.
  pose (P := euclid_terminates_prop_S).
  intros a b H_noether_max.
  apply (case_split_3way P); unfold P;
  unfold euclid_terminates_prop_S;
  intros H_order; [
    apply find_euclid_n_lt
    | apply find_euclid_n_eq
    | apply find_euclid_n_gt
  ]; auto.
Qed.

Theorem euclid_terminates : forall a b,
  a > 0 -> b > 0 -> exists z, euclid a b z.
Proof.
  intros a b H_a H_b.
  destruct a; [inversion H_a |]; destruct b; [inversion H_b |];
  clear H_a H_b; pose (P := euclid_terminates_prop_S).
  apply (noehter_max P). apply find_euclid_n.
Qed.
