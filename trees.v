Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From LF Require Import Lists.
From LF Require Import Poly.
Import Lists.

Inductive tree X : Type :=
| empty : tree X
| node : tree X -> X -> tree X -> tree X.

Arguments empty {X}.
Arguments node {X} _ _ _.

Fixpoint in_order {X : Type} (t : tree X) : list X :=
  match t with
  | empty => []
  | node l x r => (in_order l) ++ [x] ++ (in_order r)
  end
.

Definition leaf {X : Type} (x : X) := (node empty x empty).

Definition example_tree : tree nat := (
  node
    (node (leaf 1) 3 (leaf 2))
    0
    (node (leaf 4) 1 (leaf 5))
  )
.

Example in_order_example_1 :
  in_order example_tree = [1; 3; 2; 0; 4; 1; 5].
Proof. reflexivity. Qed.

Fixpoint tree_map {X Y} (f : X -> Y) (t : tree X) : tree Y :=
  match t with
  | empty => empty
  | node l x r => node (tree_map f l) (f x) (tree_map f r)
  end
.

Example tree_map_example_1 :
  tree_map (fun x => [x; 2 * x]) example_tree = (
    node
      (node (leaf [1; 2]) [3; 6] (leaf [2; 4]))
      [0; 0]
      (node (leaf [4; 8]) [1; 2] (leaf [5; 10]))
  ).
Proof. reflexivity. Qed.

Theorem list_map_app_split : forall {X Y : Type} (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1. induction l1 as [| x1 l1' IHl1'].
  - reflexivity.
  - intros. simpl. rewrite -> (IHl1' l2). reflexivity.
Qed.

Lemma tree_map_in_order : forall X Y (f: X -> Y) (t : tree X),
  map f (in_order t) = in_order (tree_map f t).
Proof.
  intros. induction t as [| l IHl x r IHr].
  - reflexivity.
  - simpl. rewrite <- IHl. rewrite <- IHr.
    rewrite -> list_map_app_split. simpl.
    reflexivity.
Qed.

(*
  ****************************************
  ********** true specification **********
  ****************************************
*)

Definition injective {X Y : Type} (f : X -> Y) :=
  forall x y : X, f x = f y -> x = y.

Theorem tree_map_injective : forall {X Y : Type} (f : X -> Y),
  injective f -> injective (tree_map f).
Proof.
  intros X Y f H_f_injective t1 t2; generalize dependent t2.
  induction t1 as [| l1 IHl1 x1 r1 IHr1]; simpl;
  intros t2; destruct t2 as [| l2 x2 r2]; simpl; try discriminate; intros H.
  - reflexivity.
  - injection H as H_eq_map_l H_eq_x H_eq_map_r.
    rewrite <- (IHl1 l2 H_eq_map_l). rewrite <- (H_f_injective x1 x2 H_eq_x).
    rewrite <- (IHr1 r2 H_eq_map_r). reflexivity.
Qed.

(*
(*
A less exciting theorem:
*)
Theorem tree_map_composition : forall
  {X1 X2 X3 : Type} (f1_2 : X1 -> X2) (f2_3 : X2 -> X3) (t : tree X1),
  tree_map f2_3 (tree_map f1_2 t) = tree_map (fun x => f2_3(f1_2 x)) t.
Proof.
  intros. induction t as [| l IHl x r IHr].
  - reflexivity.
  - simpl. rewrite -> IHl. rewrite -> IHr.
    reflexivity.
Qed.
*)


(*
  ****************************************
  ********** false specification *********
  ****************************************

  The actual theorem is all the way down at the bottom.
*)
Definition R_reflexive {X : Type} (R : X -> X -> Prop) :=
  forall (x : X), R x x.
Definition R_anti_symmetric {X : Type} (R : X -> X -> Prop) :=
  forall (x y : X), R x y -> R y x -> x = y.
Definition R_transitive {X : Type} (R : X -> X -> Prop) :=
  forall (x y z : X), R x y -> R y z -> R x z.
Definition R_partial_order {X : Type} (R : X -> X -> Prop) :=
  R_reflexive R /\ R_anti_symmetric R /\ R_transitive R.

(*
  This part of the project isn't about naturals,
  so I just used Coq's library theorems for this one.
*)
Theorem nat_le_partial_order : R_partial_order le.
Proof.
  unfold R_partial_order;
  unfold R_reflexive; unfold R_anti_symmetric; unfold R_transitive.
  split; [| split].
  - apply Nat.le_refl.
  - apply Nat.le_antisymm.
  - apply Nat.le_trans.
Qed.

Fixpoint search_tree {X : Type}
 (R : X -> X -> Prop) (H_po : R_partial_order R)
 (t : tree X) : Prop :=
  match t with
  | empty => True
  | node l x r => (
    let search_tree_l := search_tree R H_po l in
    let l_less_than := match l with
      | empty => True
      | node ll lx lr => R lx x
    end in
    let search_tree_r := search_tree R H_po r in
    let less_than_r := match r with
      | empty => True
      | node rl rx rr => R x rx
    end in
    search_tree_l /\ l_less_than /\ search_tree_r /\ less_than_r
  )
  end
.

Theorem leaf_search_tree : forall {X : Type}
  (R : X -> X -> Prop) (H_po : R_partial_order R) (x : X),
  search_tree R H_po (leaf x).
Proof.
  intros; unfold leaf. simpl. auto.
Qed.

Definition search_tree_nat := search_tree le nat_le_partial_order.

Example search_tree_ex_1 : search_tree_nat (
  node
    (node (node (leaf 2) 4 (leaf 5)) 4 (leaf 6))
    7
    (node empty 7 (leaf 10))
).
Proof.
  unfold leaf. repeat split.
  - apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_n.
  - apply le_n.
  - apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_S. apply le_S. apply le_n.
  - apply le_n.
Qed.

Definition search_tree_neg_1 := node (leaf 5) 8 (leaf 6).

Example search_tree_ex_neg_1 : ~search_tree_nat search_tree_neg_1.
Proof.
  unfold not. simpl. intros.
  destruct H as [_ [_ [_ H_le]]].
  repeat (
    inversion H_le as [n | n H_le' H_n_eq]; subst;
    clear H_le; rename H_le' into H_le
  ).
Qed.

Definition f_const {X Y : Type} (x : X) :=
  fun (y : Y) => x.

Theorem R_reflex_f_const : forall {X : Type} (R : X -> X -> Prop) (x : X),
  R_reflexive R -> forall (x1 x2 : X), R (f_const x x1) (f_const x x2).
Proof.
  intros X R x H_R_reflexive x1 x2.
  unfold f_const; simpl. apply H_R_reflexive.
Qed.

Theorem search_tree_const : forall {X : Type}
  (x : X) (R : X -> X -> Prop) (H_po : R_partial_order R) (t : tree X),
  search_tree R H_po (tree_map (f_const x) t).
Proof.
  intros. induction t as [| l IHl tx r IHr]; simpl.
  - apply I.
  - repeat split; auto.
    destruct l as [| ll lx lr]; simpl; auto.
    + apply R_reflex_f_const. apply H_po.
    + destruct r as [| rl rx rr]; simpl; auto.
      apply R_reflex_f_const. apply H_po.
Qed.

Theorem dist_exists_not_all : forall {X : Type} (P : X -> Prop),
  (exists (x : X), ~ P x) -> ~(forall (x : X), P x).
Proof.
  unfold not; intros X P H_exists_x_not_Px H_forall_x_Px.
  destruct H_exists_x_not_Px as [x H_not_Px].
  apply H_not_Px. apply H_forall_x_Px.
Qed.

Theorem not_imp_imp_and : forall (P Q : Prop),
  P /\ ~Q -> ~(P -> Q).
Proof.
  unfold not; intros P Q H H_P_imp_Q; destruct H as [H_P H_not_Q].
  apply H_not_Q. apply H_P_imp_Q. apply H_P.
Qed.

Theorem tree_map_search_tree_counter_ex :
  exists (f : nat -> nat) (t : tree nat),
  search_tree_nat (tree_map f t) /\ ~(search_tree_nat t).
Proof.
  exists (f_const 0). exists search_tree_neg_1. split.
  - apply search_tree_const.
  - exact search_tree_ex_neg_1.
Qed.

(*
  The false specification
*)
Theorem tree_map_search_tree_not_implies_search_tree :
  ~(forall
      {X : Type} (R : X -> X -> Prop) (H_po : R_partial_order R)
      (f : X -> X) (t : tree X),
    search_tree R H_po (tree_map f t) -> search_tree R H_po t).
Proof.
  pose (H_counter_ex := tree_map_search_tree_counter_ex).
  destruct H_counter_ex as [f [t H_counter]].
  apply dist_exists_not_all. exists nat.
  apply dist_exists_not_all. exists le.
  apply dist_exists_not_all. exists nat_le_partial_order.
  apply dist_exists_not_all. exists f.
  apply dist_exists_not_all. exists t.
  apply not_imp_imp_and. exact H_counter.
Qed.