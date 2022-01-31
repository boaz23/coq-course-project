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
I used nat because I did not want to get into defining a partial order relation
on any type.
*)
Fixpoint search_tree (t : tree nat) : Prop :=
  match t with
  | empty => True
  | node l x r => (
    let search_tree_l := search_tree l in
    let l_less_than := match l with
      | empty => True
      | node ll lx lr => lx <= x
    end in
    let search_tree_r := search_tree r in
    let less_than_r := match r with
      | empty => True
      | node rl rx rr => x <= rx
    end in
    search_tree_l /\ l_less_than /\ search_tree_r /\ less_than_r
  )
  end
.

Theorem leaf_search_tree : forall (x : nat),
  search_tree (leaf x).
Proof.
  intros; unfold leaf. simpl. auto.
Qed.

Example search_tree_ex_1 : search_tree (
  node
    (node (node (leaf 2) 4 (leaf 5)) 4 (leaf 6))
    7
    (node empty 7 (leaf 10))
).
Proof.
  simpl. repeat split.
  - apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_n.
  - apply le_n.
  - apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_S. apply le_S. apply le_n.
  - apply le_S. apply le_S. apply le_S. apply le_n.
  - apply le_n.
Qed.

Definition search_tree_neg_1 := node (leaf 5) 8 (leaf 6).

Example search_tree_ex_neg_1 : ~search_tree search_tree_neg_1.
Proof.
  unfold not. simpl. intros.
  destruct H as [_ [_ [_ H_le]]].
  repeat (
    inversion H_le as [n | n H_le' H_n_eq]; subst;
    clear H_le; rename H_le' into H_le
  ).
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

Definition f_const {X Y : Type} (x : X) :=
  fun (y : Y) => x.

Theorem search_tree_const : forall (x : nat) (t : tree nat),
  search_tree (tree_map (f_const x) t).
Proof.
  intros. induction t as [| l IHl tx r IHr].
  - simpl. apply I.
  - destruct l as [| ll lx lr]; destruct r as [| rl rx rr]; simpl; auto.
Qed.

Theorem tree_map_search_tree_counter_ex :
  exists (f : nat -> nat) (t : tree nat),
  search_tree (tree_map f t) /\ ~(search_tree t).
Proof.
  exists (f_const 0). exists search_tree_neg_1. split.
  - apply search_tree_const.
  - exact search_tree_ex_neg_1.
Qed.

Theorem tree_map_search_tree_not_implies_search_tree :
  ~(forall (f : nat -> nat) (t : tree nat),
    search_tree (tree_map f t) -> search_tree t).
Proof.
  pose (H_counter_ex := tree_map_search_tree_counter_ex).
  destruct H_counter_ex as [f [t H_counter]].
  apply dist_exists_not_all. exists f.
  apply dist_exists_not_all. exists t.
  apply not_imp_imp_and. exact H_counter.
Qed.