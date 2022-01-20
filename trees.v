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

Definition example_tree : tree nat := (
  node
    (node (node empty 1 empty) 3 (node empty 2 empty))
    0
    (node (node empty 4 empty) 1 (node empty 5 empty))
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
      (node (node empty [1; 2] empty) [3; 6] (node empty [2; 4] empty))
      [0; 0]
      (node (node empty [4; 8] empty) [1; 2] (node empty [5; 10] empty))
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

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Theorem tree_map_injective : forall {X Y : Type} (f : X -> Y),
  injective f -> injective (tree_map f).
Proof.
  intros X Y f H_f_injective t1 t2; generalize dependent t2.
  induction t1 as [| l1 IHl1 x1 r1 IHr1]; simpl;
  intros t2; destruct t2 as [| l2 x2 r2]; simpl; try discriminate.
  - reflexivity.
  - intros H. injection H as H_eq_map_l H_eq_x H_eq_map_r.
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
