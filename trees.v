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
