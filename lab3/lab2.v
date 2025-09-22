From Coq Require Import Lia.
From Coq Require Import Bool.Bool.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
Import ListNotations.

From Coq Require Import Recdef.

Module BinTree.

  Inductive bin_tree : Type :=
  | Empty
  | Node (l: bin_tree) (e: nat) (r: bin_tree).

  Fixpoint size (t: bin_tree) : nat :=
    match t with
    | Empty => 0
    | Node l _ r => 1 + size l + size r
    end.

End BinTree.

Definition heap : Type := BinTree.bin_tree.

Definition heap63 : heap :=
  BinTree.Node BinTree.Empty 63 BinTree.Empty.

Definition heap24 : heap :=
  BinTree.Node BinTree.Empty 24 BinTree.Empty.

Definition heap4 : heap :=
  BinTree.Node heap63 4 heap24.

Definition heap44 : heap :=
  BinTree.Node BinTree.Empty 44 BinTree.Empty.

Definition heap28 : heap :=
  BinTree.Node BinTree.Empty 28 BinTree.Empty.

Definition heap23 : heap :=
  BinTree.Node heap44 23 heap28.

Definition heap1 : heap :=
  BinTree.Node heap4 1 heap23.

Definition elt : Type := nat.

Inductive le_root : elt -> heap -> Prop := .
(* FILL HERE, exercise 1 *)

Inductive is_heap : heap -> Prop := .
(* FILL HERE, exercise 2 *)

Definition create : heap := BinTree.Empty.

Lemma create_correct: is_heap create.
Admitted. (* exercise 3 *)

Definition size_two (t: heap * heap) : nat :=
  let (h1, h2) := t in
  BinTree.size h1 + BinTree.size h2.

Function merge (t: heap * heap) {measure size_two t} : heap :=
  match t with
  | (BinTree.Empty, t2) => t2
  | (t1, BinTree.Empty) => t1
  | (BinTree.Node l1 x1 r1 as h1, BinTree.Node l2 x2 r2 as h2) =>
      if x1 <=? x2 then
        BinTree.Node (merge (r1, h2)) x1 l1
      else
        BinTree.Node (merge (r2, h1)) x2 l2
  end.
Proof.
  - intros. simpl in *. lia.
  - intros. simpl in *. lia.
Defined.

Lemma merge_correct :
  forall t h1 h2,
    is_heap h1 -> is_heap h2 ->
    t = (h1, h2) ->
    is_heap (merge t).
Proof.
Admitted. (* exercise 4 *)

Definition add (x: elt) (h: heap) : heap :=
  merge ((BinTree.Node BinTree.Empty x BinTree.Empty), h).

Lemma add_correct: forall x h,
    is_heap h ->
    is_heap (add x h).
Proof.
Admitted. (* exercise 5 *)

Definition remove_min (h: heap) : option heap :=
  match h with
  | BinTree.Empty => None
  | BinTree.Node l _ r => Some (merge (l, r))
  end.

Lemma remove_min_correct: forall h,
    is_heap h ->
    match remove_min h with
    | None => h = BinTree.Empty
    | Some h' => is_heap h'
    end.
Proof.
Admitted. (* exercise 6 *)

From Coq Require Import Extraction.

Recursive Extraction remove_min.
