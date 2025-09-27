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

Inductive le_root : elt -> heap -> Prop :=
| le_root_Empty : forall x: nat,
    le_root x BinTree.Empty
| le_root_Node : forall (x y: nat) (l r: heap),
    x <= y ->
    le_root x (BinTree.Node l y r).

Inductive is_heap : heap -> Prop :=
| is_heap_Empty :
  is_heap BinTree.Empty
| is_heap_Node : forall (x: nat) (l r: heap),
    is_heap l ->
    is_heap r ->
    le_root x l ->
    le_root x r ->
    is_heap (BinTree.Node l x r).

Definition create : heap := BinTree.Empty.

Lemma create_correct: is_heap create.
Proof.
  unfold create.
  constructor.
Qed.

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
  intros t.
  (* when we do [T1; T2] this will apply tactic [T1] to the current
     goal and then apply tactic [T2] to the all the generated
     sub-goals. This allows one to write shorter and more readable
     proofs. Instead, one could do only [T1.] (note the '.') and then,
     for each subs-goal, apply [T2]. *)
  functional induction (merge t); intros; simpl; auto.
  - inversion H1; assumption.
  - inversion H1; assumption.
  - constructor.
    + apply IHh with (h1:=r1) (h2:=BinTree.Node l2 x2 r2);
        inversion H1; subst; inversion H; subst; auto.
    + inversion H1; subst; inversion H; subst; auto.
    + destruct r1 eqn:Hr1.
      * rewrite merge_equation. constructor.
        Search (_ <=? _). apply Compare_dec.leb_complete in e0. lia.
      * rewrite merge_equation. Search (_ <=? _).
        destruct (PeanoNat.Nat.leb_spec0 e x2).
        { constructor. inversion H1; subst. inversion H; subst.
          inversion H8; subst. lia. }
        { constructor. apply Compare_dec.leb_complete in e0. lia. }
    + inversion H1; subst. inversion H; subst. auto.
  - constructor.
    + apply IHh with (h1:=r2) (h2:=BinTree.Node l1 x1 r1);
        inversion H1; subst; inversion H0; subst; auto.
    + inversion H1; subst; inversion H0; subst; auto.
    + destruct r2 eqn:Hr2; rewrite merge_equation.
      * constructor.
        Search (_ <=? _). apply Compare_dec.leb_complete_conv in e0.
        lia.
      * destruct (PeanoNat.Nat.leb_spec0 e x1); constructor.
        { inversion H1; subst; inversion H0; subst.
          inversion H8; subst. lia. }
        { apply Compare_dec.leb_complete_conv in e0. lia. }
    + inversion H1; subst; inversion H0; subst; assumption.
Qed.

Definition add (x: elt) (h: heap) : heap :=
  merge ((BinTree.Node BinTree.Empty x BinTree.Empty), h).

Lemma add_correct: forall x h,
    is_heap h ->
    is_heap (add x h).
Proof.
  intros.
  unfold add.
  apply merge_correct with (h1:=BinTree.Node BinTree.Empty x BinTree.Empty) (h2:=h); auto.
  constructor; constructor.
Qed.

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
  intros. destruct h eqn:Hh; simpl; auto.
  inversion H; subst.
  apply merge_correct with (h1:=h0_1) (h2:=h0_2); auto.
Qed.

From Coq Require Import Extraction.

Recursive Extraction remove_min.
