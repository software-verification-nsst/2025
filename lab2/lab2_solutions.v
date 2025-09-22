From Coq Require Import Nat. (* Library on natural numbers *)
From Coq Require Import Bool.Bool. (* Library on Boolean values *)
From Coq Require Import Lia. (* Linear integer arithmetic decision procedure *)
From Coq Require Import Lists.List. (* Library on lists *)
Import ListNotations. (* Syntactic-sugar for list values *)

Lemma add_0_r : forall n: nat,
    n + 0 = n.
Proof. (* lia. *)
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.simpl

Lemma mult_0_r : forall n: nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n.
  - auto.
  - auto.
Qed.

Lemma plus_n_Sm : forall n m: nat,
    S (n + m) = n + S m.
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    reflexivity.
Qed.

Lemma add_comm : forall n m: nat,
    n + m = m + n.
Proof. (* lia. *)
  intros n m.
  induction n.
  - rewrite add_0_r.
    reflexivity.
  - simpl. rewrite IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Lemma add_assoc : forall n m p: nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    reflexivity.
Qed.

Fixpoint power (n: nat) (m: nat) : nat :=
  match m with
  | O => S O
  | S m' => mult n (power n m')
  end.

Fixpoint pow (n: nat) (m: nat) (r: nat) : nat :=
  match m with
  | O => r
  | S m' => pow n m' (r * n)
  end.

Lemma pow_correct : forall n m r: nat,
    pow n m r = r * power n m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros n r. simpl. lia.
  - intros n r. simpl.
    rewrite IHm. lia.
Qed.

Definition power_alt (n: nat) (m: nat) : nat :=
  pow n m 1.

Lemma power_alt_correct : forall n m: nat,
    power n m = power_alt n m.
Proof.
  intros n m.
  unfold power_alt.
  rewrite pow_correct.
  lia.
Qed.

Fixpoint fact (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => n * fact n'
  end.

Fixpoint fact_acc (n: nat) (a: nat) : nat :=
  match n with
  | O => a
  | S n' => fact_acc n' (n * a)
  end.

Lemma fact_acc_power : forall n a: nat,
    fact_acc n a = a * fact n.
Proof.
  intros n.
  induction n.
  - intros a. simpl. lia.
  - intros a. simpl.
    rewrite IHn. lia.
Qed.

Definition fact_alt (n: nat) : nat :=
  fact_acc n 1.

Lemma fact_alt_correct : forall n: nat,
    fact_alt n = fact n.
Proof.
  intros n.
  unfold fact_alt.
  rewrite fact_acc_power.
  lia.
Qed.

Lemma nil_app: forall l : list nat,
    [ ] ++ l  = l.
Proof. intros l. simpl. reflexivity. Qed.

Lemma app_assoc : forall l1 l2 l3: list nat,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1.
  induction l1.
  - intros l2 l3. reflexivity.
  - intros l2 l3. simpl.
    rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l: list nat) : list nat :=
  match l with
  | [ ] => [ ]
  | h :: t => rev t ++ [h]
  end.

Lemma app_nil_r : forall l : list nat,
    l ++ [ ] = l.
Proof.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    reflexivity.
Qed.

Lemma rev_length : forall l: list nat,
    length (rev l) = length l.
Proof.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. Search (length (_ ++ _)).
    rewrite app_length.
    rewrite IHl. simpl.
    lia.
Qed.

Lemma rev_app_distr : forall l1 l2 : list nat,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1.
  induction l1.
  - intros l2. simpl. rewrite app_nil_r.
    reflexivity.
  - intros l2. simpl. rewrite IHl1.
    rewrite app_assoc. reflexivity.
Qed.

Lemma rev_involutive : forall l : list nat,
    rev (rev l) = l.
Proof.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr.
    simpl. rewrite IHl.
    reflexivity.
Qed.

Inductive tree : Type :=
  | Leaf : tree
  | Node (l: tree) (v: nat) (r: tree).

Fixpoint mirror (t: tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r =>
      Node (mirror r) v (mirror l)
  end.

Example mirror1 : mirror Leaf = Leaf.
Proof. reflexivity. Qed.

Example mirror2 :
  mirror (Node (Node Leaf 0 Leaf) 1 (Node Leaf 2 Leaf)) =
    Node (Node Leaf 2 Leaf) 1 (Node Leaf 0 Leaf).
Proof. reflexivity. Qed.

Lemma mirror_involutive: forall t: tree,
    mirror (mirror t) = t.
Proof.
  intros t.
  induction t.
  - simpl. reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.
