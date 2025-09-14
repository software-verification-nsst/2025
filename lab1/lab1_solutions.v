Inductive bool : Type :=
| true
| false.

Definition negb (b: bool) : bool :=
  if b then false else true.

Definition andb (b1 b2: bool) : bool :=
  if b1 then b2 else false.

Definition orb (b1 b2: bool) : bool :=
  if b1 then true else b2.

Lemma unfold_andb : forall b1 b2: bool,
    andb b1 b2 = if b1 then b2 else false.
Proof. intros b1 b2. unfold andb. reflexivity. Qed.

Lemma andb_true_b: forall b: bool,
    andb true b = b.
Proof. intros b. simpl. reflexivity. Qed.

Lemma andb_false_b : forall b: bool,
    andb false b = false.
Proof. intros b. simpl. reflexivity. Qed.

Module NatPlayground.

  Inductive nat : Type :=
  | O
  | S (n: nat).

  Fixpoint plus (n1 n2: nat) : nat :=
    match n1 with
    | O => n2
    | S n1' => S (plus n1' n2)
    end.

  Fixpoint mult (n1 n2: nat) : nat :=
    match n1 with
    | O => O
    | S n1' => plus n2 (mult n1' n2)
    end.

  Lemma plus_O_n: forall n: nat,
      plus O n = n.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.

  Lemma mult_O_l: forall n: nat,
      mult O n = O.
  Proof.
    intros n.
    simpl.
    reflexivity.
  Qed.

  Lemma plus_id: forall n m: nat,
      n = m ->
      plus n n = plus m m.
  Proof.
    intros n m.
    intros Hnm.
    rewrite Hnm.
    reflexivity.
  Qed.

End NatPlayground.

Lemma mult_n_O_m_O: forall p q: nat,
    plus (mult p O) (mult q O) = O.
Proof.
  intros.
  Search (_ * 0).
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Lemma mult_n_1 : forall n: nat,
    mult n (S O) = n.
Proof.
  simpl.
  intros.
  Search (_ * S _).
  rewrite <- mult_n_Sm.
  Search (_ * 0).
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

Lemma andb_b_false : forall b: bool,
    andb b false = false.
Proof.
  intros.
  destruct b eqn:Hb.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma negb_involutive: forall b: bool,
    negb (negb b) = b.
Proof.
  intros.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma andb_commutative: forall b c: bool,
    andb b c = andb c b.
Proof.
  intros.
  destruct b eqn:Hb.
  - simpl. destruct c eqn:Hc.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. destruct c eqn:Hc.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma andb_true_elim: forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Hb.
  - simpl.
    intros.
    rewrite H.
    reflexivity.
  - simpl. intros.
    destruct c eqn:Hc.
    + reflexivity.
    + rewrite H. reflexivity.
Qed.

Lemma students_favorite: forall b : bool,
    b = if b then true else false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint eqb (n1 n2: nat) : bool :=
  match n1 with
  | O =>
      match n2 with
      | O => true
      | S _ => false
      end
  | S n1' =>
      match n2 with
      | O => false
      | S n2' => eqb n1' n2'
      end
  end.

Lemma plus_1_neq_O: forall n: nat,
    eqb (plus n (S O)) O = false.
Proof.
  intros.
  destruct n eqn:Hn.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.
