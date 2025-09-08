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
Proof.
Admitted.

Lemma andb_true_b: forall b: bool,
    andb true b = b.
Proof.
Admitted.

Lemma andb_false_b : forall b: bool,
    andb false b = false.
Proof.
Admitted.

Module NatPlayground.

  Inductive nat : Type :=
  | O
  | S (n: nat).

  Parameter plus: nat -> nat -> nat.
  (** To be completed. Change this header into
      [Fixpoint plus (n1 n2: nat) : nat :=]
      to give your definition. *)

  Parameter mult: nat -> nat -> nat.
  (** To be completed. Change this header into
      [Fixpoint mult (n1 n2: nat) : nat :=]
      to give your definition. *)

  Lemma plus_O_n: forall n: nat,
      plus O n = n.
  Proof.
  Admitted.

  Lemma mult_O_l: forall n: nat,
      mult O n = O.
  Proof.
  Admitted.

  Lemma plus_id: forall n m: nat,
      n = m ->
      plus n n = plus m m.
  Proof.
  Admitted.

End NatPlayground.

Lemma mult_n_O_m_O: forall p q: nat,
    plus (mult p O) (mult q O) = O.
Proof.
Admitted.

Lemma mult_n_1 : forall n: nat,
    mult n (S O) = n.
Proof.
Admitted.

Lemma andb_b_false : forall b: bool,
    andb b false = false.
Proof.
Admitted.

Lemma negb_involutive: forall b: bool,
    negb (negb b) = b.
Proof.
Admitted.

Lemma andb_commutative: forall b c: bool,
    andb b c = andb c b.
Proof.
Admitted.

Lemma andb_true_elim: forall b c : bool,
    andb b c = true -> c = true.
Proof.
Admitted.

Lemma students_favorite: forall b : bool,
    b = if b then true else false.
Proof.
Admitted.

Parameter eqb: nat -> nat -> bool.
(** To be completed. Change this header into
    [Fixpoint eqb (n1 n2: nat) : bool :=]
    to give your definition. *)

Lemma plus_1_neq_O: forall n: nat,
    eqb (plus n (S O)) O = false.
Proof.
Admitted.
