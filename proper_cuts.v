From Coq Require Import Lists.List.
Import ListNotations.

From Coq Require Import Nat.
From Coq Require Import Lia.

(** Some words of advice/hints before you even get started on the
    assignment:

    - When you have an hypothesis of the form [H : P /\ Q], you want to
      be able to manipulate, individually, [P] and [Q]. Use [destruct
      H] to split the former hypothesis into two individual hypotheses
      [H1 : P] and [H2 : Q].

    - When you have an hypothesis of the form [H: exists x, P], you know
      indeed that there is an [x] that satisfies property [P]. Use
      [destruct H] to introduce just argument in your context.

    - When faced with a goal of the form [P /\ Q], you want to focus
      first on the proof of [P] and then on the proof of [Q]. In other
      words, you want to generate two cases, one for the proof of [P]
      the other for the proof of [Q]. Use [split] to instruct Rocq to
      generate such cases.

    - When faced with a goal of the form [P <-> Q], this stands for the
      equivalence of [P] with [Q]. This is exactly as if you were
      trying to prove two different lemmas: first that [P -> Q], and
      then that [Q -> P]. Use [split] to instruct Rocq to generate such
      cases.

    - When faced with a goal of the form [exists x, P], you want to find
      out some witness (in other words, a value) that satisfies
      [P]. When you find out such a value, lets call it [y], you just
      need to do [exists y] and the proof will continue with goal [P] where
      every occurrence of [x] has been replaced by [y].

    - From time to time, you find yourself with an hypothesis [H : P]
      where you know [P] is a false statement, i.e., a
      contradiction. That is fine, sometimes this just stands for an
      unreachable point in your implementation or proof. In that case,
      use [discriminate H] in order to instruct Rocq to exploit such a
      contradiction and finish the proof (remember: with a
      contradiction as an hypothesis everything can be proved, so the
      proof finishes immediately as soon as you are able to convince
      Rocq [H] is indeed a contradiction).

    - Do not forget that you can use other Lemmas during your
      proofs. In fact, for some of the exercises, you are supposed to
      use Lemmas that you have already proved. Also, you should be
      able to use some auxiliary Lemmas from the Rocq Standard
      Library. The [Search] command can help you find useful Lemmas
      already proved (either your own or from Rocq). *)

Definition injective [A B: Type] (f: A -> B) : Prop :=
  forall x x': A, x <> x' -> f x <> f x'.

Inductive distinct {A: Type}: list A -> Prop := .
(* FILL HERE, exercise 1 *)

(* A [Parameter] definition in Rocq works like an axiom: some result
   that you can use without proving it. *)
Parameter injective_map: forall [A B: Type] (f: A -> B) (l: list A),
    distinct l -> injective f -> distinct (map f l).
(* BONUS EXERCISE: if you want to try and prove the [injective_map]
   result, then simply replace the [Parameter] keyword by [Lemma]. *)

Definition cut [A: Type] (l1 l2: list A) (l: list A) : Prop :=
  l1 ++ l2 = l.

Definition cut_list (A: Type) : Type := list (list A * list A).

Definition proper_cuts_prop {A: Type} (c: cut_list A) (l: list A) : Prop :=
  distinct c /\ forall (l1 l2: list A), In (l1, l2) c -> cut l1 l2 l.

Definition cons {A: Type} (x: A) (l: (list A * list A)) : (list A * list A) :=
  let (l1, l2) := l in (x :: l1, l2).

Fixpoint proper_cuts {A: Type} (l: list A) : cut_list A :=
  match l with
  | [] => [([], [])]
  | x :: xs =>
    let pr := proper_cuts xs in
    let r := map (cons x) pr in
    ([], l) :: r
  end.

Lemma injective_cons : forall {A: Type} (x: A),
    injective (cons x).
Proof.
Admitted. (* FILL HERE, exercise 2 *)

Lemma proper_cuts_cons : forall {A: Type} (x: A) (l1 l2 l1' l2': list A) (l: list A),
    cut l1 l2 l ->
    cons x (l1, l2) = (l1', l2') ->
    cut l1' l2' (x::l).
Proof.
Admitted. (* FILL HERE, exercise 3 *)

Lemma map_cons : forall {A: Type} (x: A) (l1 l2: list A) (l: cut_list A),
    In (l1, l2) (map (cons x) l) <->
    (exists s1: list A, l1 = x :: s1 /\ In (s1, l2) l).
Proof.
  intros A x l1 l2 l.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent x.
  induction l.
  - (* l = [] *)
    intros x l2 l1. split.
    + (* -> *)
      intros HIn. simpl in *. contradiction.
    + (* <- *)
      intros HExists. destruct HExists.
      destruct H. simpl in *. contradiction.
  - (* l = a :: l *)
    intros x l2 l1. split.
    + (* -> *)
      intros HIn. simpl in *. destruct HIn.
      * unfold cons in H. destruct a eqn:Ha.
        inversion H. exists l0. split.
        { reflexivity. }
        { left. reflexivity. }
      * apply IHl in H. destruct H. destruct H.
        exists x0. split.
        { assumption. }
        { right. assumption. }
    + (* <- *)
      intros HExists. destruct HExists. destruct H.
      simpl in *. destruct H0.
      * subst. simpl. left. reflexivity.
      * right. apply IHl. exists x0. split.
        { assumption. }
        { assumption. }
Qed.

Lemma proper_cuts_correct : forall {A: Type} (l: list A),
    proper_cuts_prop (proper_cuts l) l.
Proof.
Admitted. (* FILL HERE, exercise 5 *)
