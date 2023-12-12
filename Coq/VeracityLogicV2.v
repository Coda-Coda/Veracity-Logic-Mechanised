Require Import List.
Import ListNotations.
Require Import QArith.
Require Import QArith.Qminmax.

Section VeracityLogic.

Inductive actor :=
  | Actor (a : nat).

Inductive basic_claim :=
  | Atomic_Claim (name : nat)
  | Trusts (a : actor).

Inductive claim :=
  | Atomic (c : basic_claim)
  | And (c1 c2 : claim)
  | OrL  (c1 c2 : claim)
  | OrR  (c1 c2 : claim)
  | Or (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Inductive trusted_claim :=
  | Trusted (weight : Q) (c : claim).


Infix "/\'" := And (at level 80, right associativity).
Infix "\/L" := OrL (at level 85, right associativity). 
Infix "\/R" := OrR (at level 85, right associativity). 
Infix "\/'" := OrR (at level 85, right associativity). 

Reserved Notation "P |- A ~> B @ W" (at level 80).
Inductive Believes (Ps : list (actor * basic_claim)) : actor -> claim -> Q -> Prop :=
  | assumed (a : actor) (C : basic_claim) (H : List.In (a, C) Ps) : Ps |- a ~> (Atomic C) @ 1.0
  (* bot_elim is implied by there being no rule for Believing bottom. *)
  | and_intro (a : actor) (C1 C2 : claim) (w1 w2 : Q)

                  (e1 : Ps |- a ~> C1 @ w1) (e2 : Ps |- a ~> C2 @ w2)
                                :
                          Ps |- a ~> (C1 /\' C2) @ Qmin w1 w2

  | and_elim1 (a : actor) (C1 C2 : claim) (w : Q)

                  (e : Ps |- a ~> (C1 /\' C2) @ w)
                           :
                        Ps |- a ~> C1 @ w

  | and_elim2 (a : actor) (C1 C2 : claim) (w:Q)

                  (e : Ps |- a ~> (C1 /\' C2) @ w)
                           :
                        Ps |- a ~> C2 @ w

  | or_intro1 (a : actor) (C1 C2 : claim) (w : Q)

                      (e : Ps |- a ~> C1 @ w)
                           :
                    Ps |- a ~> (C1 \/L C2) @ w

  | or_intro2 (a : actor) (C1 C2 : claim) (w : Q)

                      (e : Ps |- a ~> C2 @ w)
                           :
                    Ps |- a ~> (C1 \/R C2) @ w

  | or_elim1 (a : actor) (C1 C2 : claim) (w : Q)

                  (e : Ps |- a ~> (C1 \/L C2) @ w)
                           :
                         Ps |- a ~> C1 @ w

  | or_elim2 (a : actor) (C1 C2 : claim) (w : Q)

                  (e : Ps |- a ~> (C1 \/R C2) @ w)
                           :
                         Ps |- a ~> C2 @ w

  | or_detag1 (a : actor) (C1 C2 : claim) (w : Q)

                  (e : Ps |- a ~> (C1 \/L C2) @ w)
                           :
                     Ps |- a ~> (C1 \/' C2) @ w

  | or_detag2 (a : actor) (C1 C2 : claim) (w : Q)

                  (e : Ps |- a ~> (C1 \/R C2) @ w)
                           :
                    Ps |- a ~> (C1 \/' C2) @ w

  | trust (a1 a2 : actor) (C : claim) (w1 w2 : Q)

                (e : Ps |- a2 ~> C @ w1) (eT : Ps |- a1 ~> (Atomic (Trusts a2)) @ w1)
                              :
                        Ps |- a1 ~> C @ w1*w2

(* impl_intro, when partially applied up to just before e2, has a similar meaning
   to the Isabelle equivalent. *)
  | impl_intro (a : actor) (C1 C2 : claim) (w : Q)
                       (e1 : Ps |- a ~> C1 @ 1) (e2 : Ps |- a ~> C2 @ w)
                                           :
                               Ps |- a ~> (Implies C1 C2) @ w
  (** TODO, think about the weight for impl_intro here. *)

where "P |- A ~> B @ W " := (Believes P A B W).

Notation "P |- A ~~> B" := (Believes P A B 1)  (at level 80).

(** * Examples: Incorrect Statements *)

Lemma incorrect_example1 : forall a C, ~ ([] |- a ~~> C).
Proof.
unfold not.
intros.
induction H.
simpl in H.
all: contradiction.
Qed.

(** Here, the antecedent is false (see incorrect_example1). So this is provable. *)
Lemma incorrect_example2 : forall a C1 C2,
   ([] |- a ~~> C1 -> [] |- a ~~> (C1 /\' C2)).
Proof.
intros.
apply incorrect_example1 in H.
contradiction.
Qed.

(** * Examples: Correct Statements *)

Lemma example1_old_version : forall a C1 C2 C3,

       [] |- a ~~> C1 /\ [] |- a ~~> C2 /\ [] |- a ~~> C3
                               ->
            [] |- a ~~> ((C1 /\' C2) /\' C3)
.
Proof.
intros.
destruct H as [H1 [H2 H3]].
apply incorrect_example1 in H1.
contradiction.
Qed.

Lemma example1 : forall a C1 C2 C3 Ps,

       Ps |- a ~~> C1 /\ Ps |- a ~~> C2 /\ Ps |- a ~~> C3
                               ->
            Ps |- a ~~> ((C1 /\' C2) /\' C3)
.
Proof.
intros.
destruct H as [H1 [H2 H3]].
pose proof (and_intro Ps a C1 C2 1 1).
compute in H.
pose proof (and_intro Ps a (C1 /\' C2) C3 1 1).
compute in H0.
apply H0.
apply H.
all: assumption.
Qed.

Lemma example2 : forall a1 a2 C1 C2 Ps,

             (Ps |- a1 ~~> C1) /\ (Ps |- a2 ~~> C2) /\ (Ps |- a2 ~~> Atomic (Trusts a1))
                                   ->
                       (Ps |- a2 ~~> (C1 /\' C2)).
Proof.
intros.
destruct H as [H1 [H2 H3]].
epose proof (and_intro Ps _ _ _ 1 1).
compute in H.
apply H.
epose proof (trust Ps _ _ _ 1 1).
compute in H0.
apply H0.
apply H1.
apply H3.
apply H2.
Qed.