Require Import List.
Import ListNotations.

Section VeracityLogic.

Inductive actor :=
  | Actor (a : nat).

Inductive atomic_claim :=
  | Atomic_Claim (name : nat).

Inductive claim :=
  | Atomic (c : atomic_claim)
  | And (c1 c2 : claim)
  | OrL  (c1 c2 : claim)
  | OrR  (c1 c2 : claim)
  | Or (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Context (Trusts : actor -> actor -> Prop).
Infix "`trusts`" := Trusts (at level 25, right associativity).

Infix "/\'" := And (at level 80, right associativity).
Infix "\/L" := OrL (at level 85, right associativity). 
Infix "\/R" := OrR (at level 85, right associativity). 
Infix "\/'" := OrR (at level 85, right associativity). 

Reserved Notation "P |- A ~> B" (at level 80).
Inductive Believes (Ps : list (actor * atomic_claim)) : actor -> claim -> Prop :=
  | assumed_belief (a : actor) (C : atomic_claim) (H : List.In (a, C) Ps) : Ps |- a ~> (Atomic C)
  (* bot_elim is implied by there being no rule for Believing bottom. *)
  | and_intro (a : actor) (C1 C2 : claim)

                  (e1 : Ps |- a ~> C1) (e2 : Ps |- a ~> C2)
                                :
                          Ps |- a ~> (C1 /\' C2)

  | and_elim1 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 /\' C2))
                           :
                        Ps |- a ~> C1

  | and_elim2 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 /\' C2))
                           :
                        Ps |- a ~> C2

  | or_intro1 (a : actor) (C1 C2 : claim)

                      (e : Ps |- a ~> C1)
                           :
                    Ps |- a ~> (C1 \/L C2)

  | or_intro2 (a : actor) (C1 C2 : claim)

                      (e : Ps |- a ~> C2)
                           :
                    Ps |- a ~> (C1 \/R C2)

  | or_elim1 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 \/L C2))
                           :
                         Ps |- a ~> C1

  | or_elim2 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 \/R C2))
                           :
                         Ps |- a ~> C2

  | or_detag1 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 \/L C2))
                           :
                     Ps |- a ~> (C1 \/' C2)

  | or_detag2 (a : actor) (C1 C2 : claim)

                  (e : Ps |- a ~> (C1 \/R C2))
                           :
                    Ps |- a ~> (C1 \/' C2)

  | trust (a1 a2 : actor) (C : claim)

                (e : Ps |- a2 ~> C) (eT : a1 `trusts` a2)
                              :
                        Ps |- a1 ~> C

(* impl_intro, when partially applied up to just before e2, has a similar meaning
   to the Isabelle equivalent. *)
  | impl_intro (a : actor) (C1 C2 : claim)
                       (e1 : Ps |- a ~> C1) (e2 : Ps |- a ~> C2)
                                           :
                               Ps |- a ~> (Implies C1 C2)

where "P |- A ~> B" := (Believes P A B).

(** * Examples: Incorrect Statements *)

Lemma incorrect_example1 : forall a C, ~ ([] |- a ~> C).
Proof.
unfold not.
intros.
induction H.
simpl in H.
all: contradiction.
Qed.

(** Here, the antecedent is false (see incorrect_example1). So this is provable. *)
Lemma incorrect_example2 : forall a C1 C2,
   ([] |- a ~> C1 -> [] |- a ~> (C1 /\' C2)).
Proof.
intros.
apply incorrect_example1 in H.
contradiction.
Qed.

(** * Examples: Correct Statements *)

Lemma example1_old_version : forall a C1 C2 C3,

       [] |- a ~> C1 /\ [] |- a ~> C2 /\ [] |- a ~> C3
                               ->
            [] |- a ~> ((C1 /\' C2) /\' C3)
.
Proof.
intros.
destruct H as [H1 [H2 H3]].
apply incorrect_example1 in H1.
contradiction.
Qed.

Lemma example1 : forall a C1 C2 C3 Ps,

       Ps |- a ~> C1 /\ Ps |- a ~> C2 /\ Ps |- a ~> C3
                               ->
            Ps |- a ~> ((C1 /\' C2) /\' C3)
.
Proof.
intros.
destruct H as [H1 [H2 H3]].
apply and_intro.
apply and_intro.
all: assumption.
Qed.

Lemma example2 : forall a1 a2 C1 C2 Ps,

             (Ps |- a1 ~> C1) /\ (Ps |- a2 ~> C2) /\ (a2 `trusts` a1)
                                   ->
                       (Ps |- a2 ~> (C1 /\' C2)).
Proof.
intros.
destruct H as [H1 [H2 H3]].
apply and_intro; [|assumption].
eapply trust.
apply H1.
apply H3.
Qed.