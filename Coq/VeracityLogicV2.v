(*|
=================================================
    Veracity Logic Mechanised in Coq (Draft)
=================================================

.. raw:: html

   <script type="text/javascript" src="http://livejs.com/live.js"></script>

.. coq:: all
|*)

Require Import List.
Import ListNotations.
Require Import QArith.
Require Import QArith.Qminmax.

Section VeracityLogic.

(*|

One of the differences to the original Veracity Logic in this current formalisation is the handling of trust.

In the original logic we have the rule:

.. math::
  \begin{prooftree}
  \AxiomC{$a^l \in A \quad kTl$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$a^k \in A$}
  \end{prooftree}

Instead, here the equivalent would be:

.. math::
  \begin{prooftree}
  \AxiomC{$a^l \in A \quad b^k \in Tl$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$c^k \in A$}
  \end{prooftree}

With weights, this is:

.. math::
  \begin{prooftree}
  \AxiomC{$a^l_{w_1} \in A \quad b^k_{w_2} \in Tl$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$c^k_{w_1 \times w_2} \in A$}
  \end{prooftree}

:math:`a, b, c` lose meaning in the new approach, as each piece of evidence is directly tied to the claim it is evidence for. So, we omit :math:`a, b, c` and write the following:

.. math::
  \begin{prooftree}
  \AxiomC{$l \rightsquigarrow_{w_1} A \quad k \rightsquigarrow_{w_2} Tl$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$k \rightsquigarrow_{w_1 \times w_2} A$}
  \end{prooftree}

In Coq, we cannot use subscript notation. So for :math:`k \rightsquigarrow_{w_1 * w_2} A` we write:

`k ~> A @ (w1 * w2)`.

|*)

(*|
.. coq:: all
|*)

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
Reserved Notation "P |- A ~> B @@ W" (at level 80).
Inductive Believes (Ps : list (actor * basic_claim)) : actor -> claim -> Q -> Prop :=
  | assumed (a : actor) (C : basic_claim) (H : List.In (a, C) Ps) : Ps |- a ~> (Atomic C) @ 1.0
  (* bot_elim has been removed, along with Bottom. TODO: discuss this *)
  | and_intro (a : actor) (C1 C2 : claim) (w1 w2 : Q)

                  (e1 : Ps |- a ~> C1 @ w1) (e2 : Ps |- a ~> C2 @ w2)
                                :
                          Ps |- a ~> (C1 /\' C2) @ (Qmin w1 w2)

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

                (e : Ps |- a2 ~> C @ w2) (eT : Ps |- a1 ~> (Atomic (Trusts a2)) @ w1)
                              :
                        Ps |- a1 ~> C @ (Qred (w1*w2))

(* impl_intro, when partially applied up to just before e2, has a similar meaning
   to the Isabelle equivalent. *)
  | impl_intro (a : actor) (C1 C2 : claim) (w : Q)
                       (e1 : Ps |- a ~> C1 @ 1) (e2 : Ps |- a ~> C2 @ w)
                                           :
                               Ps |- a ~> (Implies C1 C2) @ w
  (** TODO, think about the weight for impl_intro here. *)

where "P |- A ~> B @@ W" := (Believes P A B W)
and   "P |- A ~> B @ W" := (P |- A ~> B @@ (Qred W)).

Notation "P |- A ~~> B" := (Believes P A B 1) (at level 80).

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

(** ** Example 1 (old version): Trivially true, each antecedent is false. *)
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

(** ** Example 1: Three-claim conjunction *)
Lemma example1 : forall a C1 C2 C3 Ps,

       Ps |- a ~~> C1 /\ Ps |- a ~~> C2 /\ Ps |- a ~~> C3
                               ->
            Ps |- a ~~> ((C1 /\' C2) /\' C3)
.
Proof.
intros.
destruct H as [H1 [H2 H3]].
pose proof (and_intro Ps a C1 C2 1 1).
simpl in H.
pose proof (and_intro Ps a (C1 /\' C2) C3 1 1).
simpl in H0.
apply H0.
apply H.
all: assumption.
Qed.

(* ** Example 2: Trust *)
Lemma example2 : forall a1 a2 C1 C2 Ps,

             (Ps |- a1 ~~> C1) /\ (Ps |- a2 ~~> C2) /\ (Ps |- a2 ~~> Atomic (Trusts a1))
                                   ->
                       (Ps |- a2 ~~> (C1 /\' C2)).
Proof.
intros.
destruct H as [H1 [H2 H3]].
epose proof (and_intro Ps _ _ _ 1 1).
simpl in H.
apply H.
epose proof (trust Ps _ _ _ 1 1).
simpl in H0.
apply H0.
apply H1.
apply H3.
apply H2.
Qed.

(** ** Example 3: Using weights. *)
Lemma example3 : forall a1 a2 C1 C2 Ps,

             (Ps |- a1 ~> C1 @ 0.8) /\ (Ps |- a2 ~> C2 @ 0.5) /\ (Ps |- a2 ~> Atomic (Trusts a1) @ 0.25)
                                   ->
                       (Ps |- a2 ~> (C1 /\' C2) @ 0.2).
Proof.
intros.
destruct H as [H1 [H2 H3]].
epose proof (and_intro Ps a2 C1 C2 0.2 0.5).
simpl in H.
apply H.
simpl in *.
epose proof (trust Ps a2 a1 C1 0.25 0.8).
simpl in H0.
apply H0.
assumption.
assumption.
assumption.
Qed.

Lemma QredQred : forall q, Qred (Qred q) = (Qred q).
Proof.
intros.
apply Qred_complete.
apply Qred_correct.
Qed.

(** ** Example 4: With a variable that is a weight. *)
Lemma example4 : forall a1 a2 C w Ps,

             (Ps |- a1 ~> C @ 0.8) /\ (Ps |- a2 ~> Atomic (Trusts a1) @ w)
                                   ->
                       (Ps |- a2 ~> C @ (w * 0.8)).
Proof.
intros.
destruct H as [H1].
epose proof (trust Ps a2 a1 C (w) 0.8).
rewrite QredQred in H0.
apply H0.
assumption.
assumption.
Qed.

(** ** Example 5: Three-claim conjunction with arbitrary weights *)
Lemma example5 : forall a C1 C2 C3 w1 w2 w3 Ps,

       Ps |- a ~> C1 @ w1 /\ Ps |- a ~> C2 @ w2  /\ Ps |- a ~> C3 @w3
                               ->
            Ps |- a ~> ((C1 /\' C2) /\' C3) @ (Qmin w1 (Qmin w2 w3)).
Proof.
intros.
destruct H as [H1 [H2 H3]].
assert(Qred (Qmin w1 (Qmin w2 w3)) = Qred( Qmin (Qmin w1 w2) w3)).
apply Qred_complete.
apply Q.min_assoc.
rewrite H.
apply and_intro.
apply and_intro.
all: assumption.
Qed.

(** ** Example 6: Three-claim conjunction with arbitrary weights - simpler *)
Lemma example6 : forall a C1 C2 C3 w1 w2 w3 Ps,

       Ps |- a ~> C1 @ w1 /\ Ps |- a ~> C2 @ w2  /\ Ps |- a ~> C3 @w3
                               ->
            Ps |- a ~> ((C1 /\' C2) /\' C3) @ (Qmin (Qmin w1 w2) w3).
Proof.
intros.
destruct H as [H1 [H2 H3]].
apply and_intro.
apply and_intro.
all: assumption.
Qed.

