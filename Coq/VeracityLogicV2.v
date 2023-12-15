(*|
=================================================
    Veracity Logic Mechanised in Coq (Draft)
=================================================

.. raw:: html

   <script type="text/javascript" src="http://livejs.com/live.js"></script>

Introduction
------------

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
  \AxiomC{$a^l \in A \quad b^k \in T l$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$c^k \in A$}
  \end{prooftree}

With weights, this is:

.. math::
  \begin{prooftree}
  \AxiomC{$a^l_{w_1} \in A \quad b^k_{w_2} \in T l$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$c^k_{w_1 \times w_2} \in A$}
  \end{prooftree}

:math:`a, b, c` lose meaning in the new approach, as each piece of evidence is directly tied to the claim it is evidence for. So, we omit :math:`a, b, c` and write the following:

.. math::
  \begin{prooftree}
  \AxiomC{$l \rightsquigarrow_{w_1} A \quad k \rightsquigarrow_{w_2} T l$}
  \RightLabel{ $trust\ T$}
  \UnaryInfC{$k \rightsquigarrow_{w_1 \times w_2} A$}
  \end{prooftree}

In Coq, we cannot use subscript notation. So for :math:`k \rightsquigarrow_{w_1 \times w_2} A` we write:

`k ~> A @ (w1 * w2)`.

|*)

(*|
Here we introduce the Coq formalisation of the Veracity Logic, still an early draft.

The key 'features' supported by this formalisation are:
  * Arbitrarily many actors and atomic claims, indexed by :math:`\mathbb{N}`.
  * An inductive type for claims, where claims are:

    - Basic or asserting Trust in an actor (basic claim).
    - Built from pre-existing claims by logical connectives.

      + With tagged :coq:`OrL` and :coq:`OrR` as well as a regular :coq:`Or`.

  * Trust handling, with trust in another actor being a basic claim.
  * Weights for all beliefs.

    - Weights are of the :coq:`Q` rational numbers type.
    - Every statement about a belief has a weight.

      + For now, the weights are any rational number, not restricted to :math:`[0,1]`. This restriction could be added in the future.

  * There is also a list of basic claims which is meant to serve the same purpose as the :coq:`Ps` variable in the Isabelle formalisation.
    
    - Currently, the list holds any claims, but it could potentially be restricted to only include basic claims.


Formalisation
-------------
|*)

(*|
Arbitrarily many actors, indexed by :math:`\mathbb{N}`

.. coq:: all
|*)

Inductive actor :=
  | Actor (a : nat).

(*|
:coq:`Check` provides the type of the term that follows it.
|*)

Check Actor 1.
Check Actor 42.

(*|
Basic claims include:

  * Arbitrarily many atomic claims, indexed by :math:`\mathbb{N}`

  * And claims of the form :coq:`Trusts a` where :coq:`a` is an actor.

.. coq:: all
|*)

Inductive basic_claim :=
  | Atomic_Claim (name : nat)
  | Trusts (a : actor).

Check Atomic_Claim 3.
Check Trusts (Actor 4).

(*|
Claims include:

  * Basic claims

  * Composite claims constructed using the logical connectives, with the tagged :coq:`OrL` and :coq:`OrR` disjunction connectives in addition to conjunction, regular disjunction and implication. Bottom is excluded currently.

.. coq:: all
|*)

Inductive claim :=
  | Basic (c : basic_claim)
  | And (c1 c2 : claim)
  | OrL (c1 c2 : claim)
  | OrR (c1 c2 : claim)
  | Or (c1 c2 : claim)
  | Implies (c1 c2 : claim).

Check (Basic (Atomic_Claim 4)).
Check (Basic (Trusts (Actor 5))).
Definition c1 := (Basic (Atomic_Claim 4)).
Definition c2 := (Basic (Trusts (Actor 5))).
Check (And c1 c2).
Check (OrL c1 c2).
Check (Implies (And c1 c2) (OrR c1 c2)).


(*|
Now, we introduce notation to aid readability.

.. coq:: all
|*)

Infix "/\'" := And (at level 80, right associativity).
Infix "\/L" := OrL (at level 85, right associativity). 
Infix "\/R" := OrR (at level 85, right associativity). 
Infix "\/'" := OrR (at level 85, right associativity). 
Infix "->'" := Implies (at level 99, right associativity). 

Check (c1 /\' c2 ->' c1 \/' c2).

(*|
Next are the proof rules.

:coq:`Believes` is an inductive proposition, so the rules listed are the only way to construct evidence of the form :coq:`Believes ...`.

In the notation :coq:`P |- A ~> B @ W` this means that the list of claims, P, entails that the actor A believes claim B with weight W (once the fraction is simplified fully).

The double :coq:`@@` notation has the same meaning, except it skips the simplification of the fraction (assuming that has already occurred).

.. coq:: all
|*)

Reserved Notation "P |- A ~> B @ W" (at level 80).
Reserved Notation "P |- A ~> B @@ W" (at level 80).
Inductive Believes (Ps : list (actor * claim))
  : actor -> claim -> Q -> Prop :=
  | assumed (a : actor) (C : claim) (H : List.In (a, C) Ps)
     : Ps |- a ~> C @ 1
  (* bot_elim has been removed, along with Bottom. TODO: discuss this *)
  | and_intro (a : actor) (C1 C2 : claim) (w1 w2 : Q)

    (e1 : Ps |- a ~> C1 @ w1) (e2 : Ps |- a ~> C2 @ w2) 
  (*---------------------------------------------------*):
            Ps |- a ~> (C1 /\' C2) @ (Qmin w1 w2)

  | and_elim1 (a : actor) (C1 C2 : claim) (w : Q)

    (e : Ps |- a ~> (C1 /\' C2) @ w)
  (*--------------------------------*):
          Ps |- a ~> C1 @ w

  | and_elim2 (a : actor) (C1 C2 : claim) (w:Q)

    (e : Ps |- a ~> (C1 /\' C2) @ w)
  (*--------------------------------*):
          Ps |- a ~> C2 @ w

  | or_intro1 (a : actor) (C1 C2 : claim) (w : Q)

      (e : Ps |- a ~> C1 @ w)
    (*-----------------------*):
    Ps |- a ~> (C1 \/L C2) @ w

  | or_intro2 (a : actor) (C1 C2 : claim) (w : Q)

      (e : Ps |- a ~> C2 @ w)
    (*-----------------------*):
    Ps |- a ~> (C1 \/R C2) @ w

  | or_elim1 (a : actor) (C1 C2 : claim) (w : Q)

    (e : Ps |- a ~> (C1 \/L C2) @ w)
  (*--------------------------------*):
           Ps |- a ~> C1 @ w

  | or_elim2 (a : actor) (C1 C2 : claim) (w : Q)

    (e : Ps |- a ~> (C1 \/R C2) @ w)
  (*--------------------------------*):
           Ps |- a ~> C2 @ w

(* These detag rules should probably be removed, loss of information. *)
  | or_detag1 (a : actor) (C1 C2 : claim) (w : Q)

    (e : Ps |- a ~> (C1 \/L C2) @ w)
  (*--------------------------------*):
       Ps |- a ~> (C1 \/' C2) @ w

  | or_detag2 (a : actor) (C1 C2 : claim) (w : Q)

    (e : Ps |- a ~> (C1 \/R C2) @ w)
  (*--------------------------------*):
      Ps |- a ~> (C1 \/' C2) @ w

  | trust (a1 a2 : actor) (C : claim) (w1 w2 : Q)

  (e : Ps |- a2 ~> C @ w2) (eT : Ps |- a1 ~> (Basic (Trusts a2)) @ w1)
(*-------------------------------------------------------------------*):
            Ps |- a1 ~> C @ (Qred (w1*w2))
(* impl_intro, when partially applied up to just before e2,
   has a similar meaning to the Isabelle equivalent. *)
  | impl_intro (a : actor) (C1 C2 : claim) (w : Q)
   
     (e1 : Ps |- a ~> C1 @ 1) (e2 : Ps |- a ~> C2 @ w)
   (*-------------------------------------------------*):
            Ps |- a ~> (Implies C1 C2) @ w
  (** TODO, think about the weight for impl_intro here. *)

where "P |- A ~> B @@ W" := (Believes P A B W)
and   "P |- A ~> B @ W" := (P |- A ~> B @@ (Qred W)).

(*| 
Or, presented as Coq parses the above, each with its rule:

.. coq:: unfold
|*)

Check assumed.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$(a, C)$ is contained in $Ps$}
  \RightLabel{ $assumed$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{1} C$}
  \end{prooftree}

.. coq:: unfold
|*)

Check and_intro.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w_1} C1 \quad Ps \vdash a \rightsquigarrow_{w_2} C2$}
  \RightLabel{ $and\_intro$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{min(w_1, w_2)} (C1 \wedge C2)$}
  \end{prooftree}

.. coq:: unfold
|*)

Check and_elim1.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \wedge C2)$}
  \RightLabel{ $and\_elim1$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} C1$}
  \end{prooftree}

.. coq:: unfold
|*)

Check and_elim2.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \wedge C2)$}
  \RightLabel{ $and\_elim2$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} C2$}
  \end{prooftree}

.. coq:: unfold
|*)

Check or_intro1.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} C1$}
  \RightLabel{ $or\_intro1$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_L C2)$}
  \end{prooftree}

.. coq:: unfold
|*)

Check or_intro2.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} C2$}
  \RightLabel{ $or\_intro2$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_R C2)$}
  \end{prooftree}

.. coq:: unfold
|*)

Check or_elim1.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_L C2)$}
  \RightLabel{ $or\_elim1$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} C1$}
  \end{prooftree}

.. coq:: unfold
|*)


Check or_elim2.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_R C2)$}
  \RightLabel{ $or\_elim2$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} C2$}
  \end{prooftree}

.. coq:: unfold
|*)

Check or_detag1.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_L C2)$}
  \RightLabel{ $or\_detag1$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee C2)$}
  \end{prooftree}

.. coq:: unfold
|*)

Check or_detag2.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee_R C2)$}
  \RightLabel{ $or\_detag2$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} (C1 \vee C2)$}
  \end{prooftree}

.. coq:: unfold
|*)

Check trust.

(*|
.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a_2 \rightsquigarrow_{w_2} C \quad Ps \vdash a_1 \rightsquigarrow_{w_1} T a_2$}
  \RightLabel{ $trust$}
  \UnaryInfC{$Ps \vdash a_1 \rightsquigarrow_{w_1 \times w_2} C$}
  \end{prooftree}

.. coq:: unfold
|*)

Check impl_intro.

(*|

I am not certain how to best write this rule.
In any case, the Coq version is equivalent to the following:

.. math::
  \begin{prooftree}
  \AxiomC{$Ps \vdash a \rightsquigarrow_{1} C1 \quad Ps \vdash a \rightsquigarrow_{w} C2$}
  \RightLabel{ $impl\_intro$ }
  \UnaryInfC{$Ps \vdash a \rightsquigarrow_{w} (C1 \rightarrow C2)$}
  \end{prooftree}

|*)

(*|
.. coq:: all
|*)

(*| 
We also introduce one additional notation, for when were are working solely with weights of 1. So that we don't have to write :coq:`@ 1` everywhere. This notation has an additional :coq:`~` (so, a longer squiggly arrow).
|*)
Notation "P |- A ~~> B" := (P |- A ~> B @ 1) (at level 80).

(*|
Example Proofs
--------------

Now we move on to the example proofs, these are early versions partially based on the Isabelle examples, with the main extension being some examples with weights.

|*)

(** * Examples: Incorrect Statements *)

Lemma incorrect_example1 : forall a C, ~ ([] |- a ~~> C).
Proof.
unfold not.
intros.
induction H.
simpl in H.
all: contradiction.
Qed.

(** Here, the antecedent is false (see incorrect_example1).
    So this is provable. *)
Lemma incorrect_example2 : forall a C1 C2,
   ([] |- a ~~> C1 -> [] |- a ~~> (C1 /\' C2)).
Proof.
intros.
apply incorrect_example1 in H.
contradiction.
Qed.

(** * Examples: Correct Statements *)

(** ** Example 1 (old version):
        Trivially true, each antecedent is false. *)
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

(** ** Example 2: Trust *)
Lemma example2 : forall a1 a2 C1 C2 Ps,

  Ps |- a1 ~~> C1 /\ Ps |- a2 ~~> C2 /\ Ps |- a2 ~~> Basic (Trusts a1)
                        ->
            Ps |- a2 ~~> (C1 /\' C2).
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

Ps|-a1~>C1@0.8 /\ Ps|-a2~>C2@0.5 /\ Ps|-a2~>Basic(Trusts a1)@0.25
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

  (Ps |- a1 ~> C @ 0.8) /\ (Ps |- a2 ~> Basic (Trusts a1) @ w)
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

(** ** Example 6:
  Three-claim conjunction with arbitrary weights - simpler *)
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

