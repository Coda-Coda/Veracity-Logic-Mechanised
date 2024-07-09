(*|
Veracity Logic Mechanised in Coq
================================

This Coq formalisation is an attempt to mechanise a logic for veracity, with the goal of precisely pinning down the meaning of veracity.
Veracity is concerned with trust, truth, demonstrability and authenticity.
We take an approach inspired by intuitionistic logic, in part due to a desire not to "lose information" as proofs progress.
For further details, please see the arXiv paper "A logic for Veracity" by Steve Reeves available at https://arxiv.org/abs/2302.06164.

This work was completed as a part of the `Veracity Lab <https://veracity.wgtn.ac.nz/>`_ which was one of the `Spearhead projects <https://www.sftichallenge.govt.nz/our-research/projects/spearhead/veracity-technology/>`_ of the `Science for Technological Innovation National Science Challenge (SfTI) <https://www.sftichallenge.govt.nz/>`_ in New Zealand.

.. contents::

..
  The following is required to get MathJax to process the outputs marked with the class coq-math.

.. raw:: html

   <link rel="stylesheet" href="overrides.css">
   
   <script type="text/javascript">
     document.addEventListener("DOMContentLoaded", () => {
        // 1. Find all relevant Alectryon tags
        var spans = document.querySelectorAll(".coq-math > * > * > * > * > * > .s2, .custom-math");

        // 2. Wrap the contents of each in \(\) math delimiters, add mathjax class
        spans.forEach(function (e) {
            e.innerText = '\\[' + e.innerText + '\\]';
            e.classList.add("mathjax_process");
        });

        // 3. If MathJax has already loaded, force reprocessing
        window.MathJax && MathJax.typesetPromise(spans);
     });
   </script>

   <style type="text/css"> /* Override MathJax margins */
       .coq-math .goal-conclusion > *,
       .coq-math .hyp-body span > *,
       .coq-math .hyp-type span > * {
           margin: 0 !important;
       }
   </style>


.. coq:: all
|*)

(*|

Imports
-------

`List`, `ListNotations`, `String`, `Strings.Ascii` and `Bool` are required for various aspects of this formalisation as one might expect.
In particular, `String` and `Strings.Ascii` are required because a key feature of this formalisation is the ability to output strings as LaTeX, natural language, or formatted for `LogSeq <https://logseq.com>`_.

`QArith` and `QArith.Qminmax` are imported because rational numbers are used to represent weights (e.g. how much does one actor trust another).
We chose rational numbers rather than real numbers because rational numbers are much easier to work with and the additional expressivity of real numbers is not necessary here.

|*)

Require Import List.
Import ListNotations.
Require Import String.
Require Import Strings.Ascii.
Require Import Bool.
Require Import Program.
Require Import QArith.
Require Import QArith.Qminmax.

(*|

Converting rational numbers to strings
--------------------------------------

Coq does not natively include a function to convert rational numbers to strings (or even natural numbers).
Here we define a function that prints rational numbers as strings formatted for LaTeX.
E.g. as `\frac{3}{8}` i.e. :math:`\frac{3}{8}`.

The following `writeNat` function and those it depends on are used under the MIT License, they are by @arthuraa on GitHub.
See: https://github.com/arthuraa/poleiro/blob/master/theories/ReadNat.v

|*)


Open Scope char_scope.
Open Scope nat_scope.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Eval compute in writeNat 42.

Close Scope nat_scope.

Eval compute in Qnum 0.5.
Eval compute in Qden 0.5.
Eval compute in Qnum (Qred 0.5).
Eval compute in Qden (Qred 0.5).

Open Scope nat_scope.
Definition writeQ (x : Q) : string :=
  let simplified := Qred x in
  let numerator := Z.to_nat (Qnum simplified) in
  let denominator := Pos.to_nat (Qden simplified) in
  if (denominator =? 1) then writeNat numerator else
  "\frac{" 
    ++  (writeNat numerator) 
    ++ "}{" 
    ++ (writeNat denominator) ++ "}".
Close Scope nat_scope.
Eval compute in writeQ 0.35.

(*|
.. coq:: all
|*)

(*|

Start of the formalisation of the veracity logic
------------------------------------------------

With the preliminaries covered, we now begin to introduce the definitions directly related to the veracity logic.

|*)

Section VeracityLogic.

(*|

Types for names
---------------

First, we introduce inductive types for the names of atomic evidence, actors and trust relations.

We use `Scheme Equality for ...` to automatically generate functions such as `atomic_evid_name_beq` which are boolean equality functions for each of the inductive types for names.

For more information on `Scheme Equality`, please see: https://coq.inria.fr/doc/V8.17.1/refman/proofs/writing-proofs/reasoning-inductives.html#coq:cmd.Scheme-Equality.

|*)

Inductive atomic_evid_name :=
  | _e_
  | _e1_
  | _e2_
  | _e3_
  | _e4_
  | _eQ_
  | _eB_
  | _l_
  | _s_
  | _c_
  | _x_
  | _y_
  | _z_
  | _belief_
  | _testing_
  | _audit_
  | _compile_
  | _review_
  | _assess_
  | _business_procedure_
  | _ingredients_percentage_list_
  | _breakdown_of_formulations_list_
.

Scheme Equality for atomic_evid_name.
Check atomic_evid_name_beq. (* .unfold *)

(*|

The `Check` command, above, prints the type of the term following it.

|*)

Inductive actor_name :=
  | _a1_
  | _a2_
  | _a3_
  | _a4_
  | _aQ_
  | _retailer_
  | _vineyard_
  | _winery_
  | _P_
  | _Q_
  | _R_
  | _S_
  | _T_
  | _U_
  | _L_
  | _applicant_
  | _certifier_
.

Scheme Equality for actor_name.
Check actor_name_beq. (* .unfold *)

Inductive claim_name :=
  | _c1_
  | _c2_
  | _c3_
  | _c4_
  | _c5_
  | _cQ_
  | _healthy_
  | _nonToxic_
  | _organic_
  | _ingredients_valid_
  | _ingredients_valid_approved_
  | _recipe_valid_
  | _percentage_ingredients_valid_
  | _breakdown_of_formulations_valid_
  | _successful_market_compliance_assessment_
. 

Scheme Equality for claim_name.
Check claim_name_beq. (* .unfold *)

Inductive trust_relation_name :=
  | _A_Trust_
  | _B_Trust_
  | _T_Trust_
  | _U_Trust_
  | _V_Trust_
.

Scheme Equality for trust_relation_name.
Check trust_relation_name_beq. (* .unfold *)

(*|

Types of aspects of the veracity logic
--------------------------------------

|*)

(*|

Claims
~~~~~~

First, we have the inductive type for claims.
A claim can either be:

  - A named atomic claim
  - `Bottom`, the claim which can never have veracity
  - A conjuction of two other claims
  - A disjucntion of two other claims

We again use `Scheme Equality` to define boolean equality for claims.

|*)

Inductive claim :=
  | AtomicClaim (n : claim_name)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Scheme Equality for claim.

(*|

Evidence
~~~~~~~~

Secondly, we have the inductive type for evidence.
Evidence can either be:

  - Named atomic evidence
  - A pair of other evidence (used for claims which are a conjunction)
  - Evidence tagged with `Left` (used for claims which are a disjunction where the left disjunct is true)
  - Evidence tagged with `Right` (used for claims which are a disjunction where the right disjunct is true)
  - Evidence that involves an abstraction, described further below (used for implicative claims)

An experimental alternative implementation of `evid` which uses dependent types to make the links described in the parentheses explicit can be found on the branch `WIP-dependent-evid` here: https://github.com/Coda-Coda/Veracity-Logic-Mechanised/blob/WIP-dependent-evid/Coq/VeracityLogic.v#L331.
The experimental `WIP-dependent-evid` branch was only completed up to the definition of `proofTreeOf` and does not include working versions of the example proofs.

We again use `Scheme Equality` to define boolean equality for evidence.

**Abstractions** turn out to be challenging to formalise, especially when including weights.
The solution taken in this formalisation at the moment is to require evidence of the same weight to be used when a lambda is applied as back when the lambda was constructed.
This requires the formalisation to keep track of the weights used when lambdas are constructed, and so `Lambda` has the argument `required_weight`.

|*)

Inductive evid :=
  | AtomicEvid (n : atomic_evid_name)
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (x : atomic_evid_name) (required_weight : Q) (bx : evid).

Scheme Equality for evid.

(*|

Actors
~~~~~~

Next, we have the inductive type for actors.

An `actor` can only be:

  - A tagged `actor_name`

We again use `Scheme Equality` to define boolean equality for actors.

|*)

Inductive actor :=
  | Actor (n : actor_name).

Scheme Equality for actor.

(*|

Trust Relations
~~~~~~~~~~~~~~~

Next, we have the inductive type for trust relations.

Similarly to actors, a `trust_relation` can only be:

  - A tagged `trust_relation_name`

We again use `Scheme Equality` to define boolean equality for trust relations.

|*)

Inductive trustRelation :=
  | Trust (n : trust_relation_name).

Scheme Equality for trustRelation.

(*|

Judgements
~~~~~~~~~~

Finally, we have the inductive type for judgements.

A `judgement` has one constructor which requries:

  - Evidence, an Actor, a Weight, and a Claim.

This is taken to mean that based on the provided evidence, the given actor holds that the given claim has veracity, at the strength of the given weight.

We again use `Scheme Equality` to define boolean equality for judgements.

|*)

Inductive judgement :=
  Judgement (e : evid) (a : actor) (w : Q) (c: claim).

Scheme Equality for judgement.

(*|

Helpful extras
--------------

|*)

(*|

Notation
~~~~~~~~

Here we define convenient notation for `Judgement`, `And`, `Or`, `Implies`, `Bottom`, and `Pair`.

For more information on Coq's notation system please see https://coq.inria.fr/doc/V8.17.1/refman/user-extensions/syntax-extensions.html?highlight=notation#coq:cmd.Notation.

|*)

Notation "E \by A @ W \in C" := (Judgement E A W C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Infix "->'" := Implies (at level 99, right associativity).
Notation "_|_" := (Bottom) (at level 1).
Notation "{{ x , y , .. , z }}" := (Pair .. (Pair x y) .. z).

(*|

Shorter names for atomic evidence, actors, claims, etc.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we define convenient names such as `e` for `AtomicEvid _e_`.
These will be used later on in examples and lemmas.

|*)

Definition e := AtomicEvid _e_.

Definition e1 := AtomicEvid _e1_.
Definition a1 := Actor _a1_.
Definition c1 := AtomicClaim _c1_.

Definition e2 := AtomicEvid _e2_.
Definition a2 := Actor  _a2_.
Definition c2 := AtomicClaim _c2_.

Definition e3 := AtomicEvid _e3_.
Definition a3 := Actor _a3_.
Definition c3 := AtomicClaim _c3_.

Definition e4 := AtomicEvid  _e4_.
Definition a4 := Actor _a4_ .
Definition c4 := AtomicClaim _c4_.

Definition eB := AtomicEvid  _eB_.

Definition x := AtomicEvid _x_ .
Definition y := AtomicEvid _y_.
Definition z := AtomicEvid _z_.
Definition Penelope := Actor _P_.
Definition Quentin := Actor _Q_.
Definition Ryan := Actor _R_.
Definition Samantha := Actor _S_.
Definition Tom := Actor _T_.
Definition Ulysses := Actor _U_.
Definition Ledger := Actor _L_.
Definition C1 := AtomicClaim _c1_.
Definition C2 := AtomicClaim _c2_.
Definition C3 := AtomicClaim _c3_.
Definition C4 := AtomicClaim _c4_.
Definition C5 := AtomicClaim _c5_.


Definition trustT := Trust _T_Trust_.
Definition trustU := Trust _U_Trust_.
Definition trustV := Trust _V_Trust_.
Definition trustA := Trust _A_Trust_.
Definition trustB := Trust _B_Trust_.

Definition j1 := x \by Penelope @ 1 \in c1.
Definition j2 := y \by Penelope @ 1 \in c2.
Definition j3 := z \by Penelope @ 1 \in c3.

(*|

Boolean equality typeclass
~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we define a typeclass for boolean equality with the notation `=?` to make things more convenient when using the boolean equality functions.

For more information on Coq's typeclasses please see https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html.

|*)

Class Beq A : Type :=
  {
    beq : A -> A -> bool
  }.
Infix "=?" := beq : beq_scope.
Instance : Beq atomic_evid_name := { beq := atomic_evid_name_beq }.
Instance : Beq actor_name := { beq := actor_name_beq }.
Instance : Beq claim_name := { beq := claim_name_beq }.
Instance : Beq trust_relation_name := { beq := trust_relation_name_beq }.
Instance : Beq evid := { beq := evid_beq }.
Instance : Beq claim := { beq := claim_beq }.
Instance : Beq actor := { beq := actor_beq }.
Instance : Beq trustRelation := { beq := trustRelation_beq }.
Instance : Beq judgement := { beq := judgement_beq }.

Close Scope string.

(*|

The machinery for applying abstractions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Abstractions are described in the `arXiv paper <https://arxiv.org/abs/2302.06164>`_ as follows.

.. pull-quote::

  "For expression :math:`e` and variable :math:`x`, the expression :math:`(x)e` is an expression where all free occurrences of :math:`x` in :math:`e` become bound by this :math:`(x)`. The expression :math:`(x)e` called an abstraction (of :math:`e` by :math:`x`). For expression :math:`(x)e` and expression :math:`a`, :math:`(x)e(a)` is an expression where all occurrences of :math:`x` in :math:`e` bound by this :math:`(x)` are replaced by :math:`a`. The expression :math:`(x)e(a)`  is called the application of :math:`(x)e` to :math:`a`."

The following functions implement the core features of abstractions.

|*)

Open Scope beq_scope.

(*|

First we define a helper function to help prevent a situation where the same atomic evidence is used for an abstraction multiple times. 

We write the abstraction :math:`(x)(x)` as :math:`\lambda(x)(x)`.

We want to prevent abstractions such as :math:`\lambda(x)(\lambda(x)(x))`. We should not use :math:`x` as the variable for both abstractions. Instead, :math:`\lambda(x)(\lambda(y)(x))` or :math:`\lambda(x)(\lambda(y)(y))` would be permitted and are not ambiguous.

We represent an abstraction by `x` and `bx`, where `bx` is the evidence (potentially using `Pair`, `Left`, `Right` and `Lambda`) for which every occurrence of the `AtomicEvid` `x` within `bx` should be replaced by the supplied evidence `a` when `apply_abstraction` is called. For `apply_abstraction`, we require that the atomic evidence `x` is not used in an "inner abstraction" such as described in the previous paragraph. Coq's `Program` machinery is used to show that `notUsedInInnerAbstraction` returns `true` for recursive calls to `apply_abstraction`, supported by the proofs following each `Next Obligation`.

|*)

Fixpoint notUsedInInnerAbstraction (x : atomic_evid_name) (bx : evid) : bool :=
match bx with
  | AtomicEvid _ => true
  | Pair e1 e2 => notUsedInInnerAbstraction x e1 && notUsedInInnerAbstraction x e2
  | Left e => notUsedInInnerAbstraction x e
  | Right e => notUsedInInnerAbstraction x e
  | Lambda x' _ bx' => (negb (x =? x')) && notUsedInInnerAbstraction x bx'
end.

Program Fixpoint apply_abstraction (x : atomic_evid_name) (bx : evid) (a : evid) (H2 : notUsedInInnerAbstraction x bx = true) : evid := 
  match bx with
  | AtomicEvid name => if name =? x then a else AtomicEvid name
  | Pair e1 e2 => Pair (apply_abstraction x e1 a _) (apply_abstraction x e2 a _)
  | Left e => Left (apply_abstraction x e a _)
  | Right e => Right (apply_abstraction x e a _)
  | Lambda x' w bx' => Lambda x' w (apply_abstraction x bx' a _)
end.
Next Obligation.
simpl in H2. apply andb_prop in H2. destruct H2. auto.
Defined.
Next Obligation.
simpl in H2. apply andb_prop in H2. destruct H2. auto.
Defined.
Next Obligation.
simpl in H2. apply andb_prop in H2. destruct H2. auto.
Defined.

(*|

In the following example, Coq's `Program` machinery automatically fills in the proof that :math:`x` is not used in an inner abstraction, thanks to the tactic `program_simpl`. For more information on Coq's Program machinery please see: https://coq.inria.fr/doc/V8.17.1/refman/addendum/program.html. For the `program_simpl` tactic please see: https://github.com/coq/coq/blob/881027fa1c868bc12f7d2e4f9dd407c3847a95a7/theories/Program/Tactics.v#L319.

Here we show that :math:`\lambda(x)(Left(x))(l) = Left(l)`.

|*)

Program Example apply_example1 :
  apply_abstraction _x_
    (Left (AtomicEvid _x_))
    (AtomicEvid _l_) _ 
  = Left (AtomicEvid _l_).
reflexivity.
Qed.

(*|

Here we show that :math:`\lambda(y)((y,s))(Right(l)) = (Right(l),s)`.

|*)

Program Example apply_example2 : 
  apply_abstraction _y_
    (Pair (AtomicEvid _y_) (AtomicEvid _s_))
    (Right (AtomicEvid _l_)) _
  = Pair (Right (AtomicEvid _l_)) (AtomicEvid _s_).
reflexivity.
Qed.

(*|

The machinery for equality treating lists as sets
-------------------------------------------------

We would like to treat assumptions as sets, because the order of assumptions is irrelevant and we would like to not be concerned with duplicate assumptions. The only operation we need to apply to assumptions is equality, which is used in the logical rules in the `proofTreeOf` definition later. So, here we take the straightforward approach of defining `eq_sets` which is an equality function treating lists as sets, defined as both lists being a `subset` of each other.

The notation `{Beq A}` preceded by a backquote indicates that the type `A` is of the typeclass `Beq` described earlier, see `Boolean equality typeclass`_. So, `eq_sets` defines equality for lists treated as sets containing elements of a type which has a boolean equality function declared for it. The typeclass instance for `Beq` is what defines `=?` in the definitions below, as this was the notation we defined for `beq`. In this file we only use `eq_sets` for lists of evidence, but for the sake of generality we use the `Beq` typeclass.

|*)

Fixpoint contains {A} `{Beq A} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: tl => (x =? h) || contains x tl
  end.

Fixpoint subset {A} `{Beq A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => true
  | h :: tl => contains h l2 && subset tl l2
end.

Definition eq_sets {A} `{Beq A} (l1 l2 : list A) : bool := subset l1 l2 && subset l2 l1.

(*|

We also define the notation `==?` for `eq_sets`.

|*)

Infix "==?" := eq_sets (at level 70) : beq_scope.

(*|

The central inductive definition of valid proof trees
-----------------------------------------------------

Now we move to the most important definition of this file.
The inductive type `proofTreeOf` defines what a correct proof tree can be.
At it's core, it is a datatype for a tree.
However, it is *dependently typed*, the type depends on the values `list judgement` (the list/set of assumptions) and `judgement` (the judgement that this proof tree). That is, `proofTreeOf Ps j` is the type of all correct proof trees of the judgement `j` with the assumptions `Ps`.

In the rules we use the convention of naming variables as follows:

  - `Ps`, `Qs`, `Rs` refer to the lists/sets of assumptions (we represent assumptions as judgements).
  - `e`, `e1`, `e2` refer to evidence or, in some cases, atomic evidence names when we require the evidence to be atomic.
  - `a`, `a1`, `a2` refer to actors.
  - `w`, `w1`, `w2` refer to weights, of type `Q`.
  - `c`, `c1`, `c2` refer to claims.
  - `H`, `H1`, `H2` refer to "hypotheses" or, in these rules, conditions that must be met for the rule/constructor to be able to be applied. They are sometimes followed by a description, e.g. `HWeights` refers to a condition to do with weights.

In these rules, we rely on Coq's type inference, so we don't explicity give the types of `e a w` and `c` in the `assume` rule, for example. But we could instead have written:

`| assume (e : atomic_evid_name) (a : actor) (w : Q) (c : claim) ...`

A helpful exercise may be to add explicit types like this whenever the types are not 100% clear and check if Coq still accepts the definition.

It is important to realise that `proofTreeOf` is a dependent `Type` (rather than a `Prop`), so we can pattern match on values of type `proofTreeOf Ps j` and use this to define functions on proof trees, such as converting them to Latex strings. The alternative would have been to make `proofTreeOf` an inductive proposition. For more information on inductive propositions see: https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html. `VeracityLogicV1.v <../Previous/VeracityLogicV1.v>`_ and `VeracityLogicV2.v <../Previous/VeracityLogicV2.v>`_ took the inductive proposition approach.

For each rule, everything before the final colon is required in order to construct the proof tree that follows the final colon. 

For example, in `and_intro`, for any:

  - evidence `e1, e2`
  - actor `a`
  - weights `w1, w2, w3`
  - claims `C1, C2`
  - assumptions `Ps, Qs, Rs`

As well as:

  - a proof that the assumptions in `Rs` equals (`Ps` appended to `Qs`) (considered as sets)
  - a proof that `w3` is the minimum of `w1` and `w2`

Along with:

  - a proof tree from the assumptions `Ps` of the judgement that the actor `a` holds that `C1` has veracity with weight `w1` by the evidence `e1`
  - and a proof tree from the assumptions `Qs` of the judgement that the actor `a` holds that `C2` has veracity with weight `w2` by the evidence `e2`

We then have constructed:

- a proof tree from the assumptions `Rs` of the judgement that the actor `a` holds that :math:`C_1 \wedge C_2` has veracity with weight `w3` by the evidence :math:`(e_1,e_2)`.

Further details of each rule are discussed later in: `Example applications of each rule`_.

|*)

Inductive proofTreeOf : list judgement -> judgement -> Type :=
| assume (e : atomic_evid_name) (a : actor) (w : Q) (c : claim) : proofTreeOf [((AtomicEvid e) \by a @ w \in c)] ((AtomicEvid e) \by a @ w \in c)

| bot_elim e a w C Ps

        (M : proofTreeOf Ps (e \by a @ w \in _|_))
                           :
             proofTreeOf Ps (e \by a @ w \in C)

| and_intro e1 e2 a w1 w2 w3 C1 C2 Ps Qs Rs
         (H : Ps ++ Qs ==? Rs = true)
         (HWeights : w3 = Qmin w1 w2)

(L: proofTreeOf Ps (e1 \by a @ w1 \in C1))
                           (R: proofTreeOf Qs (e2 \by a @ w2 \in C2))
                        :
    proofTreeOf Rs ({{e1, e2}} \by a @ w3 \in (C1 /\' C2))

| and_elim1 e1 e2 a w C1 C2 Ps

    (M : proofTreeOf Ps ({{e1, e2}} \by a @ w \in (C1 /\' C2)))
                           :
             proofTreeOf Ps (e1 \by a @ w \in C1)

| and_elim2 e1 e2 a w C1 C2 Ps

    (M : proofTreeOf Ps ({{e1, e2}} \by a @ w \in (C1 /\' C2)))
                          :
        proofTreeOf Ps (e2 \by a @ w \in C2)

| or_intro1 e1 a w C1 C2 Ps

           (M: proofTreeOf Ps (e1 \by a @ w \in C1))
                          :
    proofTreeOf Ps ((Left e1) \by a @ w \in (C1 \/' C2))

| or_intro2 e2 a w C1 C2 Ps

           (M: proofTreeOf Ps (e2 \by a @ w \in C2))
                          :
    proofTreeOf Ps ((Right e2) \by a @ w \in (C1 \/' C2))

| or_elim1 e1 a w C1 C2 Ps

    (M: proofTreeOf Ps ((Left e1) \by a @ w \in (C1 \/' C2)))
                        :
      proofTreeOf Ps (e1 \by a @ w \in C1)

| or_elim2 e2 a w C1 C2 Ps

    (M : proofTreeOf Ps ((Right e2) \by a @ w \in (C1 \/' C2)))
                          :
        proofTreeOf Ps (e2 \by a @ w \in C2)

| trust e a1 a2 wTrust w1 w2 C (name : trustRelation) Ps
                    (HWeights : w2 = w1 * wTrust)

(L: proofTreeOf Ps (e \by a2 @ w1 \in C))
                          :
            proofTreeOf Ps (e \by a1 @ w2 \in C)

| impl_intro (x : atomic_evid_name) (bx : evid) a w1 w2 (C1 : claim) C2 Ps Qs
                    (H1 : notUsedInInnerAbstraction x bx = true)
                 (H2 : contains ((AtomicEvid x) \by a @ w1 \in C1) Ps = true)
                 (H3 : remove judgement_eq_dec ((AtomicEvid x) \by a @ w1 \in C1) Ps ==? Qs = true)

              (M: proofTreeOf Ps (bx \by a @ w2 \in C2))
                              :
   proofTreeOf Qs ((Lambda x w1 bx) \by a @ w2 \in (Implies C1 C2))
| impl_elim x bx y a w1 w2 C1 C2 Ps Qs Rs
                    (H1 : Ps ++ Qs ==? Rs = true)
               (H2 : notUsedInInnerAbstraction x bx = true)                
                
(L: proofTreeOf Ps ((Lambda x w1 bx) \by a @ w2 \in (Implies C1 C2)))
                           (R: proofTreeOf Qs (y \by a @ w1 \in C1))
                        :
    proofTreeOf Rs ((apply_abstraction x bx y H2) \by a @ w2 \in C2)
.

Record proofTreeOf_wrapped (a : actor) (c : claim) := {
  _Ps : list judgement;
  _e : evid;
  _w : Q;
  _p : proofTreeOf _Ps (_e \by a @ _w \in c)
}.

(*|

String representations
----------------------

|*)
Open Scope string.

Class ShowForProofTree A : Type :=
  {
    showForProofTree : A -> string
  }.
Class ShowForNaturalLanguage A : Type :=
  {
    showForNaturalLanguage : A -> string
  }.
Class ShowForLogSeq A : Type :=
  {
    showForLogSeq : A -> string
  }.

Instance : ShowForProofTree Q := { showForProofTree := writeQ }.
Instance : ShowForNaturalLanguage Q := { showForNaturalLanguage := writeQ }.
Instance : ShowForLogSeq Q := { showForLogSeq := writeQ }.

Instance : ShowForProofTree atomic_evid_name := { 
  showForProofTree n := 
    match n with
      | _e_ => "e"
      | _e1_ => "e1"
      | _e2_ => "e2"
      | _e3_ => "e3"
      | _e4_ => "e4"
      | _eQ_ => "e?"
      | _eB_ => "eB"
      | _l_ => "l"
      | _s_ => "s"
      | _c_ => "c"
      | _x_ => "x"
      | _y_ => "y"
      | _z_ => "z"
      | _belief_ => "b"
      | _testing_ => "t"
      | _audit_ => "a"
      | _compile_=> "c"
      | _review_=> "r"
      | _assess_ => "a"
      | _business_procedure_ => "p"
      | _ingredients_percentage_list_ => "ePI"
      | _breakdown_of_formulations_list_=> "eBF"
    end
  }.

Instance : ShowForProofTree actor_name := { 
  showForProofTree n := 
    match n with
      | _a1_ => "a_{1}"
      | _a2_ => "a_{2}"
      | _a3_ => "a_{3}"
      | _a4_ => "a_{4}"
      | _aQ_ => "a_{?}"
      | _retailer_ => "r"
      | _vineyard_ => "v"
      | _winery_ => "w"
      | _P_ => "P"
      | _Q_ => "Q"
      | _R_ => "R"
      | _S_ => "S"
      | _T_ => "T"
      | _U_ => "U"
      | _L_ => "L"
      | _applicant_ => "A"
      | _certifier_ => "C"
    end
  }.

Instance : ShowForProofTree claim_name := { 
  showForProofTree n := 
    match n with
      | _c1_ => "C_{1}"
      | _c2_ => "C_{2}"
      | _c3_ => "C_{3}"
      | _c4_ => "C_{4}"
      | _c5_ => "C_{5}"
      | _cQ_ => "C_{?}"
      | _healthy_ => "H"
      | _nonToxic_ => "N"
      | _organic_ => "O"
      | _ingredients_valid_ => "\mathit{IV}"
      | _ingredients_valid_approved_ => "\mathit{IVA}"
      | _recipe_valid_ => "\mathit{RV}"      
      | _percentage_ingredients_valid_ => "\mathit{PIV}"
      | _breakdown_of_formulations_valid_ => "\mathit{BFV}"
      | _successful_market_compliance_assessment_ => "\mathit{SMCA}"
    end
  }.

Instance : ShowForProofTree trust_relation_name := { 
  showForProofTree n := 
    match n with
      | _A_Trust_ => "A"
      | _B_Trust_ => "B"
      | _T_Trust_ => "T"
      | _U_Trust_ => "U"
      | _V_Trust_ => "V"
    end
  }.

Instance : ShowForNaturalLanguage atomic_evid_name := { 
  showForNaturalLanguage n := 
    match n with
      | _e_ => "atomic evidence e"
      | _e1_ => "atomic evidence 1"
      | _e2_ => "atomic evidence 2"
      | _e3_ => "atomic evidence 3"
      | _e4_ => "atomic evidence 4"
      | _eQ_ =>  "unknown evidence"
      | _eB_ =>  "evidence for bottom"
      | _l_ => "atomic evidence l"
      | _s_ => "atomic evidence s"
      | _c_ => "atomic evidence c"
      | _x_ => "atomic evidence x"
      | _y_ => "atomic evidence y"
      | _z_ => "atomic evidence z"
      | _belief_ => "belief"
      | _testing_ => "testing"
      | _audit_ => "audit"
      | _compile_=> "compile"
      | _review_=> "review"
      | _assess_ => "assess"
      | _business_procedure_ => "business procedure"
      | _ingredients_percentage_list_ => "ingredients percentage list"
      | _breakdown_of_formulations_list_ => "breakdown of formulations list"
    end
  }.
Instance : ShowForLogSeq atomic_evid_name := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForNaturalLanguage actor_name := { 
  showForNaturalLanguage n := 
    match n with
      | _a1_ => "actor 1"
      | _a2_ => "actor 2"
      | _a3_ => "actor 3"
      | _a4_ => "actor 4"
      | _aQ_ => "unknown actor"
      | _retailer_ => "retailer"
      | _vineyard_ => "vineyard"
      | _winery_ => "winery"
      | _P_ => "Penelope"
      | _Q_ => "Quentin"
      | _R_ => "Ryan"
      | _S_ => "Samantha"
      | _T_ => "Tom"
      | _U_ => "Ulysses"
      | _L_ => "Ledger"
      | _applicant_ => "applicant"
      | _certifier_ => "certifier"
    end
  }.
Instance : ShowForLogSeq actor_name := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForNaturalLanguage claim_name := { 
  showForNaturalLanguage n := 
    match n with
      | _c1_ => "claim 1"
      | _c2_ => "claim 2"
      | _c3_ => "claim 3"
      | _c4_ => "claim 4"
      | _c5_ => "claim 5"
      | _cQ_ => "unknown claim"
      | _healthy_ => "healthy"
      | _nonToxic_ => "non-toxic"
      | _organic_ => "organic"
      | _ingredients_valid_ => "ingredients-valid"
      | _ingredients_valid_approved_ => "ingredients-valid-approved"
      | _recipe_valid_ => "recipe-valid"      
      | _percentage_ingredients_valid_ => "percentage-ingredients-valid"
      | _breakdown_of_formulations_valid_ => "breakdown-of-formulations-valid"
      | _successful_market_compliance_assessment_ => "successful-market-compliance-assessment"
    end
  }.
Instance : ShowForLogSeq claim_name := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForNaturalLanguage trust_relation_name := { 
  showForNaturalLanguage n := 
    match n with
      | _A_Trust_ => "trust relation A"
      | _B_Trust_ => "trust relation B"
      | _T_Trust_ => "trust relation T"
      | _U_Trust_ => "trust relation U"
      | _V_Trust_ => "trust relation V"
    end
  }.
Instance : ShowForLogSeq trust_relation_name := {showForLogSeq := showForNaturalLanguage}.

Fixpoint showForProofTreeEvid e :=
  match e with
  | AtomicEvid name => showForProofTree name
  | Pair e1 e2 => "(" ++ (showForProofTreeEvid e1) ++ ", "
                      ++ (showForProofTreeEvid e2) ++ ")"
  | Left e => "i(" ++ showForProofTreeEvid e ++ ")"
  | Right e => "j(" ++ showForProofTreeEvid e ++ ")"
  | Lambda e1 w e2 => "\lambda(" ++ showForProofTree e1 ++ "_{" ++ showForProofTree w ++ "})(" ++ showForProofTreeEvid e2 ++ ")"
end.

Instance : ShowForProofTree evid := { showForProofTree := showForProofTreeEvid }.
Instance : ShowForNaturalLanguage evid := { showForNaturalLanguage := showForProofTree }.
Instance : ShowForLogSeq evid := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForProofTree claim := {
  showForProofTree :=
  fix showForProofTreeClaim c :=
    match c with
      | AtomicClaim name => showForProofTree name
      | Bottom => "\bot"
      | And c1 c2 => "(" ++ showForProofTreeClaim c1 ++ " \wedge " ++ showForProofTreeClaim c2 ++ ")"
      | Or c1 c2 => "(" ++ showForProofTreeClaim c1 ++ " \vee " ++ showForProofTreeClaim c2 ++ ")"
      | Implies c1 c2 => "(" ++ showForProofTreeClaim c1 ++ " \rightarrow " ++ showForProofTreeClaim c2 ++ ")"
    end
}.

Instance : ShowForNaturalLanguage claim := {
  showForNaturalLanguage :=
  fix showForNaturalLanguageClaim c :=
    match c with
      | AtomicClaim name => showForNaturalLanguage name
      | Bottom => "impossible"
      | And c1 c2 => "(" ++ showForNaturalLanguageClaim c1 ++ " and " ++ showForNaturalLanguageClaim c2  ++ ")"
      | Or c1 c2 => "(" ++ showForNaturalLanguageClaim c1 ++ " or " ++ showForNaturalLanguageClaim c2 ++ ")"
      | Implies c1 c2 => "(" ++ showForNaturalLanguageClaim c1 ++ " implies " ++ showForNaturalLanguageClaim c2 ++ ")"
    end
}.
Instance : ShowForLogSeq claim := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForProofTree actor := {
  showForProofTree a :=
  match a with
    | Actor name => showForProofTree name
  end
}.

Instance : ShowForNaturalLanguage actor := {
  showForNaturalLanguage a :=
  match a with
    | Actor name => showForNaturalLanguage name
  end
}.

Instance : ShowForLogSeq actor := {
  showForLogSeq a :=
  match a with
    | Actor name => showForLogSeq name
  end
}.

Instance : ShowForProofTree trustRelation := {
  showForProofTree t :=
  match t with
    | Trust name => showForProofTree name
  end
}.

Instance : ShowForNaturalLanguage trustRelation := {
  showForNaturalLanguage t :=
  match t with
    | Trust name => showForNaturalLanguage name
  end
}.

Instance : ShowForLogSeq trustRelation := {
  showForLogSeq t :=
  match t with
    | Trust name => showForLogSeq name
  end
}.

Fixpoint showForProofTree_list {A} `{ShowForProofTree A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => showForProofTree h
    | h1 :: (h2 :: tl) as tl' => showForProofTree h1 ++ ", " ++ showForProofTree_list tl'
  end.

Instance showForProofTree_list_instance (A : Type) `(ShowForProofTree A) : ShowForProofTree (list A) := {
  showForProofTree l := showForProofTree_list l
}.

Fixpoint showForNaturalLanguage_list {A} `{ShowForNaturalLanguage A} (l : list A) :=
  match l with
    | [] => "no items"
    | [h] => showForNaturalLanguage h
    | [h1;h2] => showForNaturalLanguage h1 ++ ", and " ++ showForNaturalLanguage h2
    | h1 :: (h2 :: tl) as tl' => showForNaturalLanguage h1 ++ ", " ++ showForNaturalLanguage_list tl'
  end.
Instance showForNaturalLanguage_list_instance (A : Type) `(ShowForNaturalLanguage A) : ShowForNaturalLanguage (list A) := {
    showForNaturalLanguage l := showForNaturalLanguage_list l
  }.

Fixpoint showForLogSeq_list {A} `{ShowForLogSeq A} (indent : string) (l : list A) :=
  match l with
    | [] => ""
    | [h] => indent ++ "- " ++ showForLogSeq h
    | h :: tl => indent ++ "- " ++ showForLogSeq h ++ "
" ++ showForLogSeq_list indent tl
  end.

Instance : ShowForProofTree judgement := {
  showForProofTree j :=
  match j with
  | Judgement e a w c => showForProofTree e ++ "^{" ++ showForProofTree a ++ "}_{" 
                         ++ showForProofTree w ++ "} \in " ++ showForProofTree c
  end
}.

Instance : ShowForNaturalLanguage judgement := {
  showForNaturalLanguage j :=
  match j with
  | Judgement e a w c => showForNaturalLanguage c ++ " is supported by $" ++ showForNaturalLanguage e ++ "$ at weight $" ++ showForNaturalLanguage w ++ "$ which " ++ showForNaturalLanguage a ++ " uses"
  end
}.

Instance : ShowForLogSeq judgement := {
  showForLogSeq j :=
  match j with
  | Judgement e a w c => showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence $" ++ showForLogSeq e ++ "$ at weight $" ++ showForLogSeq w ++ "$"
  end
}.

Definition showForProofTree_judgement (Ts : list trustRelation) (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j) :=
    match Ps with
      | [] => showForProofTree j
      | (h :: tl) as Ps => showForProofTree Ps ++ " \vdash_{" ++ showForProofTree Ts ++ "} " ++ (showForProofTree j)
    end.

Definition showForNaturalLanguage_judgement (Ts : list trustRelation) (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j) :=
  match Ps with
    | [] => showForNaturalLanguage j
    | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage j
  end.

Definition showForLogSeq_judgement (Ts : list trustRelation) (indent : string) (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j) :=
  match Ps,Ts with
        | [],[] => showForLogSeq j
        | (h :: tl),[] => showForLogSeq j ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Assumptions made:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ps
        | [],(h :: tl) => showForLogSeq j ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Trust relations used:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ts
        | (h :: tl),(h2::tl2) => showForLogSeq j ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Assumptions made:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ts
  end.

Fixpoint getAllTrustRelationsUsed (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j)
  : list trustRelation :=
match p with
| assume e a w C => []
| bot_elim e a w C Ps M => getAllTrustRelationsUsed _ _ M
| and_intro e1 e2 a w1 w2 w3 C1 C2 Ps Qs Rs H HWeight L R => 
    getAllTrustRelationsUsed _ _ L ++ getAllTrustRelationsUsed _ _ R 
| and_elim1 e1 e2 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| and_elim2 e1 e2 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| or_intro1 e1 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| or_intro2 e2 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| or_elim1 e1 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| or_elim2 e2 a w C1 C2 Ps M => getAllTrustRelationsUsed _ _ M
| trust e a1 a2 wTrust w1 w2 C name Ps HWeight L => name :: getAllTrustRelationsUsed _ _ L
| impl_intro _ _ _ _ _ _ _ _ _ _ _ _ M => getAllTrustRelationsUsed _ _ M
| impl_elim _ _ _ _ _ _ _ _ _ _ _ _ _ L R => getAllTrustRelationsUsed _ _ L ++ getAllTrustRelationsUsed _ _ R 
end.

Fixpoint getAllEvidence (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j)
  : list evid :=
match p with
| assume e a w C => [(AtomicEvid e)]
| bot_elim e a w C _ M => (getAllEvidence _ _ M)
| and_intro e1 e2 a w1 w2 w3 C1 C2 Ps Qs Rs H HWeight L R => getAllEvidence _ _ L ++ getAllEvidence _ _ R 
| and_elim1 e1 e2 a w C1 C2 _ M => getAllEvidence _ _ M
| and_elim2 e1 e2 a w C1 C2 _ M => getAllEvidence _ _ M
| or_intro1 e1 a w C1 C2 _ M => getAllEvidence _ _ M
| or_intro2 e2 a w C1 C2 _ M => getAllEvidence _ _ M
| or_elim1 e1 a w C1 C2 _ M => getAllEvidence _ _ M
| or_elim2 e2 a w C1 C2 _ M => getAllEvidence _ _ M
| trust e a1 a2 wTrust w1 w2 C name _ _ L => getAllEvidence _ _ L
| impl_intro _ _ _ _ _ _ _ _ _ _ _ _ M => getAllEvidence _ _ M
| impl_elim _ _ _ _ _ _ _ _ _ _ _ _ _ _ M => getAllEvidence _ _ M
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Definition getAssumptions (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j) : list judgement := Ps.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
    match l with
    | [] => []
    | h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
    end.

Fixpoint showForProofTree_proofTreeOf_helper (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed Ps j p)) in
match p with
| assume e a w C => "\AxiomC{$ " 
             ++ showForProofTree C 
             ++ " \textit{ is a veracity claim} $}"
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showForProofTree_judgement Ts _ _ p ++ " $}"
| bot_elim e a w C _ M => showForProofTree_proofTreeOf_helper _ _ M
    ++ " \RightLabel{ $ \bot^{-} $} \UnaryInfC{$ "
    ++ showForProofTree_judgement Ts _ _ p
    ++ " $}"
| and_intro e1 e2 a w1 w2 w3 C1 C2 _ _ _ _ _ L R => 
    showForProofTree_proofTreeOf_helper _ _ L
 ++ showForProofTree_proofTreeOf_helper _ _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p ++ " $}"
| and_elim1 e1 e2 a w C1 C2 _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \land^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| and_elim2 e1 e2 a w C1 C2 _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \land^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| or_intro1 e1 a w C1 C2 _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| or_intro2 e2 a w C1 C2_ _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| or_elim1 e1 a w C1 C2_ _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \lor^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| or_elim2 e2 a w C1 C2 _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \lor^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| trust e a1 a2 wTrust w1 w2 C name _ _ L => 
    showForProofTree_proofTreeOf_helper _ _ L
 ++ " \AxiomC{$" ++ showForProofTree a1 ++ showForProofTree name ++ showForProofTree a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ showForProofTree name ++ "\ (" ++ showForProofTree wTrust ++ ")"
 ++ "$} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p ++ " $}"
| impl_intro e1 e2 a w1 w2 C1 C2 H _ _ _ _ M => showForProofTree_proofTreeOf_helper _ _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p
 ++ " $}"
| impl_elim x bx y a w1 w2 C1 C2 H1 _ _ _ _ L R => 
     showForProofTree_proofTreeOf_helper _ _ L
 ++ showForProofTree_proofTreeOf_helper _ _ R 
 ++ " \RightLabel{ $ \rightarrow^{-} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ts _ _ p ++ " $}"
end.

Fixpoint showForNaturalLanguage_proofTreeOf_helper (indent : string) (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed Ps j p)) in
match p with
| assume e a w C => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ "  " ++ indent ++ showForNaturalLanguage C ++ " is a veracity claim." ++ "
"
++ indent ++ "by assumption."
| bot_elim e a w C _ M =>
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by the logical principle of explosion."
| and_intro e1 e2 a w1 w2 w3 C1 C2 _ _ _ _ _ L R => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ R ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim1 e1 e2 a w C1 C2 _ M =>
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim2 e1 e2 a w C1 C2 _ M => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| or_intro1 e1 a w C1 C2 _ M =>
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_intro2 e2 a w C1 C2 _ M =>
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim1 e1 a w C1 C2 _ M =>
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim2 e2 a w C1 C2 _ M => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| trust e a1 a2 wTrust w1 w2 C name _ _ L => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ L ++ "
"
++ indent ++ "by the trust relation " ++ showForNaturalLanguage name ++ " with weight $" ++ showForNaturalLanguage wTrust ++ "$."
| impl_intro _ _ _ _ _ _ _ _ _ _ _ _ M => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ M ++ "
"
++ indent ++ "by a logical rule for implication."
| impl_elim _ _ _ _ _ _  _ _ _ _ _ _ _ L R => 
indent ++ showForNaturalLanguage_judgement Ts _ _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ _ R ++ "
"
++ indent ++ "by a logical rule for implication."
end.

Fixpoint showForLogSeq_proofTreeOf_helper (indent : string) (Ps : list judgement) (j : judgement) (p : proofTreeOf Ps j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed Ps j p)) in
match p with
| assume e a w C => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: we assume this"
| bot_elim e a w C _ M =>
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: the principle of explosion
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| and_intro e1 e2 a w1 w2 w3 C1 C2 _ _ _ _ _ L R => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and introduction
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ R
| and_elim1 e1 e2 a w C1 C2 _ M =>
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| and_elim2 e1 e2 a w C1 C2 _ M => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| or_intro1 e1 a w C1 C2 _ M =>
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| or_intro2 e2 a w C1 C2 _ M =>
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| or_elim1 e1 a w C1 C2 _ M =>
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| or_elim2 e2 a w C1 C2 _ M => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| trust e a1 a2 wTrust w1 w2 C name _ _ L => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: trust, with relation " ++ showForLogSeq name ++ " with weight $" ++ showForLogSeq wTrust ++ "$
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ L
| impl_intro _ _ _ _ _ _ _ _ _ _ _ _ M => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication introduction
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ M
| impl_elim _ _ _ _ _ _  _ _ _ _ _ _ _ L R => 
indent ++ "- " ++ showForLogSeq_judgement Ts ("  " ++ indent) _ _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication elimination
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ _ R
end.

Open Scope string.

Fixpoint showForProofTree_list_newline {A} `{ShowForProofTree A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => showForProofTree h
    | h1 :: (h2 :: tl) as tl' => showForProofTree h1 ++ "
" ++ showForProofTree_list_newline tl'
  end.

Definition showForProofTree_proofTreeOf Ps j p
  := "\begin{prooftree}" ++ showForProofTree_proofTreeOf_helper Ps j p
       ++ "\end{prooftree}".
Instance showForProofTree_proofTreeOf_instance Ps (j : judgement)
  : ShowForProofTree (proofTreeOf Ps j) := { showForProofTree := showForProofTree_proofTreeOf Ps j}.

Definition showForNaturalLanguage_proofTreeOf Ps j (p : proofTreeOf Ps j) := "

" ++ showForNaturalLanguage_proofTreeOf_helper "- " Ps j p ++ "

".
Instance showForNaturalLanguage_proofTreeOf_instance Ps (j : judgement)
  : ShowForNaturalLanguage (proofTreeOf Ps j) := { showForNaturalLanguage := showForNaturalLanguage_proofTreeOf Ps j}.

Definition printProofTitle j :=
match j with
| Judgement e a w c => "### Veracity proof that " ++ showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence $" ++ showForLogSeq e ++ "$ at weight $" ++ showForLogSeq w ++ "$"
end.

Instance : ShowForLogSeq string := { showForLogSeq := id}.

Definition showForLogSeq_proofTreeOf Ps j (p : proofTreeOf Ps j) := 
let evidenceList := (removeDups (filter isAtomicEvidence (getAllEvidence Ps j p))) in
let evidenceWithNames := map (fun e => match e with
                                   | AtomicEvid n => showForLogSeq e ++ " = " ++ showForLogSeq n
                                   | _ => ""
                                   end) evidenceList in
"

" ++ printProofTitle j ++ "
" ++ showForLogSeq_proofTreeOf_helper "  " Ps j p ++ "
  - Atomic evidence is abbreviated as follows:
    collapsed:: true
" ++ showForLogSeq_list "    " evidenceWithNames ++ "

".
Instance showForLogSeq_proofTreeOf_instance Ps (j : judgement)
  : ShowForLogSeq (proofTreeOf Ps j) := { showForLogSeq := showForLogSeq_proofTreeOf Ps j}.

Fixpoint showListOfProofTrees {Ps} {j : judgement} (l : list (proofTreeOf Ps j)) :=
    match l with
      | [] => ""
      | h :: tl => "

----------------

" ++ showForProofTree h ++ showListOfProofTrees tl
    end.

Instance showForProofTree_proofTreeOf_wrapped_instance (a : actor) (c : claim) : ShowForProofTree (proofTreeOf_wrapped a c) := { showForProofTree p := showForProofTree (_p a c p) }.
Instance showForNaturalLanguage_proofTreeOf_wrapped_instance (a : actor) (c : claim) : ShowForNaturalLanguage (proofTreeOf_wrapped a c) := { showForNaturalLanguage p := showForNaturalLanguage (_p a c p) }.
Instance showForLogSeq_proofTreeOf_wrapped_instance (a : actor) (c : claim) : ShowForLogSeq (proofTreeOf_wrapped a c) := { showForLogSeq p := showForLogSeq (_p a c p) }.

Open Scope beq_scope.

(*|

Examples
--------

|*)

(*|

Example applications of each rule
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|*)

(*|

Using the `assume` rule gives the leaf nodes of the proof trees.
It allows any judgement to be shown to have veracity from exactly that assumption in the list of assumptions.

|*)

Lemma assume_example :
  proofTreeOf [(e \by a1 @ (1 # 3) \in c1)] (e \by a1 @ (1 # 3) \in c1).
Proof.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree assume_example).

(*|
.. coq::
|*)

(*|

`bot_elim` allows us to conclude any claim from evidence for the claim that should never have veracity, :math:`\bot`.

|*)

Lemma bot_elim_example :
  proofTreeOf [(eB \by a1 @ (1 # 3) \in _|_)] (eB \by a1 @ (1 # 3) \in (c1 \/' c2)).
Proof.
apply bot_elim.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree bot_elim_example).

(*|
.. coq::
|*)

(*|

`and_intro` combines two proof trees, taking the minimum weight of the two as the weight for the resulting conjunction.

|*)

Lemma and_intro_example : proofTreeOf [(e1 \by a1 @ (1 # 3) \in c1); (e2 \by a1 @ (1 # 2) \in c2)] ({{e1,e2}} \by a1 @ (1 # 3) \in (c1 /\' c2)).
Proof.
apply and_intro with (w1:=(1#3)) (w2:=(1#2)) (Ps:=[e1 \by a1 @ 1 # 3 \in c1]) (Qs:=[e2 \by a1 @ 1 # 2 \in c2]). 1-2: reflexivity.
apply assume.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree and_intro_example).

(*|
.. coq::
|*)

(*|

`and_elim1` allows us to conclude the left conjunct from a conjunctive claim.
It requires that the evidence is a `Pair`, here written as `{{e1, e2}}`.
The weight remains the same.

|*)

Lemma and_elim1_example : proofTreeOf [(e1 \by a1 @ (1 # 3) \in c1); (e2 \by a1 @ (1 # 2) \in c2)] (e1 \by a1 @ (1 # 3) \in c1).
Proof.
apply and_elim1 with (e2:=e2) (C2:=c2).
apply and_intro with (w1:=(1#3)) (w2:=(1#2)) (Ps:=[e1 \by a1 @ 1 # 3 \in c1]) (Qs:=[e2 \by a1 @ 1 # 2 \in c2]). 1-2: reflexivity.
apply assume.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree and_elim1_example).

(*|
.. coq::
|*)

(*|

`and_elim2` is similar to `and_elim1` but allows us to conclude the right conjunct.

|*)

Lemma and_elim2_example : proofTreeOf [(e1 \by a1 @ (1 # 3) \in c1); (e2 \by a1 @ (1 # 2) \in c2)] (e2 \by a1 @ (1 # 3) \in c2).
Proof.
apply and_elim2 with (e1:=e1) (C1:=c1).
apply and_intro with (w1:=(1#3)) (w2:=(1#2)) (Ps:=[e1 \by a1 @ 1 # 3 \in c1]) (Qs:=[e2 \by a1 @ 1 # 2 \in c2]). 1-2: reflexivity.
apply assume.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree and_elim2_example).

(*|
.. coq::
|*)

(*|

`or_intro1` allows us to conclude a disjunctive claim by tagging the evidence with `Left`, represented in Latex as :math:`i(...)`.
This indicates that the disjunctive claim has veracity because the left disjunct had been shown to have veracity.
The right disjunct can be any claim.

|*)

Lemma or_intro1_example :
  proofTreeOf [(e \by a1 @ (1 # 3) \in c1)] ((Left e) \by a1 @ (1 # 3) \in (c1 \/' c2)).
Proof.
apply or_intro1.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree or_intro1_example).

(*|
.. coq::
|*)

(*|

`or_intro2` similarly allows us to conclude a disjunctive claim but by tagging the evidence with `Right`, represented in Latex as :math:`j(...)`.
The left disjunct can be any claim.

|*)

Lemma or_intro2_example :
  proofTreeOf [(e \by a1 @ (1 # 3) \in c2)] ((Right e) \by a1 @ (1 # 3) \in (c1 \/' c2)).
Proof.
apply or_intro2.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree or_intro2_example).

(*|
.. coq::
|*)

(*|

`or_elim1` allows us to conclude the left disjunct from a disjunctive claim whose veracity came from the left disjunct, as evident from tagged evidence.

|*)

Lemma or_elim1_example :
  proofTreeOf [(e \by a1 @ (1 # 3) \in c1)] (e \by a1 @ (1 # 3) \in c1).
Proof.
apply or_elim1 with (C2:=c2). (* .unfold *)
(*|

Here we see the proof state before and after `or_elim1` is applied.

|*)
apply or_intro1. (* .unfold *)
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree or_elim1_example).

(*|
.. coq::
|*)

(*|

`or_elim2` similarly allows us to conclude the right disjunct from a disjunctive claim whose veracity came from the right disjunct.

|*)

Lemma or_elim2_example :
  proofTreeOf [(e \by a1 @ (1 # 3) \in c2)] (e \by a1 @ (1 # 3) \in c2).
Proof.
apply or_elim2 with (C1:=c1). (* .unfold *)
apply or_intro2. (* .unfold *)
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree or_elim2_example).

(*|
.. coq::
|*)

(*|

All the other rules require the actor to stay the same, `trust` allows the actor holding that the claim has veracity to change.
An application of the rule `trust` is intended to implicitly declare that the named trust relation, in this case `trustT`, relates the two actors `a1` and `a2` with the weight `wTrust`.
Currently, there is no mechanism forcing that `trust` is used in a consistent manner.
One could, for instance, use `trustT` with Penelope and Quentin with weight :math:`\frac{1}{3}` and then elsewhere use `trustT` again with Penelope Quentin but with weight :math:`\frac{1}{2}`.
This could be prevented with a technique such as explored in the branch `WIP-with-fDef-as-proofTreeOf-parameter` for the related challenge of ensuring that functions are applied consistently (which has been solved with `apply_abstraction` in the current code-base, not requiring `by_def1`/`by_def2`). See: https://github.com/Coda-Coda/Veracity-Logic-Mechanised/blob/5351832ae3d9a32b3a13eb5a5865b35b30ff3b47/Coq/VeracityLogic.v#L398 for the `fDef` approach.

|*)

Lemma trust_example :
  proofTreeOf [(e \by Penelope @ (1 # 3) \in c1)] (e \by Quentin @ (1 # 6) \in c1). (* .unfold *)
Proof.
(*|
Applying the rule `trust` leaves us with three subgoals.
|*)
apply trust with (a2:=Penelope) (wTrust:=1#2) (w1:=1#3). (* .unfold *)
(*|

The first is just to name which trust relation we are using, in this case `trustT`.
It would be better if we could have used the syntax `(name:=trustT)` but unfortunately we cannot do that in this case.

The second subgoal can be solved by `reflexivity`.

The third subgoal now has the actor `Penelope` rather then `Quentin`.
|*)
apply trustT. reflexivity.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree trust_example).

(*|
.. coq::
|*)

(*|

------------

As a side note, notice that we end all these proof tree "Lemmas" with the keyword `Defined`. Recall that `proofTreeOf Ps j` is a `Type` not a `Prop` and that we use pattern matching on proof trees to generate Latex strings and perform other computations about proof trees. The keyword `Defined` makes the proof tree definitions transparent and not opaque, which makes it possible (among other things) to generate Latex strings from them. For more information about `Defined` see https://coq.inria.fr/doc/V8.17.1/refman/proofs/writing-proofs/proof-mode.html?highlight=defined#coq:cmd.Defined.

In addition to this, notice that we are using Coq's "proof mode" to construct *values* of type `proofTreeOf Ps j`. While it feels a bit like we are doing proofs about propositions, we are actually just constructing trees, *values*, that follow the rules of the `proofTreeOf` type. This is a somewhat related to the Curry-Howard correspondence where we see that constructing proofs of propositions is like constructing values of a particular type. The fact that we can use "proof mode" to carry out both tasks is related to the Curry-Howard correspondence. For more information on the Curry-Howard correspondence, see: https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html.

------------

|*)

Lemma impl_intro_example : proofTreeOf [] ((Lambda _e_ (1#4) e) \by a1 @ (1 # 4) \in (Implies c1 c1)).
apply impl_intro with (Ps:=[e \by a1 @ 1 # 4 \in c1]). 1-3: reflexivity.
apply assume.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro_example).

(*|
.. coq::
|*)


Lemma impl_elim_example : proofTreeOf [(e2 \by a1 @ (1 # 4) \in c1)] ((e2 \by a1 @ (1 # 4) \in c1)).
apply impl_elim with (x:=_e1_) (bx:=e1) (w1:=1#4) (C1:=c1) (Ps:=[]) (Qs:=[e2 \by a1 @ 1 # 4 \in c1]) (H2:=eq_refl). reflexivity.
apply impl_intro with (Ps:=[e1 \by a1 @ 1 # 4 \in c1]). 1-3: reflexivity.
apply assume.
apply assume.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_elim_example).

(*|
.. coq::
|*)


(*|

Other examples
~~~~~~~~~~~~~~

|*)


Eval compute in showForProofTree_judgement [] [(e1 \by a1 @ 1 \in c1)] (e1 \by a1 @ 1 \in c1) (assume _e1_ a1 1 c1).


Definition process_example : proofTreeOf_wrapped Penelope (c3 ->' (c2 ->' (c1 ->' (c1 /\' c2 /\' c3)))).
Proof.
eexists  _ _ _.
eapply impl_intro with (x:=_z_) (Ps := [j3]) (Qs:=[]) (w1 := 1) (w2 := 1). 1-3: shelve.
eapply impl_intro with (x:=_y_) (Ps := [j2;j3]) (Qs:=[j3]) (w1 := 1) (w2 := 1). 1-3: shelve.
eapply impl_intro with (x:=_x_) (Ps := [j1;j2;j3]) (Qs:=[j2;j3]) (w1 := 1) (w2 := 1). 1-3: shelve.
eapply and_intro with (Ps := [j1;j2]) (w3 := 1). 1-2: shelve.
eapply and_intro with (w3 := 1). 1-2: shelve.
apply assume with (e := _x_) (w := 1).
apply assume with (e := _y_) (w := 1).
apply assume with (e := _z_) (w := 1).
Unshelve.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree process_example).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage process_example).
Eval compute in (showForLogSeq process_example).

Definition impl_intro1 : proofTreeOf_wrapped a1 ((Implies c1 c1)).
eexists [] _ _.
eapply (impl_intro _e1_ _ _ 1 1 _ _ _ _ _ _ _).
eapply (assume _e1_ _ 1).
Unshelve.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro1).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_intro1).
Eval compute in (showForLogSeq impl_intro1).

Definition impl_intro_elim : proofTreeOf_wrapped a1 (c1).
eexists [(AtomicEvid _e2_) \by a1 @ 1 \in c1] _ 1.
eassert (apply_abstraction _e1_ e1 e2 _ = e2).
simpl. reflexivity. Unshelve. 3: reflexivity. 2: shelve.
fold e2.
rewrite <- H.

eapply (impl_elim _e1_ e1 e2 a1 1 1 C1 C1 _ _ _ _).
eapply (impl_intro _e1_ _ _ 1 1 _ _ _ [] _ _ _).
eapply (assume _e1_ _ 1).
eapply (assume _e2_ _ 1).
Unshelve.
all: try reflexivity.
Defined.
    
(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro_elim).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_intro_elim).
Eval compute in (showForLogSeq impl_intro_elim).


Definition and_example : proofTreeOf_wrapped a1 (Implies c1 (c1 /\' c1)).
eexists []  _ 1.
eapply (impl_intro _e1_ _ _ 1 1 _ _ [e1 \by a1 @ 1 \in c1] _ _ _ _).
eapply and_intro with (Ps:= [e1 \by a1 @ 1 \in c1]) (Qs:= [e1 \by a1 @ 1 \in c1]) (w1 := 1) (w2 := 1) (w3 := 1). 1-2: reflexivity.
eapply (assume _e1_ _ 1).
eapply (assume _e1_ _ 1).
Unshelve.
all: reflexivity.
Defined.

 (*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree and_example).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage and_example).
Eval compute in (showForLogSeq and_example).

Definition l := AtomicEvid _l_ .
Definition s := AtomicEvid _s_.
Definition c := AtomicEvid _c_.

Program Definition concreteProofTreeExampleWith2Conjuncts : 
proofTreeOf [l \by Penelope @ 1 \in c1;s \by Penelope @ 1\in c2] ({{l, s}} \by Penelope @ 1 \in (C1 /\' C2)).
eapply and_intro with (Ps:= [l \by Penelope @ 1 \in c1]) (Qs:= [s \by Penelope @ 1 \in c2]) (w1 := 1) (w2 := 1) (w3 := 1). 1-2: reflexivity.
apply assume.
apply assume.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree concreteProofTreeExampleWith2Conjuncts).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleWith2Conjuncts).
Eval compute in showForLogSeq concreteProofTreeExampleWith2Conjuncts.

Program Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2;c \by Penelope @ 1 \in c3] ({{{{l, s}},c}} \by Penelope @ 1 \in (C1 /\' C2 /\' C3)).
eapply and_intro with (Ps:= [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2]) (Qs:= [c \by Penelope @ 1 \in c3]) (w1 := 1) (w2 := 1) (w3 := 1). 1-2: reflexivity.
eapply and_intro with (Ps:= [l \by Penelope @ 1 \in c1]) (Qs:= [s \by Penelope @ 1 \in c2]) (w1 := 1) (w2 := 1) (w3 := 1). 1-2: reflexivity.
apply (assume _l_).
apply (assume _s_).
apply (assume _c_).
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree concreteProofTreeExampleWith3Conjuncts).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleWith3Conjuncts).
Eval compute in showForLogSeq concreteProofTreeExampleWith3Conjuncts.

(*|
We can also combine existing trees into new trees, when appropriate. For example:
|*)

Program Definition concreteProofTreeExampleWith3ConjunctsUsingExistingTree : 
proofTreeOf [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2;c \by Penelope @ 1 \in c3] ({{{{l, s}},c}} \by Penelope @ 1 \in (C1 /\' C2 /\' C3)).
eapply and_intro with (Ps:= [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2]) (Qs:= [c \by Penelope @ 1 \in c3]) (w1 := 1) (w2 := 1) (w3 := 1). 1-2: reflexivity.
exact concreteProofTreeExampleWith2Conjuncts.
Show Proof.
apply (assume _c_).
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree concreteProofTreeExampleWith3Conjuncts).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleWith3Conjuncts).
Eval compute in showForLogSeq concreteProofTreeExampleWith3Conjuncts.

Program Definition concreteProofTreeExampleTrust : 
proofTreeOf [e \by a2 @ 1 \in (c1)] e \by a1 @ 1 \in (c1).
eapply (trust _ a1 a2 1 1 1 c1 trustT). reflexivity.
apply (assume _e_).
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree concreteProofTreeExampleTrust).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleTrust).
Eval compute in showForLogSeq concreteProofTreeExampleTrust.

Program Definition concreteProofTreeExampleWith3ConjunctsWithTrust : 
proofTreeOf [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2;c \by Penelope @ 1 \in c3] ({{{{l, s}},c}} \by Quentin @ 1 \in (C1 /\' C2 /\' C3)).
eapply (trust _ _ _ 1 1 1 _ trustU). reflexivity.
apply concreteProofTreeExampleWith3ConjunctsUsingExistingTree.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrust). 

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleWith3ConjunctsWithTrust).
Eval compute in showForLogSeq concreteProofTreeExampleWith3ConjunctsWithTrust.

Program Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
proofTreeOf [l \by Penelope @ 1 \in c1;s \by Penelope @ 1 \in c2;c \by Penelope @ 1 \in c3] ({{{{l, s}},c}} \by Quentin @ 1 \in (C1 /\' C2 /\' C3)).
eapply (trust _ Quentin Quentin 1 1 1 _ trustU). reflexivity.
eapply (trust _ Quentin Quentin 1 1 1 _ trustV). reflexivity.
eapply (trust _ _ _ 1 1 1 _ trustU). reflexivity.
apply concreteProofTreeExampleWith3ConjunctsUsingExistingTree.
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in (showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras). 

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras).
Eval compute in showForLogSeq concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras. 


Definition exampleWithProofOf : proofTreeOf_wrapped a1 C1.
Proof.
eexists _ _ _.
apply (assume _e_ a1 1).
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree exampleWithProofOf.


(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage exampleWithProofOf.
Eval compute in showForLogSeq exampleWithProofOf.

Definition bot_example : proofTreeOf_wrapped a1 (_|_ ->' (C1 /\' C2)).
Proof.
eexists [] _ _.
eapply (impl_intro _eB_ _ a1) with (Ps := [(AtomicEvid _eB_) \by a1 @ 1 \in _|_]) (w1 := 1). 1,2,3: shelve.
apply bot_elim with (w := 1).
apply (assume _eB_ _ 1).
Unshelve.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree bot_example.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage bot_example.
Eval compute in showForLogSeq bot_example.

Definition bot_example2 : proofTreeOf_wrapped a1 (_|_ ->' (C1 \/' C2 ->' (C3 /\' _|_))).
Proof.
eexists [] _ _.
eapply (impl_intro _eB_ _ a1) with (Ps := [(AtomicEvid _eB_) \by a1 @ 1 \in _|_]) (w1 := 1). 1,2,3: shelve.
apply bot_elim.
apply (assume _eB_ _ 1).
Unshelve.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree bot_example2.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage bot_example2.
Eval compute in showForLogSeq bot_example2.


Program Definition starP : 
proofTreeOf [l \by Ledger @ 1 \in c1] (l \by Penelope @ (1 # 3) \in C1).
eapply (trust _ Penelope Ledger (1 # 3) 1 (1 # 3) _ trustT). reflexivity.
eapply (assume _ _ 1).
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree starP).

(*|
.. coq::
|*)

Eval compute in (showForLogSeq starP).


Program Definition chain : 
proofTreeOf [e \by Penelope @ 1 \in c1] (e \by Ulysses @ (1 # 32) \in C1).
eapply (trust _ Ulysses Tom (1 # 2) (1 # 16) (1 # 32) _ trustA). reflexivity.
eapply (trust _ Tom Samantha (1 # 2) (1 # 8) (1 # 16)  _ trustA). reflexivity.
eapply (trust _ Samantha Ryan (1 # 2) (1 # 4) (1 # 8) _ trustA). reflexivity.
eapply (trust _ Ryan Quentin (1 # 2) (1 # 2) (1 # 4) _ trustA). reflexivity.
eapply (trust _ Quentin Penelope (1 # 2) 1 (1 # 2) _ trustA). reflexivity.
eapply (assume _ _ 1).
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in (showForProofTree chain). 

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage chain).
Eval compute in (showForLogSeq chain).

Program Definition chainWithAnd : 
proofTreeOf [e1 \by Penelope @ 1 \in c1; e2 \by Quentin @ 1 \in c2] ({{e1,e2}} \by Samantha @ (1 # 4) \in (C1 /\' C2)).
eapply and_intro with (Ps := [e1 \by Penelope @ 1 \in c1]) (Qs := [e2 \by Quentin @ 1 \in c2]) (w1 := 1 # 4) (w2 := 1 # 2). 1-2: reflexivity.
eapply (trust _ Samantha Quentin (1 # 2) (1 # 2) (1 # 4) _ trustB). reflexivity.
eapply (trust _ Quentin Penelope (1 # 2) 1 (1 # 2) _ trustA). reflexivity.
eapply (assume _ _ 1).
eapply (trust _ Samantha Quentin (1 # 2) 1 (1 # 2) _ trustB). reflexivity.
eapply (assume _ _ 1).
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree chainWithAnd). 

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage chainWithAnd). 
Eval compute in (showForLogSeq chainWithAnd). 

Definition impl_intro_elim_with_weights : proofTreeOf_wrapped a1 (c1).
eexists [(AtomicEvid _e2_) \by a1 @ (1 # 2) \in c1] _ (1 # 2).
eassert (apply_abstraction _e1_ e1 e2 _ = e2).
simpl. reflexivity. Unshelve. 3: reflexivity. 2: shelve.
fold e2.
rewrite <- H.

eapply (impl_elim _e1_ e1 e2 a1 (1 # 2) (1 # 2) C1 C1 _ _ _ _).
eapply (impl_intro _e1_ _ _ (1 # 2) (1 # 2) _ _ _ [] _ _ _).
eapply (assume _e1_ _ (1 # 2)).
eapply (assume _e2_ _ (1 # 2)).
Unshelve.
all: try reflexivity.
Defined.
    
(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro_elim_with_weights).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_intro_elim_with_weights).
Eval compute in (showForLogSeq impl_intro_elim_with_weights).

Definition impl_intro_elim_with_different_weights : proofTreeOf_wrapped a1 (c1 /\' c2).
eexists [e3 \by a1 @ (1 # 2) \in c1; e4 \by a1 @ (1 # 3) \in c2] {{e3,e4}} (1 # 3).
eassert (apply_abstraction _e2_ e2 e3 _ = e3).
simpl. reflexivity. Unshelve. 2: reflexivity.
fold e3.
rewrite <- H.

eapply (impl_elim _e2_ {{e3,e2}} e4 a1 (1 # 3) (1 # 3) C2 (C1 /\' C2)) with (Ps := [e3 \by a1 @ 1 # 2 \in c1]) (Qs := [e4 \by a1 @ (1 # 3) \in c2]) (Rs := [(apply_abstraction _e2_ e2 e3 eq_refl) \by a1 @ 1 # 2 \in c1; e4 \by a1 @ (1 # 3) \in c2]).
simpl. reflexivity.
2: eapply assume.
Unshelve. 2: reflexivity.

eassert (apply_abstraction _e1_ (Lambda _e2_ (1 # 3) {{e3,e2}}) e3    _ = (Lambda _e2_ (1 # 3) {{e3,e2}})).
simpl. reflexivity. Unshelve. 2: reflexivity.
fold e2.
rewrite <- H0.

eapply (impl_elim _e1_ (Lambda _e2_ (1 # 3) {{e1,e2}}) e3 a1 (1 # 2) (1 # 3) C1 (C2 ->' C1 /\' C2)) with (Ps := []) (Qs := [(apply_abstraction _e2_ e2 e3 eq_refl) \by a1 @ 1 # 2 \in c1]) (Rs := [(apply_abstraction _e2_ e2 e3 eq_refl) \by a1 @ 1 # 2 \in c1]). reflexivity.

simpl.

eapply impl_intro with (Ps := [(AtomicEvid _e1_) \by a1 @ 1 # 2 \in C1]). reflexivity. reflexivity. simpl. reflexivity.

eapply impl_intro

with (Ps := [(AtomicEvid _e2_) \by a1 @ 1 # 3 \in C2; (AtomicEvid _e1_) \by a1 @ 1 # 2 \in C1])
. 
reflexivity. simpl. reflexivity. simpl. reflexivity.

eapply and_intro with (Ps := [(AtomicEvid _e1_) \by a1 @ 1 # 2 \in C1]) (Qs := [(AtomicEvid _e2_) \by a1 @ 1 # 3 \in C2]) (w1 := 1#2) (w2 := 1#3). reflexivity. reflexivity.

eapply assume.
eapply assume.
simpl.
eapply assume.

Defined.
    
(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro_elim_with_different_weights).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_intro_elim_with_different_weights).
Eval compute in (showForLogSeq impl_intro_elim_with_different_weights).



End VeracityLogic.

(*|
*The proofs on this page are rendered using MathJax which happens to require at least one explicit math command*. Hence: :math:`x`.
|*)