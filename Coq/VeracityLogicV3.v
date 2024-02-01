(*|
Veracity Logic Mechanised in Coq V3
===================================

This version aims to more closely align with the draft paper.
It also features a LaTeX/MathJax visualisation of completed proofs.

This is possible due to not using :coq:`Prop` at all. "*In fact in my logic there are no propositions*" - Steve.
Instead, this aims to model the process of constructing proof trees, just like they are done on paper.

A correct proof tree is a datatype with similarities to a tree datatype, which makes it possible to write a function that prints a proof out.

Coq is useful here because we can construct correct proof trees in "proof mode". In fact, we are just defining particular proof trees, but it is convenient to use "proof mode".

Lastly, we use Coq's dependent types to enforce that it's not just any proof tree that we build, but it is a correct proof tree for the given judgement.
The type :coq:`proofTreeOf` depends on the value, :coq:`j`, of type :coq:`judgement` which constrains what a :coq:`proofTreeOf j` is.
This is similar to a type such as :coq:`vector` depending on a value, :coq:`n`, (the vector's length) of type :coq:`nat` which constrains what a :coq:`vector n` is.

Handling a trust relation and weights are future work (2024).

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


Require Import List.
Import ListNotations.
Require Import String.
Require Import Coq.Strings.Ascii.

(*|
.. coq:: all
|*)

Section VeracityLogic.

Inductive evid :=
  | AtomicEvid (name : string)
  | Pair (e1 e2 : evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2 : evid).

Inductive claim :=
  | AtomicClaim (name : string)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Inductive actor :=
  | Actor (s : string).

Inductive singleJudgement :=
  | SingleJudgement (e : evid) (a : actor) (c: claim).

(*|

Judgements are a list of **single** judgements entailing some single judgement, or state that some claim :coq:`c` is a veracity claim.

|*)

Inductive judgement :=
  | Entail (l : list singleJudgement) (s : singleJudgement)
  | IsAVeracityClaim (c : claim).

(*|
Next, we introduce some notation for Coq.
|*)

Notation "L |- S" := (Entail L S) (at level 3).
Notation "E \by A \in C" := (SingleJudgement E A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Notation "_|_" := (Bottom) (at level 1).
Notation "( x , y , .. , z )" := (Pair .. (Pair x y) .. z).

(*|

We define a tagged type representing a trust relation.

|*)

Inductive trustRelationInfo :=
  | Trust (name : string).

(*|

And we define equality for the tagged type.

|*)

Class Beq A : Type :=
  {
    beq : A -> A -> bool
  }.

Definition beqTrust (t1 t2 : trustRelationInfo) : bool :=
match t1,t2 with
| Trust name1,Trust name2 => String.eqb name1 name2
end.
Instance : Beq trustRelationInfo := { beq := beqTrust }.



(*|

For now, I have only implemented one inference rule, :coq:`and_intro`, as well as the :coq:`assume` rule and a rule :coq:`leaf` that declares that it is correct for a proof tree to stop on a statement such as :math:`C_1 \textit{ is a claim}`.

:coq:`proofTreeOf` is a data type, a tree, which depends on a judgement. The type :coq:`tree j` describes a tree which correctly proves :coq:`j`.

But this is not a proposition. This is best thought of as the datatype for (correct) proof trees.

The remaining rules will be easy to add, this will be done in 2024.

|*)

Inductive proofTreeOf : judgement -> Type :=
| admit p : proofTreeOf p
| leaf c : proofTreeOf (IsAVeracityClaim c)
| assume e a name

       (M : proofTreeOf (IsAVeracityClaim (AtomicClaim name))) 
                         :
  proofTreeOf ([e \by a \in (AtomicClaim name)] |- e \by a \in (AtomicClaim name))
| assume_bot e a

       (M : proofTreeOf (IsAVeracityClaim _|_)) 
                         :
  proofTreeOf ([e \by a \in _|_] |- e \by a \in _|_)

| bot_elim Ps e a C

        (M : proofTreeOf (Ps |- (e \by a \in _|_)))
                           :
           proofTreeOf (Ps |- (e \by a \in C))

| and_intro Ps Qs a e1 e2 C1 C2

(L: proofTreeOf (Ps |- e1 \by a \in C1))
                           (R: proofTreeOf (Qs |- e2 \by a \in C2))
                        :
    proofTreeOf ((Ps ++ Qs) |- (e1, e2) \by a \in (C1 /\' C2))

| and_elim1 Ps a e1 e2 C1 C2

    (M : proofTreeOf Ps |- ((e1, e2) \by a \in (C1 /\' C2)))
                           :
             proofTreeOf (Ps |- (e1 \by a \in C1))

| and_elim2 Ps a e1 e2 C1 C2

    (M : proofTreeOf Ps |- ((e1, e2) \by a \in (C1 /\' C2)))
                          :
        proofTreeOf (Ps |- (e2 \by a \in C2))

| or_intro1 Ps a e1 C1 C2

           (M: proofTreeOf Ps |- (e1 \by a \in C1))
                          :
    proofTreeOf (Ps |- ((Left e1) \by a \in (C1 \/' C2)))

| or_intro2 Ps a e2 C1 C2

           (M: proofTreeOf Ps |- (e2 \by a \in C2))
                          :
    proofTreeOf (Ps |- ((Right e2) \by a \in (C1 \/' C2)))

| or_elim1 Ps a e1 C1 C2

      (M: proofTreeOf (Ps |- ((Left e1) \by a \in (C1 \/' C2))))
                          :
        proofTreeOf (Ps |- (e1 \by a \in C1))

| or_elim2 Ps a e2 C1 C2

      (M : proofTreeOf (Ps |- ((Right e2) \by a \in (C1 \/' C2))))
                            :
          proofTreeOf (Ps |- (e2 \by a \in C2))

| trust Ps a1 a2 e C (name : trustRelationInfo)

(L: proofTreeOf (Ps |- (e \by a2 \in C)))
                          :
            proofTreeOf (Ps |- (e \by a1 \in C))

| impl_intro Ps Qs a e1 e2 C1 C2

(M: proofTreeOf
      ((Ps ++ ((e1 \by a \in C1) :: Qs)) |- (e2 \by a \in C2)))
                              :
proofTreeOf
   ((Ps ++ Qs) |- ((Lambda e1 e2) \by a \in (Implies C1 C2)))
.
(*|
This is the :coq:`and_intro` rule as Coq sees it:
|*)

Check and_intro. (* .unfold *)

(*|

..
  For some reason, math:: directives cause prooftree to crash. The following is an alternative that works.

Here is a *manual* translation of the above rule into Latex.

.. code:: 
  :class: custom-math
   
  \begin{prooftree}
  \AxiomC{$Ps \vdash e_1^a \in C_1 \quad Ps \vdash e_2^a \in C_2$}
  \RightLabel{ $and\_intro$}
  \UnaryInfC{$Ps ++ Qs \vdash (e_1, e_2)^a \in (C_1 \wedge C_2)$}
  \end{prooftree}

|*)

(*|

Example actors, evidence, claims and judgements
-----------------------------------------------

|*)

Open Scope string.

Definition e := AtomicEvid "e".
Definition C := AtomicClaim "C".

Definition a1 := Actor "a_{1}".
Definition e1 := AtomicEvid "e_{1}".
Definition c1 := AtomicClaim "c_{1}".

Definition a2 := Actor "a_{2}".
Definition e2 := AtomicEvid "e_{2}".
Definition c2 := AtomicClaim "c_{2}".

Definition a3 := Actor "a_{3}".
Definition e3 := AtomicEvid "e_{3}".
Definition c3 := AtomicClaim "c_{3}".

Definition a4 := Actor "a_{4}".
(*|
We can also assume arbitrary evidence/claims exist. This currently doesn't work well with printing to Latex. An experimental alternative is demonstrated in the experimental-NamedC-and-NamedE branch.
|*)
Context (e4 : evid).
Context (c4 : claim).

(*|
Example Single judgements:
|*)

Definition sj1 := e1 \by a1 \in c1.
Definition sj3 := e3 \by a3 \in c3.

(*|
Example Judgments:
|*)

Definition j1 := [sj1;sj1;sj3] |- e2 \by a2 \in c2.
Definition j2 := [] |- e4 \by a4 \in c4.

(*|
Example use of notation:
|*)

Check [] |- e1 \by a1 \in c1.
Check e1 \by a1 \in c1.
Check [e1 \by a1 \in c1; e2 \by a2 \in c2] |- e1 \by a1 \in c1.

(*|
Machinery for printing to LaTeX
-------------------------------
|*)

(*| We define and make use of the :coq:`show` typeclass, for simplicity. |*)
Class Show A : Type :=
  {
    show : A -> string
  }.


Open Scope char_scope.

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

Require Import Coq.Numbers.Natural.Peano.NPeano.
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

Instance : Show nat := { show := writeNat }.

Open Scope string_scope.


(*|
For each datatype defined earlier, we define a string representation of it.
|*)

Fixpoint showEvid (e : evid) :=
match e with
  | AtomicEvid name => name
  | Pair e1 e2 => "(" ++ (showEvid e1) ++ ", "
                      ++ (showEvid e2) ++ ")"
  | Left e => "i(" ++ showEvid e ++ ")"
  | Right e => "j(" ++ showEvid e ++ ")"
  | Lambda e1 e2 => "\lambda " ++ showEvid e1 ++ " \rightarrow "
                       ++ showEvid e2
end.
Instance : Show evid := { show := showEvid }.

Fixpoint showClaim (c : claim) :=
match c with
  | AtomicClaim name => name
  | Bottom => "\bot"
  | And c1 c2 => showClaim c1 ++ " \wedge " ++ showClaim c2
  | Or c1 c2 => showClaim c1 ++ " \vee " ++ showClaim c2
  | Implies c1 c2 => showClaim c1 ++ " \rightarrow " ++ showClaim c2
  end.
Instance : Show claim := { show := showClaim }.

Definition showActor (a : actor) := 
  match a with
    | Actor s => s 
  end.
Instance : Show actor := { show := showActor }.

Definition showTrustRelationInfo (t : trustRelationInfo) := 
  match t with
    | Trust name => name
  end.
Instance : Show trustRelationInfo := { show := showTrustRelationInfo }.

Fixpoint showList {A} `{Show A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => show h
    | h1 :: (h2 :: tl) as tl' => show h1 ++ ", " ++ showList tl'
  end.
Instance showListInstance {A : Type} `{Show A} : Show (list A) 
  := { show l := showList l}.

Definition showSingleJudgement (s : singleJudgement) := 
  match s with
    | SingleJudgement e a c => show e ++ "^{" ++ show a ++ "} \in "
                                 ++ show c
  end.
Instance : Show singleJudgement := { show := showSingleJudgement }.

Definition showJudgement (Ts : list trustRelationInfo) (j : judgement) :=
  match j with
  | Entail l s => 
      match l with
        | [] => show s
        | (h :: tl) as l => show l ++ " \vdash_{" ++ show Ts ++ "} " ++ show s
      end
  | IsAVeracityClaim c => show c ++ " \em{ is a veracity claim}"
  end.

Eval compute in showJudgement [] j1.

Fixpoint getAllTrustRelationsUsed (j : judgement) (p : proofTreeOf j)
  : list trustRelationInfo :=
match p with
| admit _ => []
| leaf c => []
| assume e a name M => getAllTrustRelationsUsed _ M
| assume_bot e a M => getAllTrustRelationsUsed _ M
| bot_elim Ps e a C M => getAllTrustRelationsUsed _ M
| and_intro Ps Qs a e1 e2 C1 C2 L R => 
    getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
| and_elim1 Ps a e1 e2 C1 C2 M => getAllTrustRelationsUsed _ M
| and_elim2 Ps a e1 e2 C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro1 Ps a e1 C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 Ps a e2 C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim1 Ps a e1 C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim2 Ps a e2 C1 C2 M => getAllTrustRelationsUsed _ M
| trust Ps a1 a2 e C name L => 
    name :: getAllTrustRelationsUsed _ L
| impl_intro Ps Qs a e1 e2 C1 C2 M => getAllTrustRelationsUsed _ M
end.

Close Scope string.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
match l with
| [] => []
| h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
end.


Lemma removeDupsCorrect : (forall l, NoDup (removeDups l)) /\ forall l a, In a (removeDups l) <-> In a l.
Proof.
Abort.

Fixpoint showProofTreeOf_helper (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
match p with
| admit p => "\AxiomC{?}"
| leaf c => "\AxiomC{$ " 
             ++ show c 
             ++ " \textit{ is a veracity claim} $}"
| assume e a name M => showProofTreeOf_helper _ M
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showJudgement Ts ([e \by a \in (AtomicClaim name)] |- e \by a \in (AtomicClaim name)) ++ " $}"
| assume_bot e a M => showProofTreeOf_helper _ M
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showJudgement Ts ([e \by a \in _|_] |- e \by a \in _|_) ++ " $}"
| bot_elim Ps e a C M => showProofTreeOf_helper _ M
    ++ " \RightLabel{ $ \bot^{-} $} \UnaryInfC{$ "
    ++ showJudgement Ts (Ps |- (e \by a \in C))
    ++ " $}"
| and_intro Ps Qs a e1 e2 C1 C2 L R => 
    showProofTreeOf_helper _ L
 ++ showProofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showJudgement Ts ((Ps ++ Qs) |- (e1, e2) \by a \in (C1 /\' C2)) ++ " $}"
| and_elim1 Ps a e1 e2 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-1} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- (e1 \by a \in C1))
 ++ " $}"
| and_elim2 Ps a e1 e2 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-2} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- (e2 \by a \in C2))
 ++ " $}"
| or_intro1 Ps a e1 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- ((Left e1) \by a \in (C1 \/' C2)))
 ++ " $}"
| or_intro2 Ps a e2 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- ((Right e2) \by a \in (C1 \/' C2)))
 ++ " $}"
| or_elim1 Ps a e1 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-1} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- (e1 \by a \in C1))
 ++ " $}"
| or_elim2 Ps a e2 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-2} $} \UnaryInfC{$ "
 ++ showJudgement Ts (Ps |- (e2 \by a \in C2))
 ++ " $}"
| trust Ps a1 a2 e C name L => 
    showProofTreeOf_helper _ L
 ++ " \AxiomC{$" ++ show a1 ++ show name ++ show a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ show name
 ++ "$} \BinaryInfC{$ "
 ++ showJudgement Ts (Ps |- (e \by a1 \in C)) ++ " $}"
| impl_intro Ps Qs a e1 e2 C1 C2 M => showProofTreeOf_helper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showJudgement Ts ((Ps ++ Qs) |- ((Lambda e1 e2) \by a \in (Implies C1 C2)))
 ++ " $}"
end.

Open Scope string.

Definition showProofTreeOf j p
  := "\begin{prooftree}" ++ showProofTreeOf_helper j p
       ++ "\end{prooftree}".
Instance showProofTreeOfInstance (j : judgement)
  : Show (proofTreeOf j) := { show := showProofTreeOf j}.

(*|

An example from the paper
-------------------------

This example is the top half of the proof tree on p13 (Section 4.2) of the draft paper.

The proof trees visualised in this section are **automatically generated** by Coq.

|*)

Definition l := AtomicEvid "l".
Definition s := AtomicEvid "s".
Definition c := AtomicEvid "c".
Definition P := Actor "P".
Definition Q := Actor "Q".
Definition C1 := AtomicClaim "C_1".
Definition C2 := AtomicClaim "C_2".
Definition C3 := AtomicClaim "C_3".
Definition C4 := AtomicClaim "C_4".
Definition C5 := AtomicClaim "C_5".

Definition concreteProofTreeExampleWith2Conjuncts : 
proofTreeOf [l \by P \in C1; s \by P \in C2]
              |- (l, s) \by P \in (C1 /\' C2).
epose proof (and_intro [l \by P \in C1]
                       [s \by P \in C2]) _ _ _ C1 C2.
simpl in H.
apply H.
apply assume.
apply leaf.
apply assume.
apply leaf.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (show concreteProofTreeExampleWith2Conjuncts).

(*|
.. coq::
|*)

Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf [l \by P \in C1; s \by P \in C2; c \by P \in C3]
              |- ((l, s),c) \by P \in (C1 /\' C2 /\' C3).
epose proof (and_intro [l \by P \in C1; s \by P \in C2]
                       [c \by P \in C3]) P (l, s) c (C1 /\' C2) C3.
simpl in H.
apply H.
epose proof (and_intro [l \by P \in C1]
                       [s \by P \in C2]) _ _ _ C1 C2.
simpl in H0.
apply H0.
all: apply assume; apply leaf.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (show concreteProofTreeExampleWith3Conjuncts).

(*|
.. coq::
|*)

(*|
We can also combine existing trees into new trees, when appropriate. For example:
|*)

Definition concreteProofTreeExampleWith3ConjunctsUsingExistingTree : 
proofTreeOf [l \by P \in C1; s \by P \in C2; c \by P \in C3]
              |- ((l, s),c) \by P \in (C1 /\' C2 /\' C3).
epose proof (and_intro
              [l \by P \in C1; s \by P \in C2]
              [c \by P \in C3]) P (l, s) c (C1 /\' C2) C3.
simpl in H.
apply H.
exact concreteProofTreeExampleWith2Conjuncts.
apply assume; apply leaf.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (show concreteProofTreeExampleWith3Conjuncts).

(*|
.. coq::
|*)

Definition concreteProofTreeExampleTrust : 
proofTreeOf [e \by a2 \in C]
              |- e \by a1 \in (C).
apply (trust [e \by a2 \in C] a1 a2 e C (Trust "T")).
apply assume.
apply leaf.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (show concreteProofTreeExampleTrust).

(*|
.. coq::
|*)


Definition concreteProofTreeExampleWith3ConjunctsWithTrust : 
proofTreeOf [l \by P \in C1; s \by P \in C2; c \by P \in C3]
              |- ((l, s),c) \by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ _ _ _ _ (Trust "U")).
apply concreteProofTreeExampleWith3ConjunctsUsingExistingTree.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (show concreteProofTreeExampleWith3ConjunctsWithTrust). 

(*|
.. coq::
|*)


Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
proofTreeOf [l \by P \in C1; s \by P \in C2; c \by P \in C3]
              |- ((l, s),c) \by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ Q Q _ _ (Trust "U")).
eapply (trust _ Q Q _ _ (Trust "V")).
eapply (trust _ _ _ _ _ (Trust "U")).
apply concreteProofTreeExampleWith3ConjunctsUsingExistingTree.
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in (show concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras). 

(*|
.. coq::
|*)


Record proofTreeOfClaim (c : claim) := {
  _l : list singleJudgement;
  _e : evid;
  _a : actor;
  _p : proofTreeOf _l |- (_e \by _a \in c)
}.
Instance showProofTreeOfClaim (c : claim) : Show (proofTreeOfClaim c) := { show p := show (_p c p) }.

Definition exampleWithProofOf : proofTreeOfClaim C1.
Proof.
eexists _ _ _.
apply (assume e1 a1).
apply leaf.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in show exampleWithProofOf.


(*|
.. coq::
|*)

Definition usingAll : proofTreeOfClaim (Implies _|_ C1).
Proof.
eexists _ _ _.
eapply or_elim1.
eapply or_intro1.
eapply or_elim2.
eapply or_intro2.
eapply and_elim1.
eapply and_intro.
eapply and_elim2.
eapply and_intro.
apply assume; apply leaf.
2: apply assume; apply leaf.
eapply (trust _ _ _ _ _ (Trust "T")).
eapply (impl_intro []).
simpl.
eapply bot_elim.
apply assume_bot.
apply (admit _).
Unshelve.
1,8: apply a1.
1,2: apply C2.
1,2,5: apply e2.
1,2: apply "C_2".
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in show usingAll.

(*|
.. coq::
|*)

Ltac proveClaim := 
(* unshelve eexists _ _ _; *)
(repeat ( 
idtac
(* + unshelve eapply or_elim1 *)
(* + unshelve eapply admit *)
+ unshelve eapply or_intro1
(* + unshelve eapply or_elim2 *)
+ unshelve eapply or_intro2
(* + unshelve eapply and_elim1 *)
+ unshelve eapply and_intro
(* + unshelve eapply and_elim2 *)
+ unshelve eapply and_intro; simpl
+ unshelve apply assume
+ unshelve apply assume_bot
+ unshelve apply leaf
(* + unshelve eapply (trust _ _ _ _ _ (Trust "T")) *)
+ unshelve eapply (impl_intro [])
+ simpl
+ unshelve eapply bot_elim));
repeat (apply a1
+ apply C2
+ apply e2
+ apply [])
.

Definition eQ := AtomicEvid "e_{?}".
Definition CQ := AtomicClaim "C_{?}".
Definition aQ := Actor "a_{?}".

Ltac maybePrintMessage1 s := idtac s.
Ltac maybePrintMessage2 s := idtac s.
(* Ltac2 Type exn ::= [ VeracityProofSearchException(string) ]. *)

Ltac tryLeaf :=
maybePrintMessage1 "Trying leaf";
match goal with
   | [ |- proofTreeOf (IsAVeracityClaim _) ] => (maybePrintMessage2 "Applying leaf"); (eapply leaf)
   | [ |- _ ] => fail
end.

Ltac tryAssumeWitha1 :=
(maybePrintMessage1 "Trying assume");
match goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying assume"); eapply (assume _ a1)
   | [ |- _ ] => fail
end.

Ltac tryAndIntro :=
(maybePrintMessage1 "Trying and_intro");
match goal with
   | [ |- (proofTreeOf _ |- _ \by _ \in (_ /\' _)) ] => (maybePrintMessage2 "Applying and_intro"); eapply and_intro
   | [ |- _ ] => fail
end.

Ltac tryTrust :=
(maybePrintMessage1 "Trying trust");
match goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying trust"); (eapply (trust _ _ _ _ _ _))
   | [ |- _ ] => fail
end.

Ltac fillConstant :=
solve [ apply CQ | apply aQ | apply eQ | apply ([] : list singleJudgement) | apply (Trust "?") ].

Ltac tryEach :=
   (progress tryTrust)
+  (progress tryAndIntro)
+  (progress tryAssumeWitha1)
+  (progress tryLeaf)
+  (progress fillConstant).

Ltac autoProveWithDepthLimit x :=
solve [do x (tryEach)].

(* Ltac2 rec autoProveProgressiveSearch start_depth max_depth :=
match Int.gt start_depth max_depth with
  | true => Message.print (Message.of_int start_depth); Message.print (Message.of_int max_depth); Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [autoProveWithDepthLimit start_depth | autoProveProgressiveSearch (Int.add start_depth 1) max_depth]
end. *)

(* Ltac autoProve max_depth := autoProveWithDepthLimit max_depth. *)

(*|
The following demonstrates a constraing that the claim must be believed by actor 2, and we have constrained only assuming claims for actor 1 in the tactic.
|*)



Definition exampleC1 : proofTreeOfClaim (C2).
Proof.
eexists _ _ _.
solve [do 3 (tryEach)].
Unshelve.
all: fillConstant.
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show exampleC1.

(*|
.. coq::
|*)

(*|
The following demonstrates automatically proving a larger claim.
|*)
(*  *)

Definition automatedProof : proofTreeOfClaim (C1 /\' C2 /\' C2 /\' C2 /\' C2).
Proof.
eexists _ _ _.
Time solve [do 6 (tryEach)]. (* Finished transaction in 13.672 secs (13.114u,0.232s) (successful) *)
(* Time autoProve 4. Finished transaction in 0.009 secs (0.009u,0.s) (successful) *)
(* Time autoProve ().  Finished transaction in 1.503 secs (1.475u,0.s) (successful) *)
Unshelve.
all: fillConstant.
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show automatedProof.

(*|
.. coq::
|*)


