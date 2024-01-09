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
Open Scope string.

(*|
.. coq:: all
|*)

Section VeracityLogic.

Inductive evid :=
  | AtomicEvid (name : string)
  | Pair (e1 e2 : evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2 : evid)
  | NamedE (name : string) (e1 : evid).

Inductive claim :=
  | AtomicClaim (name : string)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim)
  | NamedC (name : string) (c1 : claim).

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

For now, I have only implemented one inference rule, :coq:`and_intro`, as well as the :coq:`assume` rule and a rule :coq:`leaf` that declares that it is correct for a proof tree to stop on a statement such as :math:`C_1 \textit{ is a claim}`.

:coq:`proofTreeOf` is a data type, a tree, which depends on a judgement. The type :coq:`tree j` describes a tree which correctly proves :coq:`j`.

But this is not a proposition. This is best thought of as the datatype for (correct) proof trees.

The remaining rules will be easy to add, this will be done in 2024.

|*)

Inductive proofTreeOf : judgement -> Type :=
| leaf c : proofTreeOf (IsAVeracityClaim c)
| assume e a c

       (M : proofTreeOf (IsAVeracityClaim c)) 
                         :
  proofTreeOf ([e \by a \in c] |- e \by a \in c)

| and_intro Ps Qs a e1 e2 C1 C2

(L: proofTreeOf (Ps |- e1 \by a \in C1))
                           (R: proofTreeOf (Qs |- e2 \by a \in C2))
                       :
    proofTreeOf ((Ps ++ Qs) |- (e1, e2) \by a \in (C1 /\' C2)).

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
We can also assume arbitrary evidence/claims exist.
|*)
Context (e4' : evid).
Context (c4' : claim).
Definition e4 := NamedE "e_{4}" e4'.
Definition c4 := NamedC "c_{4}" c4'.

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

(*|
For each datatype defined earlier, we define a string representation of it.
|*)

Fixpoint showEvid (e : evid) :=
match e with
  | AtomicEvid name => name
  | Pair e1 e2 => "(" ++ (showEvid e1) ++ ", "
                      ++ (showEvid e2) ++ ")"
  | Left e => "i(" ++ showEvid e ++ ")"
  | Right e => "l(" ++ showEvid e ++ ")"
  | Lambda e1 e2 => "\lambda " ++ showEvid e1 ++ " \rightarrow "
                       ++ showEvid e2
  | NamedE name e => name
end.
Instance : Show evid := { show := showEvid }.

Fixpoint showClaim (c : claim) :=
match c with
  | AtomicClaim name => name
  | Bottom => "\bot"
  | And c1 c2 => showClaim c1 ++ " \wedge " ++ showClaim c2
  | Or c1 c2 => showClaim c1 ++ " \vee " ++ showClaim c2
  | Implies c1 c2 => showClaim c1 ++ " \rightarrow " ++ showClaim c2
  | NamedC name c1 => name
  end.
Instance : Show claim := { show := showClaim }.

Definition showActor (a : actor) := 
  match a with
    | Actor s => s 
  end.
Instance : Show actor := { show := showActor }.

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

Definition showJudgement (j : judgement) :=
  match j with
  | Entail l s => 
      match l with
        | [] => show s
        | (h :: tl) as l => show l ++ " \vdash " ++ show s
      end
  | IsAVeracityClaim c => show c ++ " \em{ is a veracity claim}"
  end.
Instance : Show judgement := { show := showJudgement }.

Eval compute in show j1.

Fixpoint showProofTreeOf_helper (j : judgement) (p : proofTreeOf j)
  : string :=
match p with
| leaf c => "\AxiomC{$ " 
             ++ show c 
             ++ " \textit{ is a veracity claim} $}"
| assume e a c M => showProofTreeOf_helper (IsAVeracityClaim c) M
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ show ([e \by a \in c] |- e \by a \in c) ++ " $}"
| and_intro Ps Qs a e1 e2 C1 C2 L R => 
    showProofTreeOf_helper (Ps |- e1 \by a \in C1) L
 ++ showProofTreeOf_helper (Qs |- e2 \by a \in C2) R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ show ((Ps ++ Qs) |- (e1, e2) \by a \in (C1 /\' C2)) ++ " $}"
end.

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
Definition C1 := AtomicClaim "C_1".
Definition C2 := AtomicClaim "C_2".
Definition C3 := AtomicClaim "C_3".

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