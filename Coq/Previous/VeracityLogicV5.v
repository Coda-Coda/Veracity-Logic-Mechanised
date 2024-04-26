(*|
Veracity Logic Mechanised in Coq V5
===================================

**Note: the commentary is out of date.**

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
Require Import Bool.
Require Import Program.

(*|
.. coq:: all
|*)

Section VeracityLogic.

Inductive atomic_evid_name :=
  | _e_
  | _e1_
  | _e2_
  | _e3_
  | _e4_
  | _eB_
  | _eQ_
  | _l_
  | _s_
  | _c_evid_
  | _belief_
  | _testing_
  | _audit_
  | _compile_
  | _review_
  | _assess_
  | _ingredients_percentage_list_
  | _breakdown_of_formulations_list_
.

Scheme Equality for atomic_evid_name.

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
  | _applicant_
  | _certifier_
.

Scheme Equality for actor_name.

Inductive claim_name :=
  | _c_
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
  | _recipe_valid_
  | _percentage_ingredients_valid_
  | _breakdown_of_formulations_valid_
  | _successful_market_compliance_assessment_
. 

Scheme Equality for claim_name.

Inductive trust_relation_name :=
  | _T_
  | _U_
  | _V_
.

Scheme Equality for trust_relation_name.

Open Scope string.

Class ShowForProofTree A : Type :=
  {
    showForProofTree : A -> string
  }.

Instance : ShowForProofTree atomic_evid_name := { 
  showForProofTree n := 
    match n with
      | _e_ => "e"
      | _e1_ => "e_{1}"
      | _e2_ => "e_{2}"
      | _e3_ => "e_{3}"
      | _e4_ => "e_{4}"
      | _eB_  => "e_{\bot}"
      | _eQ_ => "e_{?}"
      | _l_ => "l"
      | _s_ => "s"
      | _c_evid_ => "c"
      | _belief_ => "b"
      | _testing_ => "t"
      | _audit_ => "a"
      | _compile_=> "c"
      | _review_=> "r"
      | _assess_ => "a"
      | _ingredients_percentage_list_ => "e_{PI}"
      | _breakdown_of_formulations_list_=> "e_{BF}"
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
      | _applicant_ => "A"
      | _certifier_ => "C"
    end
  }.

Instance : ShowForProofTree claim_name := { 
  showForProofTree n := 
    match n with
      | _c_ => "C"
      | _c1_ => "C_{1}"
      | _c2_ => "C_{2}"
      | _c3_ => "C_{3}"
      | _c4_ => "C_{4}"
      | _c5_ => "C_{5}"
      | _cQ_ => "C_{?}"
      | _healthy_ => "H"
      | _nonToxic_ => "N"
      | _organic_ => "O"
      | _ingredients_valid_ => "IV"
      | _recipe_valid_ => "RV"      
      | _percentage_ingredients_valid_ => "PIV"
      | _breakdown_of_formulations_valid_ => "BFV"
      | _successful_market_compliance_assessment_ => "SMCA"
    end
  }.

Instance : ShowForProofTree trust_relation_name := { 
  showForProofTree n := 
    match n with
      | _T_ => "T"
      | _U_ => "U"
      | _V_ => "V"
    end
  }.

Class ShowForNaturalLanguage A : Type :=
  {
    showForNaturalLanguage : A -> string
  }.
Class ShowForLogSeq A : Type :=
  {
    showForLogSeq : A -> string
  }.

Instance : ShowForNaturalLanguage atomic_evid_name := { 
  showForNaturalLanguage n := 
    match n with
      | _e_ => "atomic evidence e"
      | _e1_ => "atomic evidence 1"
      | _e2_ => "atomic evidence 2"
      | _e3_ => "atomic evidence 3"
      | _e4_ => "atomic evidence 4"
      | _eB_ =>  "evidence for bottom"
      | _eQ_ =>  "unknown evidence"
      | _l_ => "atomic evidence l"
      | _s_ => "atomic evidence s"
      | _c_evid_ => "atomic evidence c"
      | _belief_ => "belief"
      | _testing_ => "testing"
      | _audit_ => "audit"
      | _compile_=> "compile"
      | _review_=> "review"
      | _assess_ => "assess"
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
      | _Q_ => "Quintin"
      | _applicant_ => "applicant"
      | _certifier_ => "certifier"
    end
  }.
Instance : ShowForLogSeq actor_name := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForNaturalLanguage claim_name := { 
  showForNaturalLanguage n := 
    match n with
      | _c_ => "claim c"
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
      | _T_ => "trust relation T"
      | _U_ => "trust relation U"
      | _V_ => "trust relation V"
    end
  }.
Instance : ShowForLogSeq trust_relation_name := {showForLogSeq := showForNaturalLanguage}.


Inductive evid :=
  | HoleEvid
  | AtomicEvid (n : atomic_evid_name)
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2: evid)
  | Apply (e1 e2: evid).

Scheme Equality for evid.

Inductive claim :=
  | AtomicClaim (n : claim_name)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Scheme Equality for claim.

Inductive actor :=
  | Actor (n : actor_name).

Scheme Equality for actor.

Inductive judgementPart :=
  | JudgementPart (a : actor) (c: claim).

Scheme Equality for judgementPart.





(*|

Judgements are a list of **single** judgements entailing some single judgement, or state that some claim :coq:`c` is a veracity claim.

|*)

(*|
Next, we introduce some notation for Coq.
|*)

Notation "\by A \in C" := (JudgementPart A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Notation "_|_" := (Bottom) (at level 1).
Notation "{{ x , y , .. , z }}" := (Pair .. (Pair x y) .. z).

(*|

We define a tagged type representing a trust relation.

|*)

Inductive trustRelation :=
  | Trust (n : trust_relation_name).

Scheme Equality for trustRelation.

Inductive judgement :=
  Judgement (e : evid) (jp : judgementPart).

Scheme Equality for judgement.

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
Instance : Beq judgementPart := { beq := judgementPart_beq }.
Instance : Beq trustRelation := { beq := trustRelation_beq }.
Instance : Beq judgement := { beq := judgement_beq }.

(*|

For now, I have only implemented one inference rule, :coq:`and_intro`, as well as the :coq:`assume` rule and a rule :coq:`leaf` that declares that it is correct for a proof tree to stop on a statement such as :math:`C_1 \textit{ is a claim}`.

:coq:`proofTreeOf` is a data type, a tree, which depends on a judgement. The type :coq:`tree j` describes a tree which correctly proves :coq:`j`.

But this is not a proposition. This is best thought of as the datatype for (correct) proof trees.

The remaining rules will be easy to add, this will be done in 2024.

|*)

Inductive proofTreeOf : judgementPart -> Type :=
| hole j : proofTreeOf j
| assume (e : evid) a (c : claim) : proofTreeOf (\by a \in c)
| bot_elim a C

        (M : proofTreeOf (\by a \in _|_))
                           :
           proofTreeOf ((\by a \in C))

| and_intro a C1 C2

(L: proofTreeOf (\by a \in C1))
                           (R: proofTreeOf (\by a \in C2))
                        :
    proofTreeOf (\by a \in (C1 /\' C2))

| and_elim1 a C1 C2

    (M : proofTreeOf (\by a \in (C1 /\' C2)))
                           :
             proofTreeOf (\by a \in C1)

| and_elim2 a C1 C2

    (M : proofTreeOf (\by a \in (C1 /\' C2)))
                          :
        proofTreeOf (\by a \in C2)

| or_intro1 a C1 C2

           (M: proofTreeOf (\by a \in C1))
                          :
    proofTreeOf (\by a \in (C1 \/' C2))

| or_intro2 a C1 C2

           (M: proofTreeOf (\by a \in C2))
                          :
    proofTreeOf (\by a \in (C1 \/' C2))

| or_elim1 a C1 C2

      (M: proofTreeOf (\by a \in (C1 \/' C2)))
                          :
        proofTreeOf (\by a \in C1)

| or_elim2 a C1 C2

      (M : proofTreeOf (\by a \in (C1 \/' C2)))
                            :
          proofTreeOf (\by a \in C2)

| trust a1 a2 C (name : trustRelation)

(L: proofTreeOf (\by a2 \in C))
                          :
            proofTreeOf (\by a1 \in C)

| impl_intro (e1 : evid) (C1 : claim) a C2

         (M: proofTreeOf (\by a \in C2))
                              :
   proofTreeOf (\by a \in (Implies C1 C2))

| impl_elim a C1 C2

(L: proofTreeOf (\by a \in (Implies C1 C2)))
                           (R: proofTreeOf (\by a \in C1))
                        :
    proofTreeOf (\by a \in C2)
.
(*|
This is the :coq:`and_intro` rule as Coq sees it:
|*)

Check and_intro. (* .unfold *)

Fixpoint computeEvidence (j : judgementPart) (p : proofTreeOf j) : evid := 
match p with
| hole _ => HoleEvid
| assume e a c => e
| bot_elim a C M => computeEvidence _ M
| and_intro a C1 C2 L R => {{computeEvidence _ L,computeEvidence _ R}}
| and_elim1 a C1 C2 M => match computeEvidence _ M with
                          | {{e1,e2}} => e1
                          | e => e
                          end
| and_elim2 a C1 C2 M => match computeEvidence _ M with
                          | {{e1,e2}} => e2
                          | e => e
                          end
| or_intro1 a C1 C2 M => Left (computeEvidence _ M)
| or_intro2 a C1 C2 M => Right (computeEvidence _ M)
| or_elim1 a C1 C2 M => match computeEvidence _ M with
                          | (Left e1) => e1
                          | e => e
                          end
| or_elim2 a C1 C2 M => match computeEvidence _ M with
                          | (Right e2) => e2
                          | e => e
                          end
| trust a1 a2 C name L => computeEvidence _ L
| impl_intro e1 C1 a C2 M => Lambda e1 (computeEvidence _ M)
| impl_elim a C1 C2 L R => Apply (computeEvidence _ L) (computeEvidence _ R)
end.

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

Definition e := AtomicEvid _e_.
Definition C := AtomicClaim _c_.

Definition a1 := Actor _a1_.
Definition e1 := AtomicEvid _e1_.
Definition c1 := AtomicClaim _c1_.

Definition a2 := Actor  _a2_.
Definition e2 := AtomicEvid _e2_.
Definition c2 := AtomicClaim _c2_.

Definition a3 := Actor _a3_.
Definition e3 := AtomicEvid _e3_.
Definition c3 := AtomicClaim _c3_.

Definition a4 := Actor _a4_ .
Definition e4 := AtomicEvid  _e4_.
Definition c4 := AtomicClaim _c4_.

(*|
We can also assume arbitrary evidence/claims exist. This currently doesn't work well with printing to Latex. An experimental alternative is demonstrated in the experimental-NamedC-and-NamedE branch.
|*)
Context (e4 : evid).
Context (c4 : claim).

(*|
Example Single judgements:
|*)

Definition sj1 := \by a1 \in c1.
Definition sj3 := \by a3 \in c3.

(*|
Example Judgments:
|*)

Definition j1 :=\by a2 \in c2.
Definition j2 :=\by a4 \in c4.

(*|
Example use of notation:
|*)

Check\by a1 \in c1.
Check \by a1 \in c1.
Check\by a1 \in c1.

(*|
For each datatype defined earlier, we define a string representation of it.
|*)

Instance : ShowForProofTree evid := {
  showForProofTree :=
  fix showForProofTreeEvid e :=
      match e with
      | AtomicEvid name => showForProofTree name
      | HoleEvid => "\textcolor{red}{e_{?}}"
      | Pair e1 e2 => "(" ++ (showForProofTreeEvid e1) ++ ", "
                          ++ (showForProofTreeEvid e2) ++ ")"
      | Left e => "i(" ++ showForProofTreeEvid e ++ ")"
      | Right e => "j(" ++ showForProofTreeEvid e ++ ")"
      | Lambda e1 e2 => "\lambda (" ++ showForProofTreeEvid e1 ++ ")("
                          ++ showForProofTreeEvid e2 ++ ")"
      | Apply e1 e2 => showForProofTreeEvid e1 ++ "(" ++ showForProofTreeEvid e2 ++ ")"
    end
}.
Instance : ShowForNaturalLanguage evid := { showForNaturalLanguage := showForProofTree }.
Instance : ShowForLogSeq evid := {showForLogSeq := showForNaturalLanguage}.

Instance : ShowForProofTree claim := {
  showForProofTree :=
  fix showForProofTreeClaim c :=
    match c with
      | AtomicClaim name => showForProofTree name
      | Bottom => "\bot"
      | And c1 c2 => showForProofTreeClaim c1 ++ " \wedge " ++ showForProofTreeClaim c2
      | Or c1 c2 => showForProofTreeClaim c1 ++ " \vee " ++ showForProofTreeClaim c2
      | Implies c1 c2 => showForProofTreeClaim c1 ++ " \rightarrow " ++ showForProofTreeClaim c2
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
(* Instance showForLogSeq_list_instance (A : Type) `(ShowForLogSeq A) (indent : string) : ShowForLogSeq (list A) := {
    showForLogSeq l := showForLogSeq_list indent l
  }. *)

Instance : ShowForProofTree judgement := {
  showForProofTree j :=
  match j with
  | Judgement e jp =>
    match jp with
      | JudgementPart a c => showForProofTree e ++ "^{" ++ showForProofTree a ++ "} \in "
                                  ++ showForProofTree c
    end  
  end
}.

Instance : ShowForNaturalLanguage judgement := {
  showForNaturalLanguage j :=
  match j with
  | Judgement e jp =>
    match jp with
      | JudgementPart a c => showForNaturalLanguage c ++ " is supported by $" ++ showForNaturalLanguage e ++ "$ which " ++ showForNaturalLanguage a ++ " uses"
    end  
  end
}.

Instance : ShowForLogSeq judgement := {
  showForLogSeq j :=
  match j with
  | Judgement e jp =>
    match jp with
      | JudgementPart a c => showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence $" ++ showForLogSeq e ++ "$"
    end  
  end
}.

Definition showForProofTree_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgementPart) (p : proofTreeOf j) :=
let computedEvidence := computeEvidence j p in
    match Ps with
      | [] => showForProofTree (Judgement computedEvidence j)
      | (h :: tl) as Ps => showForProofTree Ps ++ " \vdash_{" ++ showForProofTree Ts ++ "} " ++ (showForProofTree (Judgement computedEvidence j))
    end.

Eval compute in showForProofTree_judgement [] [] j1 (hole j1).

Eval compute in showForProofTree_judgement [Judgement e (\by a1 \in c1)] [] (\by a1 \in c1) (assume e a1 c1).

Definition showForNaturalLanguage_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgementPart) (p : proofTreeOf j) :=
  let computedEvidence := computeEvidence j p in
    match Ps with
      | [] => showForNaturalLanguage (Judgement computedEvidence j)
      | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage (Judgement computedEvidence j)
    end.

(* Definition showForLogSeq_judgement (Ps : list judgement) (Ts : list trustRelation) (indent : string) (j : judgementPart) (p : proofTreeOf j) :=
  let computedEvidence := computeEvidence j p in  
  match Ps,Ts with
        | [],[] => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "- " ++ "Assumptions made: None" ++ "
" ++ indent ++ "- " ++ "Trust relations used: None"
        | (h :: tl),[] => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "- " ++ "Assumptions made:" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used: None"
        | [],(h :: tl) => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "- " ++ "Assumptions made: None" ++ "
" ++ indent ++ "- " ++ "Trust relations used:" ++ showForLogSeq_list ("  " ++ indent) Ts
        | (h :: tl),(h2::tl2) => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "- " ++ "Assumptions made:" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used:" ++ showForLogSeq_list ("  " ++ indent) Ts
      end. *)


Definition showForLogSeq_judgement (Ps : list judgement) (Ts : list trustRelation) (indent : string) (j : judgementPart) (p : proofTreeOf j) :=
  let computedEvidence := computeEvidence j p in        
    match Ps,Ts with
        | [],[] => showForLogSeq (Judgement computedEvidence j)
        | (h :: tl),[] => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Assumptions made:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ps
        | [],(h :: tl) => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Trust relations used:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ts
        | (h :: tl),(h2::tl2) => showForLogSeq (Judgement computedEvidence j) ++ "
" ++ indent ++ "collapsed:: true
" ++ indent ++ "- " ++ "Assumptions made:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used:
" ++ indent ++ "  collapsed:: true
" ++ showForLogSeq_list ("  " ++ indent) Ts
      end.

Fixpoint getAllTrustRelationsUsed (j : judgementPart) (p : proofTreeOf j)
  : list trustRelation :=
match p with
| hole _ => []
| assume e a C => []
| bot_elim a C M => getAllTrustRelationsUsed _ M
| and_intro a C1 C2 L R => 
    getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
| and_elim1 a C1 C2 M => getAllTrustRelationsUsed _ M
| and_elim2 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro1 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim1 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim2 a C1 C2 M => getAllTrustRelationsUsed _ M
| trust a1 a2 C name L => 
    name :: getAllTrustRelationsUsed _ L
| impl_intro e1 C1 a C2 M => getAllTrustRelationsUsed _ M
| impl_elim a C1 C2 L R => 
   getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
end.

Fixpoint getAllEvidence (j : judgementPart) (p : proofTreeOf j)
  : list evid :=
match p with
| hole _ => [HoleEvid]
| assume e a C => [e]
| bot_elim a C M => e :: (getAllEvidence _ M)
| and_intro a C1 C2 L R => 
    e1 :: e2 :: getAllEvidence _ L ++ getAllEvidence _ R 
| and_elim1 a C1 C2 M => e1 :: e2 :: getAllEvidence _ M
| and_elim2 a C1 C2 M => e1 :: e2 :: getAllEvidence _ M
| or_intro1 a C1 C2 M => e1 :: getAllEvidence _ M
| or_intro2 a C1 C2 M => e2 :: getAllEvidence _ M
| or_elim1 a C1 C2 M => e1 :: getAllEvidence _ M
| or_elim2 a C1 C2 M => e2 :: getAllEvidence _ M
| trust a1 a2 C name L => e ::  getAllEvidence _ L
| impl_intro e1 C1 a C2 M => e1 :: e2 :: getAllEvidence _ M
| impl_elim a C1 C2 L R => 
   e1 :: e2 :: getAllEvidence _ L ++ getAllEvidence _ R 
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Fixpoint getAssumptions (j : judgementPart) (p : proofTreeOf j) : list judgementPart := 
match p with
| hole _ => []
| assume e a C => [\by a \in C]
| bot_elim a C M => getAssumptions _ M
| and_intro a C1 C2 L R => 
    getAssumptions _ L ++ getAssumptions _ R 
| and_elim1 a C1 C2 M => getAssumptions _ M
| and_elim2 a C1 C2 M => getAssumptions _ M
| or_intro1 a C1 C2 M => getAssumptions _ M
| or_intro2 a C1 C2 M => getAssumptions _ M
| or_elim1 a C1 C2 M => getAssumptions _ M
| or_elim2 a C1 C2 M => getAssumptions _ M
| trust a1 a2 C name L => 
    getAssumptions _ L
| impl_intro e1 C1 a C2 M => filter (judgementPart_beq (\by a \in C1)) (getAssumptions _ M)
| impl_elim a C1 C2 L R => 
   getAssumptions _ L ++ getAssumptions _ R 
end.

Fixpoint getAssumptionsWithEvidence (j : judgementPart) (p : proofTreeOf j) : list (judgement) := 
match p with
| hole j => [(Judgement HoleEvid j)]
| assume e a C => [Judgement e (\by a \in C)]
| bot_elim a C M => getAssumptionsWithEvidence _ M
| and_intro a C1 C2 L R => 
    getAssumptionsWithEvidence _ L ++ getAssumptionsWithEvidence _ R 
| and_elim1 a C1 C2 M => getAssumptionsWithEvidence _ M
| and_elim2 a C1 C2 M => getAssumptionsWithEvidence _ M
| or_intro1 a C1 C2 M => getAssumptionsWithEvidence _ M
| or_intro2 a C1 C2 M => getAssumptionsWithEvidence _ M
| or_elim1 a C1 C2 M => getAssumptionsWithEvidence _ M
| or_elim2 a C1 C2 M => getAssumptionsWithEvidence _ M
| trust a1 a2 C name L => 
    getAssumptionsWithEvidence _ L
| impl_intro e1 C1 a C2 M => filter (judgement_beq (Judgement e1 (\by a \in C1))) (getAssumptionsWithEvidence _ M)
| impl_elim a C1 C2 L R => 
   getAssumptionsWithEvidence _ L ++ getAssumptionsWithEvidence _ R 
end.

Close Scope string.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
match l with
| [] => []
| h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
end.

Open Scope beq_scope.

Fixpoint proofTreeOf_beq {j1 j2 : judgementPart} (P1 : proofTreeOf j1) (P2 : proofTreeOf j2) : bool :=
match P1,P2 with
| hole j1,hole j2 => j1 =? j2
| assume e a1 C1, assume e2 a2 C2 => (e =? e2) && (a1 =? a2) && (C1 =? C2)
| bot_elim a1 C1 M1, bot_elim a2 C2 M2 => (a1 =? a2) && (C1 =? C2) && proofTreeOf_beq M1 M2
| and_intro a C1 C2 L R, and_intro a' C1' C2' L' R' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq L L' && proofTreeOf_beq R R'
| and_elim1 a C1 C2 M, and_elim1 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| and_elim2 a C1 C2 M, and_elim2 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_intro1 a C1 C2 M, or_intro1 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_intro2 a C1 C2 M, or_intro2 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_elim1 a C1 C2 M, or_elim1 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_elim2 a C1 C2 M, or_elim2 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| trust a1 a2 C T L, trust a1' a2' C' T' L' => (a1 =? a1') && (a2 =? a2') && (C =? C') && (T =? T') && proofTreeOf_beq L L'
| impl_intro e C1 a C2 M, impl_intro e' C1' a' C2' M' => (e =? e') && (C1 =? C1') && (a =? a') && (C2 =? C2') && proofTreeOf_beq M M'
| impl_elim a C1 C2 L R, impl_elim a' C1' C2' L' R' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq L L' && proofTreeOf_beq R R'
| _,_ => false
end.

Instance beq_proofTreeOf_instance (j : judgementPart) : Beq (proofTreeOf j) := { beq := proofTreeOf_beq }.

Close Scope beq_scope.

Open Scope string.

Fixpoint showForProofTree_proofTreeOf_helper (j : judgementPart) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptionsWithEvidence j p)) in
match p with
| hole j => "\AxiomC{$\textcolor{red}{" ++ (showForProofTree (Judgement HoleEvid j)) ++ "}$}"
| assume e a C => "\AxiomC{$ " 
             ++ showForProofTree C 
             ++ " \textit{ is a veracity claim} $}"
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| bot_elim a C M => showForProofTree_proofTreeOf_helper _ M
    ++ " \RightLabel{ $ \bot^{-} $} \UnaryInfC{$ "
    ++ showForProofTree_judgement Ps Ts _ p
    ++ " $}"
| and_intro a C1 C2 L R => 
    showForProofTree_proofTreeOf_helper _ L
 ++ showForProofTree_proofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| and_elim1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| and_elim2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_elim1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_elim2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| trust a1 a2 C name L => 
    showForProofTree_proofTreeOf_helper _ L
 ++ " \AxiomC{$" ++ showForProofTree a1 ++ showForProofTree name ++ showForProofTree a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ showForProofTree name
 ++ "$} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| impl_intro e1 C1 a C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| impl_elim a C1 C2 L R => 
     showForProofTree_proofTreeOf_helper _ L
 ++ showForProofTree_proofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \rightarrow^{-} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
end.

Fixpoint showForNaturalLanguage_proofTreeOf_helper (indent : string) (j : judgementPart) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptionsWithEvidence j p)) in
match p with
| hole p => indent ++ "we stopped the proof at this point and assumed it was provable."
| assume e a C => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ indent ++ showForNaturalLanguage C ++ " is a veracity claim." ++ "
"
++ indent ++ "by assumption."
| bot_elim a C M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by the logical principle of explosion."
| and_intro a C1 C2 L R => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim1 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim2 a C1 C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| or_intro1 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_intro2 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim1 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim2 a C1 C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| trust a1 a2 C name L => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ indent ++ "by the trust relation " ++ showForNaturalLanguage name ++ "."
| impl_intro e1 C1 a C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for implication."
| impl_elim a C1 C2 L R => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for implication."
end.

Fixpoint showForLogSeq_proofTreeOf_helper (indent : string) (j : judgementPart) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptionsWithEvidence j p)) in
match p with
| hole p => indent ++ "- " ++ "We stopped the proof at this point and assumed it was provable."
| assume e a C => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: we assume this"
| bot_elim a C M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: the principle of explosion
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| and_intro a C1 C2 L R => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and introduction
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ R
| and_elim1 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| and_elim2 a C1 C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_intro1 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_intro2 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_elim1 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_elim2 a C1 C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| trust a1 a2 C name L => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: trust, with relation " ++ showForLogSeq name ++ "
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L
| impl_intro e1 C1 a C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication introduction
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| impl_elim a C1 C2 L R => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication elimination
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ R
end.

Open Scope string.

Definition showForProofTree_proofTreeOf j p
  := "\begin{prooftree}" ++ showForProofTree_proofTreeOf_helper j p
       ++ "\end{prooftree}".
Instance showForProofTree_proofTreeOf_instance (j : judgementPart)
  : ShowForProofTree (proofTreeOf j) := { showForProofTree := showForProofTree_proofTreeOf j}.

Definition showForNaturalLanguage_proofTreeOf j p := "

" ++ showForNaturalLanguage_proofTreeOf_helper "- " j p ++ "

".
Instance showForNaturalLanguage_proofTreeOf_instance (j : judgementPart)
  : ShowForNaturalLanguage (proofTreeOf j) := { showForNaturalLanguage := showForNaturalLanguage_proofTreeOf j}.

Definition printProofTitle j :=
match j with
| JudgementPart a c => "### Veracity proof that " ++ showForLogSeq c ++ " is held by " ++ showForLogSeq a
end.

Instance : ShowForLogSeq string := { showForLogSeq := id}.

Definition showForLogSeq_proofTreeOf j p := 
let evidenceList := (removeDups (filter isAtomicEvidence (getAllEvidence j p))) in
let evidenceWithNames := map (fun e => match e with
                                   | AtomicEvid n => showForLogSeq e ++ " = " ++ showForLogSeq n
                                   | _ => ""
                                   end) evidenceList in
"

" ++ printProofTitle j ++ "
" ++ showForLogSeq_proofTreeOf_helper "  " j p ++ "
  - Atomic evidence is abbreviated as follows:
    collapsed:: true
" ++ showForLogSeq_list "    " evidenceWithNames ++ "

".
Instance showForLogSeq_proofTreeOf_instance (j : judgementPart)
  : ShowForLogSeq (proofTreeOf j) := { showForLogSeq := showForLogSeq_proofTreeOf j}.

Fixpoint showListOfProofTrees {j : judgementPart} (l : list (proofTreeOf j)) :=
    match l with
      | [] => ""
      | h :: tl => "

----------------

" ++ showForProofTree h ++ showListOfProofTrees tl
    end.

(* |

Proof Automation without Ltac
-----------------------------

The approach taken here is to search for proofs using Coq's functional language, rather than relying on Ltac.
This will:
 - Perform backwards search
 - Use "hole" (which may in future be renamed "hole") to fill in holes in the current proofs search.
 - Involve a function which takes a single proof tree (potentially containing holes), and generates a list of proof trees "one level deeper", potentially including holes.
 - Include a depth limit, after which the proof search is halted.
 - Include a function to filter out proof trees based on whether they still contain holes, (and in the future other attributes such as whether the resulting weight is above a certain value)
 - Involve a function that takes a list of prooftrees and returns a list of prooftrees "one level deeper", making use of the function which takes a single proof tree as input.

|*)

Definition toProofTreeWithHole (a : actor) (c : claim) := hole (\by a \in c).
Definition eB := AtomicEvid _eB_.
Definition T := Trust _T_.

Open Scope beq_scope.

Definition proofStepExample1 (j : judgementPart) : list (proofTreeOf j) :=
  match j with
  | JudgementPart a c => 
    (** Assumptions: *)
    (if (a =? a1) && (c =? C) then [assume e a c] else [])
    ++
    (if (a =? a2) && (c =? C) then [assume e a c] else [])
    ++
    (if (a =? a1) && (c =? (C /\' C)) then [assume e a c] else [])
    ++
    (** Trust relations: *)
    (if (a =? a1) then [trust a a2 c T (hole _); trust a a3 c T (hole _)] else [])
    ++
    (if (a =? a2) then [trust a a3 c T (hole _)] else [])
    ++
    (** Rules for specific claim patterns: *)
    match c with
      | And C1 C2 => [and_intro a C1 C2 (hole _) (hole _)] 
      | Or C1 C2 => [or_intro1 a C1 C2 (hole _); or_intro2 a C1 C2 (hole _)]
      (** The rules for Implies should echo the rules for assumptions, ideally. Or else involve eQ. *)
      | Implies C1 C2 =>
          (if (a =? a1) && (C1 =? _|_) then [impl_intro e C1 a C2 (hole _)] else [])
          ++
          (if (a =? a1) && (C1 =? C) then [impl_intro e C1 a C2 (hole _)] else [])
          ++
          (if (a =? a2) && (C1 =? C) then [impl_intro e C1 a C2 (hole _)] else [])
          ++
          (if (a =? a1) && (C1 =? (C /\' C)) then [impl_intro e C1 a C2 (hole _)] else [])
      | _ => []
      end
    ++
    (** Rules that can be applied to any claim, use with caution, can cause performance issues. *)
    [
      (bot_elim a c (assume eB a _|_))
      (* ; (or_elim1 a c c1 (hole _))
      ; (or_elim1 a c c2 (hole _))
      ; (or_elim1 a c c3 (hole _))
      ; (or_elim2 a c1 c (hole _))
      ; (or_elim2 a c2 c (hole _))
      ; (or_elim2 a c3 c (hole _))
      ; (and_elim1 a c c1 (hole _))
      ; (and_elim1 a c c2 (hole _))
      ; (and_elim1 a c c3 (hole _))
      ; (and_elim2 a c1 c (hole _))
      ; (and_elim2 a c2 c (hole _))
      ; (and_elim2 a c3 c (hole _)) *)
      ; (impl_elim a _|_ c (hole _) (hole _))
      (* ; (impl_elim a c1 c (hole _) (hole _))
      ; (impl_elim a c2 c (hole _) (hole _))
      ; (impl_elim a c3 c (hole _) (hole _)) *)
    ]
  end.

Close Scope beq_scope.

Eval compute in proofStepExample1 (\by a1 \in (C /\' C)).

Fixpoint oneLevelDeeper (step : forall j : judgementPart, list (proofTreeOf j)) (j : judgementPart) (p : proofTreeOf j) : list (proofTreeOf j) :=
  match p with
| hole j => step j
| assume e a c => [(assume e a c)]
| bot_elim a C M => map (bot_elim a C) (oneLevelDeeper step _ M)
| and_intro a C1 C2 L R => map (fun L2 => and_intro a C1 C2 L2 R) (oneLevelDeeper step _ L)
                        ++ map (and_intro a C1 C2 L) (oneLevelDeeper step _ R)
| and_elim1 a C1 C2 M => map (and_elim1 a C1 C2) (oneLevelDeeper step _ M)
| and_elim2 a C1 C2 M => map (and_elim2 a C1 C2) (oneLevelDeeper step _ M)
| or_intro1 a C1 C2 M => map (or_intro1 a C1 C2) (oneLevelDeeper step _ M)
| or_intro2 a C1 C2 M => map (or_intro2 a C1 C2) (oneLevelDeeper step _ M)
| or_elim1 a C1 C2 M => map (or_elim1 a C1 C2) (oneLevelDeeper step _ M)
| or_elim2 a C1 C2 M => map (or_elim2 a C1 C2) (oneLevelDeeper step _ M)
| trust a1 a2 C name L => map (trust a1 a2 C name) (oneLevelDeeper step _ L)
| impl_intro e1 C1 a C2 M => map (impl_intro e1 C1 a C2) (oneLevelDeeper step _ M)
| impl_elim a C1 C2 L R => map (fun L2 => impl_elim a C1 C2 L2 R) (oneLevelDeeper step _ L)
                        ++ map (impl_elim a C1 C2 L) (oneLevelDeeper step _ R)
end
.

(* Eval compute in oneLevelDeeper _ (toProofTreeWithHole a1 (C /\' C)). *)

Definition oneLevelDeeperOfList step j (l : list (proofTreeOf j)) : list (proofTreeOf j) :=
 removeDups (flat_map (oneLevelDeeper step j) l).

(*|
.. coq:: unfold
   :class: coq-math
|*)


(* Eval compute in  showForProofTree (oneLevelDeeperOfList _ (oneLevelDeeperOfList _ (oneLevelDeeper _ (toProofTreeWithHole a1 (C /\' C /\' C))))). *)

(*|
.. coq::
|*)

(* Not needed, using proofSearch instead which has a similar idea to using this but has some optimisations.
Fixpoint repeatFn {A : Type} (n : nat) (f : A -> A) :=
match n with
  | 0 => id
  | 1 => f
  | S n' => fun a => f (repeatFn n' f a)
end.
*)

Open Scope list_scope.
(* Not needed, using proofSearch instead which has a similar idea to using this but has some optimisations.
Fixpoint repeatListFnAndKeepPartials {A : Type} `{Beq A} (n : nat) (f : list A -> list A) (l : list A) :=
match n with
  | 0 => []
  | 1 => removeDups (f l)
  | S n' => removeDups ((f l) ++ f (repeatListFnAndKeepPartials n' f l))
end.
Definition generateProofsWithDepthLimit step j d := repeatListFnAndKeepPartials d (oneLevelDeeperOfList step j).
*)

Fixpoint noHoles {j : judgementPart} (p : proofTreeOf j) : bool :=
  match p with
| hole j => false
| assume e a C => true
| bot_elim a C M => noHoles M
| and_intro a C1 C2 L R => noHoles L && noHoles R
| and_elim1 a C1 C2 M => noHoles M
| and_elim2 a C1 C2 M => noHoles M
| or_intro1 a C1 C2 M => noHoles M
| or_intro2 a C1 C2 M => noHoles M
| or_elim1 a C1 C2 M => noHoles M
| or_elim2 a C1 C2 M => noHoles M
| trust a1 a2 C name L => noHoles L
| impl_intro e1 C1 a C2 M => noHoles M
| impl_elim a C1 C2 L R => noHoles L && noHoles R
end
.

Fixpoint proofSearch (d : nat) step (j : judgementPart) (l : list (proofTreeOf j))  : list (proofTreeOf j) := 
  match d with
  | 0 => []
  | S d' => let newL := removeDups (oneLevelDeeperOfList step j l) in (filter noHoles newL) ++ proofSearch d' step j (filter (fun p => negb (noHoles p)) newL) 
  end.

(** TODO: Try removing string comparison and replacing it with more native comparison, might cause speedup. *)

(*|
.. coq:: unfold
   :class: coq-math
|*)

Open Scope beq_scope.

Timeout 20 Eval vm_compute in (showListOfProofTrees (( (proofSearch 4 proofStepExample1 _  [toProofTreeWithHole a1 ((Implies _|_ C))])))).

Definition proofStepExample2 (j : judgementPart) : list (proofTreeOf j) :=
  match j with
  | JudgementPart a c => 
    (** Assumptions: *)
    (if (a =? a1) && (c =? C) then [assume e a c] else [])
    ++
    (if (a =? a1) && (c =? (C /\' C)) then [assume e a c] else [])
    ++
    (** Rules for specific claim patterns: *)
    match c with
      | And C1 C2 => [and_intro a C1 C2 (hole _) (hole _)] 
      | _ => []
      end
  end.

Close Scope beq_scope.

Timeout 20 Eval vm_compute in (showListOfProofTrees (( (proofSearch 10 proofStepExample2 _  [toProofTreeWithHole a1 ((C /\' C) /\' (C /\' C))])))).

(* Time Eval compute in (showListOfProofTrees (( (proofSearch _  [toProofTreeWithHole a1 ((C /\' C) /\' (C /\' C) /\' (C /\' C) /\' (C /\' C))] 20)))). *)
(* Time Eval compute in (showListOfProofTrees ( filter noHoles (( (generateProofsWithDepthLimit _ 7  [toProofTreeWithHole a1 ((C /\' C) /\' (C /\' C))]))))). *)

(*|
.. coq::
|*)

(*|

An example from the paper
-------------------------

This example is the top half of the proof tree on p13 (Section 4.2) of the draft paper.

The proof trees visualised in this section are **automatically generated** by Coq.

|*)

Definition l := AtomicEvid _l_ .
Definition s := AtomicEvid _s_.
Definition c := AtomicEvid _c_evid_.
Definition P := Actor _P_.
Definition Q := Actor _Q_.
Definition C1 := AtomicClaim _c1_.
Definition C2 := AtomicClaim _c2_.
Definition C3 := AtomicClaim _c3_.
Definition C4 := AtomicClaim _c4_.
Definition C5 := AtomicClaim _c5_.

Definition trustT := Trust _T_.
Definition trustU := Trust _U_.
Definition trustV := Trust _V_.

Definition concreteProofTreeExampleWith2Conjuncts : 
proofTreeOf (\by P \in (C1 /\' C2)).
apply and_intro.
apply (assume e).
apply (assume s).
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

Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf (\by P \in (C1 /\' C2 /\' C3)).
epose proof (and_intro) P (C1 /\' C2) C3.
simpl in H.
apply H.
epose proof (and_intro) _ C1 C2.
simpl in H0.
apply H0.
apply (assume l).
apply (assume s).
apply (assume c).
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

Definition concreteProofTreeExampleWith3ConjunctsUsingExistingTree : 
proofTreeOf \by P \in (C1 /\' C2 /\' C3).
epose proof (and_intro) P (C1 /\' C2) C3.
simpl in H.
apply H.
exact concreteProofTreeExampleWith2Conjuncts.
Show Proof.
apply (assume c).
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

Definition concreteProofTreeExampleTrust : 
proofTreeOf\by a1 \in (C).
apply (trust a1 a2 C trustT).
apply (assume e).
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

Definition concreteProofTreeExampleWith3ConjunctsWithTrust : 
proofTreeOf\by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ _ _ trustU).
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

Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
proofTreeOf\by Q \in (C1 /\' C2 /\' C3).
eapply (trust Q Q _ trustU).
eapply (trust Q Q _ trustV).
eapply (trust _ _ _ trustU).
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

Record proofTreeOfClaim (c : claim) := {
  _a : actor;
  _p : proofTreeOf(\by _a \in c)
}.
Instance showProofTreeOfClaim (c : claim) : ShowForProofTree (proofTreeOfClaim c) := { showForProofTree p := showForProofTree (_p c p) }.
(* Instance showLongProofTreeOfClaim (c : claim) : ShowLong (proofTreeOfClaim c) := { showForNaturalLanguage p := showForNaturalLanguage (_p c p) }. *)
(* Instance showLong2ProofTreeOfClaim (c : claim) : ShowLong2 (proofTreeOfClaim c) := { showForLogSeq p := showForLogSeq (_p c p) }. *)

Definition exampleWithProofOf : proofTreeOfClaim C1.
Proof.
eexists _.
apply (assume e1 a1).
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

Definition usingAll : proofTreeOfClaim (Implies _|_ C1).
Proof.
eexists _.
eapply (or_elim1 _ _ C2).
eapply or_intro1.
eapply (or_elim2).
eapply or_intro2.
eapply and_elim1.
eapply and_intro.
eapply and_elim2.
eapply and_intro.
apply (assume e2 a1); apply leaf.
2: apply (assume e2 a1); apply leaf.
eapply (trust _ _ _ trustT).
eapply (impl_intro e2 _|_ a1 C1).
simpl.
eapply bot_elim.
apply (assume e2 a1 _|_).
Unshelve.
Show Proof.
all: apply C2.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree usingAll.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage usingAll.
Eval compute in showForLogSeq usingAll.

Ltac proveClaim := 
(* unshelve eexists _ _ _; *)
(repeat ( 
idtac
(* + unshelve eapply or_elim1 *)
(* + unshelve eapply hole *)
+ unshelve eapply or_intro1
(* + unshelve eapply or_elim2 *)
+ unshelve eapply or_intro2
(* + unshelve eapply and_elim1 *)
+ unshelve eapply and_intro
(* + unshelve eapply and_elim2 *)
+ unshelve eapply and_intro; simpl
+ unshelve apply assume
(* + unshelve eapply (trust _ _ _ _ _ (Trust "T")) *)
+ unshelve eapply (impl_intro)
+ simpl
+ unshelve eapply bot_elim));
repeat (apply a1
+ apply C2
+ apply e2
+ apply [])
.

From Ltac2 Require Import Ltac2.

Definition CQ := AtomicClaim _cQ_.
Definition aQ := Actor _aQ_.
Definition eQ := AtomicEvid _eQ_.

(* Ltac2 maybePrintMessage1 s := Message.print (Message.of_string s). *)
(* Ltac2 maybePrintMessage2 s := Message.print (Message.of_string s). *)
Ltac2 maybePrintMessage1 s := ().
Ltac2 maybePrintMessage2 s := ().
Ltac2 Type exn ::= [ VeracityProofSearchException(string) ].

Ltac2 tryAssumeWitha1 etc :=
(maybePrintMessage1 "Trying assume");
match! goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying assume"); eapply (assume _ a1); etc
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Ltac2 tryAndIntro etc :=
(maybePrintMessage1 "Trying and_intro");
match! goal with
   | [ |- (proofTreeOf _ \by _ \in (_ /\' _)) ] => (maybePrintMessage2 "Applying and_intro"); eapply and_intro; Control.enter (fun _ => etc)
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Ltac2 tryTrust etc :=
(maybePrintMessage1 "Trying trust");
match! goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying trust"); (eapply (trust _ _ _ _ _ _)); etc
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Open Scope string_scope.

Ltac2 fillConstant () :=
solve [ apply CQ | apply aQ | apply eQ | apply ([] : list judgement) | apply (Trust T) ].

Set Default Proof Mode "Ltac2".
(* Set Ltac2 Backtrace. *)

Ltac2 rec autoProveMain max_depth :=
match Int.equal 0 max_depth with
  | true => Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [
      eapply and_intro; autoProveMain (Int.sub max_depth 1)
    | eapply (assume eQ a1); autoProveMain (Int.sub max_depth 1)
    | eapply (trust _ _ _); autoProveMain (Int.sub max_depth 1)
    | fillConstant (); autoProveMain (Int.sub max_depth 1)
  ]
end.

Ltac2 rec autoProveHelper d :=
 Message.print (Message.of_string "Depth:");
 Message.print (Message.of_int d);
 solve [ autoProveMain d | autoProveHelper (Int.add d 1) ].

Ltac2 autoProve () := autoProveHelper 1.

(*|
The following demonstrates a constraing that the claim must be believed by actor 2, and we have constrained only assuming claims for actor 1 in the tactic.
|*)

Definition exampleC1 : proofTreeOfClaim (C2).
Proof.
eexists _.
autoProve ().
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree exampleC1.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage exampleC1.
Eval compute in showForLogSeq exampleC1.

Set Default Proof Mode "Ltac2".


(*|
The following demonstrates automatically proving a larger claim.
|*)
(*  *)
(* Set Default Goal Selector "!". *)

Definition automatedProof : proofTreeOfClaim (C1 /\' C2 /\' C3 /\' C4 /\' C5).
Proof.
eexists _.
Time autoProve ().  (* Finished transaction in 0.1 secs (0.099u,0.s) (successful) *)
(* Time autoProve (). Using match statements Finished transaction in 0.188 secs (0.181u,0.004s) (successful) *)
(* Time autoProveMain 7. Finished transaction in 0.002 secs (0.002u,0.s) (successful) *)
(* Time autoProveMain ().  Finished transaction in 1.503 secs (1.475u,0.s) (successful) *)
Show Proof.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree automatedProof.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage automatedProof.
Eval compute in showForLogSeq automatedProof.

Ltac2 rec autoProveMain1 max_depth :=
match Int.equal 0 max_depth with
  | true => Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [
      eapply and_intro; autoProveMain1 (Int.sub max_depth 1)
    | eapply (impl_intro); autoProveMain1 (Int.sub max_depth 1)
    | eapply (assume l P C1); autoProveMain1 (Int.sub max_depth 1)
    | eapply (assume s P C2); autoProveMain1 (Int.sub max_depth 1)
    | eapply (assume c P C3); autoProveMain1 (Int.sub max_depth 1)
    | simpl; autoProveMain1 (Int.sub max_depth 1)
    (* | eapply (trust _ _ _ _ _ _); autoProveMain1 (Int.sub max_depth 1) *)
    | fillConstant (); autoProveMain1 (Int.sub max_depth 1)
  ]
end.

Ltac2 rec autoProveHelper1 d :=
 Message.print (Message.of_string "Depth:");
 Message.print (Message.of_int d);
 solve [ autoProveMain1 d | autoProveHelper1 (Int.add d 1) ].

Ltac2 autoProve1 () := autoProveHelper1 1.

Definition fromPaper1 : proofTreeOfClaim (C1 /\' C2 /\' C3).
Proof.
eexists _.
autoProve1 ().
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree fromPaper1.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage fromPaper1.
Eval compute in showForLogSeq fromPaper1.

Definition healthy := AtomicClaim _healthy_ .
Definition nonToxic := AtomicClaim _nonToxic_.
Definition organic := AtomicClaim _organic_.
Definition belief := AtomicEvid _belief_.
Definition testing := AtomicEvid _testing_.
Definition audit := AtomicEvid _audit_.
Definition retailer := Actor _retailer_.
Definition vineyard := Actor _vineyard_.
Definition winery := Actor _winery_.


Definition exampleFromJosh : proofTreeOfClaim healthy.
eexists retailer.
eapply (impl_elim _ (nonToxic /\' organic)).
try (apply (assume belief retailer (Implies (nonToxic /\' organic) healthy))).
try (apply (assume testing vineyard nonToxic)).
try (apply (assume audit winery organic)).
eapply and_intro.
eapply (trust retailer vineyard _ trustT).
try (apply (assume belief retailer (Implies (nonToxic /\' organic) healthy))).
try (apply (assume testing vineyard nonToxic)).
try (apply (assume audit winery organic)).
eapply (trust retailer winery _ trustT).
try (apply (assume belief retailer (Implies (nonToxic /\' organic) healthy))).
try (apply (assume testing vineyard nonToxic)).
try (apply (assume audit winery organic)).
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree exampleFromJosh.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage exampleFromJosh.
Eval compute in showForLogSeq exampleFromJosh.

Ltac2 rec autoProveMain2 max_depth :=
match Int.equal 0 max_depth with
  | true => Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [
      eapply and_intro; autoProveMain2 (Int.sub max_depth 1)
    | eapply (impl_elim); autoProveMain2 (Int.sub max_depth 1)
    | eapply (trust retailer vineyard _ trustT); autoProveMain2 (Int.sub max_depth 1)
    | eapply (trust retailer winery _ trustT); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume testing vineyard nonToxic); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume belief retailer (Implies (nonToxic /\' organic) healthy)); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume audit winery organic); autoProveMain2 (Int.sub max_depth 1)
    (* | simpl; autoProveMain2 (Int.sub max_depth 1) *)
    (* | eapply (trust _ _ _ _ _ _); autoProveMain2 (Int.sub max_depth 1) *)
    | fillConstant (); autoProveMain2 (Int.sub max_depth 1)
  ]
end.

Ltac2 rec autoProveHelper2 d max_depth :=
 Message.print (Message.of_string "Depth:");
 Message.print (Message.of_int d);
 match Int.lt d max_depth with
 | true => solve [ autoProveMain2 d | autoProveHelper2 (Int.add d 1) max_depth ]
 | false => Message.print(Message.of_string "Reached max depth, possibly unprovable by these tactics.")
end.
Ltac2 autoProve2 () := autoProveHelper2 1 20.


Definition exampleFromJoshAuto : proofTreeOfClaim healthy.
eexists retailer.
Time autoProve2 ().
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree exampleFromJoshAuto.

(*|
.. coq::
|*)

(** Ltac-less proof automation of Josh's example *)

Open Scope beq_scope.

Definition exampleFromJoshProofStep (j : judgementPart) : list (proofTreeOf j) :=
  match j with
  | JudgementPart a c => 
    (** Assumptions: *)
    (if (a =? vineyard) && (c =? nonToxic) then [assume testing a c] else [])
    ++
    (if (a =? retailer) && (c =? (Implies (nonToxic /\' organic) healthy)) then [assume belief a c] else [])
    ++
    (if (a =? winery) && (c =? organic) then [assume audit a c] else [])
    ++
    (** Trust relations: *)
    (if (a =? retailer) then [trust a vineyard c trustT (hole _); trust a winery c T (hole _)] else [])
    ++
    (** Implication elimination: *)
    (if (a =? retailer) && (c =? healthy) then [impl_elim a (nonToxic /\' organic) c (hole _) (hole _)] else [])
    ++
    (** Rules for specific claim patterns: *)
    match c with
      (** The rules for And and Or can usually be left in. *)
      | And C1 C2 => [and_intro a C1 C2 (hole _) (hole _)] 
      | Or C1 C2 => [or_intro1 a C1 C2 (hole _); or_intro2 a C1 C2 (hole _)]
      (** The rules for Implies should echo the rules for assumptions, ideally. Or else involve eQ. *)
      | Implies C1 C2 =>
          []
      | _ => []
      end
  end.

Close Scope beq_scope.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Time Timeout 5 Eval vm_compute in (showListOfProofTrees (( (proofSearch 10 exampleFromJoshProofStep _  [toProofTreeWithHole retailer healthy])))).

(*|
.. coq::
|*)


Eval compute in (showForNaturalLanguage exampleFromJoshAuto).
Eval compute in showForLogSeq exampleFromJoshAuto.

Definition whiteboardExample : proofTreeOfClaim (Implies C1 C2).
Proof.
eexists a2.
eapply (impl_intro e1).
eapply (trust a2 _ _ trustT).
eapply hole.
Unshelve.
apply a2.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree whiteboardExample.

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage whiteboardExample).
Eval compute in showForLogSeq whiteboardExample.

Definition certifier := Actor _certifier_.
Definition applicant := Actor _applicant_.
Definition ingredients_valid := AtomicClaim _ingredients_valid_.
Definition recipe_valid := AtomicClaim _recipe_valid_.
Definition percentage_ingredients_valid := AtomicClaim _percentage_ingredients_valid_.
Definition breakdown_of_formulations_valid := AtomicClaim _breakdown_of_formulations_valid_.
Definition successful_market_compliance_assessment := AtomicClaim _successful_market_compliance_assessment_.
Definition compile := AtomicEvid _compile_.
Definition review := AtomicEvid _review_.
Definition assess := AtomicEvid _assess_.
Definition ingredients_percentage_list := AtomicEvid _ingredients_percentage_list_.
Definition breakdown_of_formulations_list := AtomicEvid _breakdown_of_formulations_list_.

(*
Definition preAssessmentRequirements : proofTreeOf (JudgementPart certifier recipe_valid).
Proof.
eapply (impl_elim applicant _ recipe_valid).
eapply (assume review).
eapply (impl_elim applicant _ breakdown_of_formulations_valid).
eapply (impl_elim certifier _ ingredients_valid).
eapply (assume compile).
eapply (impl_elim applicant _ (ingredients_valid)).
eapply (impl_elim _ _ successful_market_compliance_assessment).
eapply (assume review).
eapply (assume assess certifier).
eapply (impl_elim applicant _ percentage_ingredients_valid).
eapply (assume compile).
eapply (assume ingredients_percentage_list). 
eapply (assume breakdown_of_formulations_list).
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree preAssessmentRequirements.

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage preAssessmentRequirements).
Eval compute in showForLogSeq preAssessmentRequirements.

Definition preAssessmentRequirementsWithEvidHoles : proofTreeOf (JudgementPart certifier recipe_valid).
Proof.
eapply (impl_elim applicant _ recipe_valid).
eapply (assume review).
eapply (impl_elim applicant _ breakdown_of_formulations_valid).
eapply (impl_elim certifier _ ingredients_valid).
eapply (assume HoleEvid).
eapply (impl_elim applicant _ (ingredients_valid)).
eapply (impl_elim _ _ successful_market_compliance_assessment).
eapply (assume review).
eapply (assume assess certifier).
eapply (impl_elim applicant _ percentage_ingredients_valid).
eapply (assume HoleEvid).
eapply (assume HoleEvid). 
eapply (assume HoleEvid).
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in showForProofTree preAssessmentRequirementsWithEvidHoles.

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage preAssessmentRequirementsWithEvidHoles).
Eval compute in showForLogSeq preAssessmentRequirementsWithEvidHoles.
*)
Open Scope string_scope.

Definition allProofsAsString := 
    showForProofTree concreteProofTreeExampleWith2Conjuncts
 ++ showForProofTree concreteProofTreeExampleWith3Conjuncts
 ++ showForProofTree concreteProofTreeExampleTrust
 ++ showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrust
 ++ showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras
 ++ showForProofTree exampleWithProofOf
 ++ showForProofTree usingAll
 ++ showForProofTree exampleC1
 ++ showForProofTree automatedProof
 ++ showForProofTree fromPaper1
 ++ showForProofTree exampleFromJosh
 ++ showForProofTree exampleFromJoshAuto
 ++ showForProofTree whiteboardExample
 (*++ showForProofTree preAssessmentRequirements*).

(* Definition allProofsAsString := 
    showForLogSeq concreteProofTreeExampleWith2Conjuncts
 ++ showForLogSeq concreteProofTreeExampleWith3Conjuncts
 ++ showForLogSeq concreteProofTreeExampleTrust
 ++ showForLogSeq concreteProofTreeExampleWith3ConjunctsWithTrust
 ++ showForLogSeq concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras
 ++ showForLogSeq exampleWithProofOf
 ++ showForLogSeq usingAll
 ++ showForLogSeq exampleC1
 ++ showForLogSeq automatedProof
 ++ showForLogSeq fromPaper1
 ++ showForLogSeq exampleFromJosh
 ++ showForLogSeq exampleFromJoshAuto
 ++ showForLogSeq whiteboardExample. *)


(* Eval compute in allProofsAsString. *)

End VeracityLogic.