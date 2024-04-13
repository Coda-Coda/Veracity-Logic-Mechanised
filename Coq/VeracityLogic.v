(*|
Veracity Logic Mechanised in Coq
================================

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
  | _business_procedure_
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
  | _ingredients_valid_approved_
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
      | _business_procedure_ => "p"
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
      | _T_ => "trust relation T"
      | _U_ => "trust relation U"
      | _V_ => "trust relation V"
    end
  }.
Instance : ShowForLogSeq trust_relation_name := {showForLogSeq := showForNaturalLanguage}.

Inductive claim :=
  | AtomicClaim (n : claim_name)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Scheme Equality for claim.

Inductive evid :=
  | AtomicEvid (n : atomic_evid_name)
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (n : string) (c1 c2 : claim)
  | Apply (n : string) (c1 c2 : claim) (e1 : evid)
  | Cases (c : evid) (d e : string).

Scheme Equality for evid.

Inductive actor :=
  | Actor (n : actor_name).

Scheme Equality for actor.


Inductive trustRelation :=
  | Trust (n : trust_relation_name).

Scheme Equality for trustRelation.

Inductive judgement :=
  Judgement (e : evid) (a : actor) (c: claim).

Scheme Equality for judgement.



(*|

Judgements are a list of **single** judgements entailing some single judgement, or state that some claim :coq:`c` is a veracity claim.

|*)

(*|
Next, we introduce some notation for Coq.
|*)

Notation "E \by A \in C" := (Judgement E A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Notation "_|_" := (Bottom) (at level 1).
Notation "{{ x , y , .. , z }}" := (Pair .. (Pair x y) .. z).

(*|

We define a tagged type representing a trust relation.

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

(*|

For now, I have only implemented one inference rule, :coq:`and_intro`, as well as the :coq:`assume` rule and a rule :coq:`leaf` that declares that it is correct for a proof tree to stop on a statement such as :math:`C_1 \textit{ is a claim}`.

:coq:`proofTreeOf` is a data type, a tree, which depends on a judgement. The type :coq:`tree j` describes a tree which correctly proves :coq:`j`.

But this is not a proposition. This is best thought of as the datatype for (correct) proof trees.

The remaining rules will be easy to add, this will be done in 2024.

|*)

Inductive proofTreeOf {fDef : string -> evid -> evid} : judgement -> Type :=
| assume (e : evid) a (c : claim) : proofTreeOf (e \by a \in c)
| bot_elim e a C

        (M : proofTreeOf (e \by a \in _|_))
                           :
             proofTreeOf (e \by a \in C)

| and_intro e1 e2 a C1 C2

(L: proofTreeOf (e1 \by a \in C1))
                           (R: proofTreeOf (e2 \by a \in C2))
                        :
    proofTreeOf ({{e1, e2}} \by a \in (C1 /\' C2))

| and_elim1 e1 e2 a C1 C2

    (M : proofTreeOf ({{e1, e2}} \by a \in (C1 /\' C2)))
                           :
             proofTreeOf (e1 \by a \in C1)

| and_elim2 e1 e2 a C1 C2

    (M : proofTreeOf ({{e1, e2}} \by a \in (C1 /\' C2)))
                          :
        proofTreeOf (e2 \by a \in C2)

| or_intro1 e1 a C1 C2

           (M: proofTreeOf (e1 \by a \in C1))
                          :
    proofTreeOf ((Left e1) \by a \in (C1 \/' C2))

| or_intro2 e2 a C1 C2

           (M: proofTreeOf (e2 \by a \in C2))
                          :
    proofTreeOf ((Right e2) \by a \in (C1 \/' C2))

| or_elim1 e1 a C1 C2

      (M: proofTreeOf ((Left e1) \by a \in (C1 \/' C2)))
                          :
        proofTreeOf (e1 \by a \in C1)

| or_elim2 e2 a C1 C2

      (M : proofTreeOf ((Right e2) \by a \in (C1 \/' C2)))
                            :
          proofTreeOf (e2 \by a \in C2)

| or_elim3 c A B x d C y e a
      (H1 : proofTreeOf (c \by a \in (A \/' B)))
      (H2 : proofTreeOf (Apply d A C x) \by a \in C)
      (H3 : proofTreeOf (Apply y B C x) \by a \in C)
                      :
          proofTreeOf ((Cases c d e) \by a \in C)

| trust e a1 a2 C (name : trustRelation)

(L: proofTreeOf (e \by a2 \in C))
                          :
            proofTreeOf (e \by a1 \in C)

| impl_intro (e1 : evid) e2 a (C1 : claim) C2 n
             (H : fDef n e1 = e2)

              (M: proofTreeOf (e2 \by a \in C2))
                              :
   proofTreeOf ((Lambda n C1 C2) \by a \in (Implies C1 C2))

| impl_elim e1 a C1 C2 n

(L: proofTreeOf ((Lambda n C1 C2) \by a \in (Implies C1 C2)))
                           (R: proofTreeOf (e1 \by a \in C1))
                        :
    proofTreeOf ((Apply n C1 C2 e1) \by a \in C2)

| by_def1 e1 e2 a n C1 C2 (H : fDef n e1 = e2)
           (M : proofTreeOf (e2 \by a \in C2))
                  :
            proofTreeOf ((Apply n C1 C2 e1) \by a \in C2)
| by_def2 e1 e2 a n C1 C2 (H : fDef n e1 = e2)
     (M : proofTreeOf ((Apply n C1 C2 e1) \by a \in C2))
                  :
            proofTreeOf (e2 \by a \in C2)
.

Definition e := AtomicEvid _e_.
Definition C := AtomicClaim _c_.

Definition e1 := AtomicEvid _e1_.
Definition a1 := Actor _a1_.
Definition c1 := AtomicClaim _c1_.

Definition e2 := AtomicEvid _e2_.
Definition a2 := Actor  _a2_.
Definition c2 := AtomicClaim _c2_.

Record proofTreeOfClaim (a : actor) (c : claim) := {
  _f : string -> evid -> evid;
  _e : evid;
  _p : @proofTreeOf _f (_e \by a \in c)
}.

Definition impl_elim1 : proofTreeOfClaim a1 C.
eexists (
  fun n e1 => match n,e1 with
             | "g",e => Lambda "f" C C
             | "h",e => Lambda _ _ _
             | _,_ => e
             end
) _.
eapply (impl_elim _ _ _ _ "f").
eapply (by_def2 _ _ _ _ _ _ _).
eapply (impl_elim _ _ _ _ "g").
eapply (by_def2 _ _ _ _ _ _ _).
eapply (impl_elim _ _ _ _ "h").
eapply (assume _).
eapply (assume e).
eapply (assume e).
eapply (assume e).
Unshelve.
shelve.
eapply C.
1,2,3:shelve.
simpl. reflexivity.
eapply C.
simpl.
reflexivity.
Qed.

(* Up to here *)

Definition impl2 : proofTreeOfClaim a1 (Implies C (Implies C C)).
eexists (
  fun n e1 => match n,e1 with
             | "f",e => _
             | "g",e => _
             | _,_ => e
             end
) _.
eapply (impl_intro e1 _ _ _ _ "f" _).
eapply (impl_intro e2 _ _ _ _ "g" _).
eapply (assume e).
Unshelve.
1,2:shelve.
simpl. reflexivity. reflexivity.
Defined.

(* Definition impl2 : 
proofTreeOf (Lambda "f" C (Implies C C)) \by a1 \in (Implies C (Implies C C)).
eapply (impl_intro e1 _).
eapply (impl_intro e2 _).
eapply (assume e).
Defined. *)

Definition impl : proofTreeOfClaim a1 (Implies C C).
eexists (
  fun n e1 => match n,e1 with
             | "f",e => _
             | _,_ => e
             end
) _.
eapply (impl_intro e1 _ _ _ _ "f" _).
eapply (assume e).
Unshelve.
1:shelve.
simpl. reflexivity.
Defined.

(* Definition impl : 
proofTreeOf (Lambda "f" C C) \by a1 \in (Implies C C).
eapply (impl_intro e _).
eapply (assume e).
Defined. *)


(* Up to here *)

(*|
This is the :coq:`and_intro` rule as Coq sees it:
|*)

Check and_intro. (* .unfold *)

Fixpoint computeEvidence (j : judgement) (p : proofTreeOf j) : evid := 
match p with
| assume e a c => e
| bot_elim e a C M => computeEvidence _ M
| and_intro e1 e2 a C1 C2 L R => {{computeEvidence _ L,computeEvidence _ R}}
| and_elim1 e1 e2 a C1 C2 M => match computeEvidence _ M with
                          | {{e1,e2}} => e1
                          | e => e
                          end
| and_elim2 e1 e2 a C1 C2 M => match computeEvidence _ M with
                          | {{e1,e2}} => e2
                          | e => e
                          end
| or_intro1 e1 a C1 C2 M => Left (computeEvidence _ M)
| or_intro2 e2 a C1 C2 M => Right (computeEvidence _ M)
| or_elim1 e1 a C1 C2 M => match computeEvidence _ M with
                          | (Left e1) => e1
                          | e => e
                          end
| or_elim2 e2 a C1 C2 M => match computeEvidence _ M with
                          | (Right e2) => e2
                          | e => e
                          end
| trust e a1 a2 C name L => computeEvidence _ L
| impl_intro e1 e2 a C1 C2 M => Lambda e1 (computeEvidence _ M)
| impl_elim e1 e2 a C1 C2 L R => Apply (computeEvidence _ L) (computeEvidence _ R)
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

Definition j1 := e2 \by a2 \in c2.
Definition j2 := e4 \by a4 \in c4.

(*|
Example use of notation:
|*)

Check e1 \by a1 \in c1.

(*|
For each datatype defined earlier, we define a string representation of it.
|*)

Instance : ShowForProofTree evid := {
  showForProofTree :=
  fix showForProofTreeEvid e :=
      match e with
      | AtomicEvid name => showForProofTree name
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
(* Instance showForLogSeq_list_instance (A : Type) `(ShowForLogSeq A) (indent : string) : ShowForLogSeq (list A) := {
    showForLogSeq l := showForLogSeq_list indent l
  }. *)

Instance : ShowForProofTree judgement := {
  showForProofTree j :=
  match j with
  | Judgement e a c => showForProofTree e ++ "^{" ++ showForProofTree a ++ "} \in "
                                  ++ showForProofTree c
  end
}.

Instance : ShowForNaturalLanguage judgement := {
  showForNaturalLanguage j :=
  match j with
  | Judgement e a c => showForNaturalLanguage c ++ " is supported by $" ++ showForNaturalLanguage e ++ "$ which " ++ showForNaturalLanguage a ++ " uses"
  end
}.

Instance : ShowForLogSeq judgement := {
  showForLogSeq j :=
  match j with
  | Judgement e a c => showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence $" ++ showForLogSeq e ++ "$"
  end
}.

Definition showForProofTree_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : proofTreeOf j) :=
    match Ps with
      | [] => showForProofTree j
      | (h :: tl) as Ps => showForProofTree Ps ++ " \vdash_{" ++ showForProofTree Ts ++ "} " ++ (showForProofTree j)
    end.

Eval compute in showForProofTree_judgement [(e1 \by a1 \in c1)] [] (e1 \by a1 \in c1) (assume e1 a1 c1).

Definition showForNaturalLanguage_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : proofTreeOf j) :=
  match Ps with
    | [] => showForNaturalLanguage j
    | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage j
  end.

(* Definition showForLogSeq_judgement (Ps : list judgement) (Ts : list trustRelation) (indent : string) (j : judgementPart) (p : proofTreeOf j) :=
  DELETEME  
  match Ps,Ts with
        | [],[] => showForLogSeq j ++ "
" ++ indent ++ "- " ++ "Assumptions made: None" ++ "
" ++ indent ++ "- " ++ "Trust relations used: None"
        | (h :: tl),[] => showForLogSeq j ++ "
" ++ indent ++ "- " ++ "Assumptions made:" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used: None"
        | [],(h :: tl) => showForLogSeq j ++ "
" ++ indent ++ "- " ++ "Assumptions made: None" ++ "
" ++ indent ++ "- " ++ "Trust relations used:" ++ showForLogSeq_list ("  " ++ indent) Ts
        | (h :: tl),(h2::tl2) => showForLogSeq j ++ "
" ++ indent ++ "- " ++ "Assumptions made:" ++ showForLogSeq_list ("  " ++ indent) Ps ++ "
" ++ indent ++ "- " ++ "Trust relations used:" ++ showForLogSeq_list ("  " ++ indent) Ts
      end. *)


Definition showForLogSeq_judgement (Ps : list judgement) (Ts : list trustRelation) (indent : string) (j : judgement) (p : proofTreeOf j) :=
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

Fixpoint getAllTrustRelationsUsed (j : judgement) (p : proofTreeOf j)
  : list trustRelation :=
match p with
| assume e a C => []
| bot_elim e a C M => getAllTrustRelationsUsed _ M
| and_intro e1 e2 a C1 C2 L R => 
    getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
| and_elim1 e1 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| and_elim2 e1 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro1 e1  a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim1 e1 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim2 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| trust e a1 a2 C name L => 
    name :: getAllTrustRelationsUsed _ L
| impl_intro e1 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| impl_elim e1 e2 a C1 C2 L R => 
   getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
end.

Fixpoint getAllEvidence (j : judgement) (p : proofTreeOf j)
  : list evid :=
match p with
| assume e a C => [e]
| bot_elim e a C M => (getAllEvidence _ M)
| and_intro e1 e2 a C1 C2 L R => getAllEvidence _ L ++ getAllEvidence _ R 
| and_elim1 e1 e2 a C1 C2 M => getAllEvidence _ M
| and_elim2 e1 e2 a C1 C2 M => getAllEvidence _ M
| or_intro1 e1 a C1 C2 M => getAllEvidence _ M
| or_intro2 e2 a C1 C2 M => getAllEvidence _ M
| or_elim1 e1 a C1 C2 M => getAllEvidence _ M
| or_elim2 e2 a C1 C2 M => getAllEvidence _ M
| trust e a1 a2 C name L => getAllEvidence _ L
| impl_intro e1 e2 a C1 C2 M => getAllEvidence _ M
| impl_elim e1 e2 a C1 C2 L R => getAllEvidence _ L ++ getAllEvidence _ R 
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Fixpoint getAssumptions (j : judgement) (p : proofTreeOf j) : list judgement := 
match p with
| assume e a C => [e \by a \in C]
| bot_elim e a C M => getAssumptions _ M
| and_intro e1 e2 a C1 C2 L R => 
    getAssumptions _ L ++ getAssumptions _ R 
| and_elim1 e1 e2 a C1 C2 M => getAssumptions _ M
| and_elim2 e1 e2 a C1 C2 M => getAssumptions _ M
| or_intro1 e1 a C1 C2 M => getAssumptions _ M
| or_intro2 e2 a C1 C2 M => getAssumptions _ M
| or_elim1 e1 a C1 C2 M => getAssumptions _ M
| or_elim2 e2 a C1 C2 M => getAssumptions _ M
| trust e a1 a2 C name L => 
    getAssumptions _ L
| impl_intro e1 e2 a C1 C2 M => filter (fun j => negb (judgement_beq (e1 \by a \in C1) j)) (getAssumptions _ M)
| impl_elim e1 e2 a C1 C2 L R => 
   getAssumptions _ L ++ getAssumptions _ R 
end.

Close Scope string.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
match l with
| [] => []
| h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
end.

Open Scope beq_scope.

Fixpoint proofTreeOf_beq {j1 j2 : judgement} (P1 : proofTreeOf j1) (P2 : proofTreeOf j2) : bool :=
match P1,P2 with
| assume e a1 C1, assume e2 a2 C2 => (e =? e2) && (a1 =? a2) && (C1 =? C2)
| bot_elim e a1 C1 M1, bot_elim e2 a2 C2 M2 => (e =? e2) && (a1 =? a2) && (C1 =? C2) && proofTreeOf_beq M1 M2
| and_intro e1 e2 a C1 C2 L R, and_intro e1' e2' a' C1' C2' L' R' => (e1 =? e1') && (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq L L' && proofTreeOf_beq R R'
| and_elim1 e1 e2 a C1 C2 M, and_elim1 e1' e2' a' C1' C2' M' => (e1 =? e1') && (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| and_elim2 e1 e2 a C1 C2 M, and_elim2 e1' e2' a' C1' C2' M' => (e1 =? e1') && (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_intro1 e1 a C1 C2 M, or_intro1 e1' a' C1' C2' M' => (e1 =? e1') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_intro2 e2 a C1 C2 M, or_intro2 e2' a' C1' C2' M' => (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_elim1 e1 a C1 C2 M, or_elim1 e1' a' C1' C2' M' => (e1 =? e1') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_elim2 e2 a C1 C2 M, or_elim2 e2' a' C1' C2' M' => (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| trust e a1 a2 C T L, trust e' a1' a2' C' T' L' => (e =? e') && (a1 =? a1') && (a2 =? a2') && (C =? C') && (T =? T') && proofTreeOf_beq L L'
| impl_intro e1 e2 a C1 C2 M, impl_intro e1' e2' a' C1' C2' M' => (e1 =? e1') && (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| impl_elim e1 e2 a C1 C2 L R, impl_elim e1' e2' a' C1' C2' L' R' => (e1 =? e1') && (e2 =? e2') && (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq L L' && proofTreeOf_beq R R'
| _,_ => false
end.

Instance beq_proofTreeOf_instance (j : judgement) : Beq (proofTreeOf j) := { beq := proofTreeOf_beq }.

Close Scope beq_scope.

Open Scope string.

Fixpoint showForProofTree_proofTreeOf_helper (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| assume e a C => "\AxiomC{$ " 
             ++ showForProofTree C 
             ++ " \textit{ is a veracity claim} $}"
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| bot_elim e a C M => showForProofTree_proofTreeOf_helper _ M
    ++ " \RightLabel{ $ \bot^{-} $} \UnaryInfC{$ "
    ++ showForProofTree_judgement Ps Ts _ p
    ++ " $}"
| and_intro e1 e2 a C1 C2 L R => 
    showForProofTree_proofTreeOf_helper _ L
 ++ showForProofTree_proofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| and_elim1 e1 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| and_elim2 e1 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \land^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro1 e1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro2 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_elim1 e1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_elim2 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{-2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| trust e a1 a2 C name L => 
    showForProofTree_proofTreeOf_helper _ L
 ++ " \AxiomC{$" ++ showForProofTree a1 ++ showForProofTree name ++ showForProofTree a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ showForProofTree name
 ++ "$} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| impl_intro e1 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| impl_elim e1 e2 a C1 C2 L R => 
     showForProofTree_proofTreeOf_helper _ L
 ++ showForProofTree_proofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \rightarrow^{-} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
end.

Fixpoint showForNaturalLanguage_proofTreeOf_helper (indent : string) (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| assume e a C => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ indent ++ showForNaturalLanguage C ++ " is a veracity claim." ++ "
"
++ indent ++ "by assumption."
| bot_elim e a C M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by the logical principle of explosion."
| and_intro e1 e2 a C1 C2 L R => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim1 e1 e2 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim2 e1 e2 a C1 C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| or_intro1 e1 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_intro2 e2 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim1 e1 a C1 C2 M =>
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim2 e2 a C1 C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| trust e a1 a2 C name L => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ indent ++ "by the trust relation " ++ showForNaturalLanguage name ++ "."
| impl_intro e1 e2 a C1 C2 M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for implication."
| impl_elim e1 e2 a C1 C2 L R => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for implication."
end.

Fixpoint showForLogSeq_proofTreeOf_helper (indent : string) (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| assume e a C => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: we assume this"
| bot_elim e a C M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: the principle of explosion
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| and_intro e1 e2 a C1 C2 L R => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and introduction
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ R
| and_elim1 e1 e2 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| and_elim2 e1 e2 a C1 C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_intro1 e1 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_intro2 e2 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or introduction (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_elim1 e1 a C1 C2 M =>
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (1)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| or_elim2 e2 a C1 C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: or elimination (2)
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| trust e a1 a2 C name L => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: trust, with relation " ++ showForLogSeq name ++ "
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L
| impl_intro e1 e2 a C1 C2 M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication introduction
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| impl_elim e1 e2 a C1 C2 L R => 
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
Instance showForProofTree_proofTreeOf_instance (j : judgement)
  : ShowForProofTree (proofTreeOf j) := { showForProofTree := showForProofTree_proofTreeOf j}.

Definition showForNaturalLanguage_proofTreeOf j p := "

" ++ showForNaturalLanguage_proofTreeOf_helper "- " j p ++ "

".
Instance showForNaturalLanguage_proofTreeOf_instance (j : judgement)
  : ShowForNaturalLanguage (proofTreeOf j) := { showForNaturalLanguage := showForNaturalLanguage_proofTreeOf j}.

Definition printProofTitle j :=
match j with
| Judgement e a c => "### Veracity proof that " ++ showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence " ++ showForLogSeq e
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
Instance showForLogSeq_proofTreeOf_instance (j : judgement)
  : ShowForLogSeq (proofTreeOf j) := { showForLogSeq := showForLogSeq_proofTreeOf j}.

Fixpoint showListOfProofTrees {j : judgement} (l : list (proofTreeOf j)) :=
    match l with
      | [] => ""
      | h :: tl => "

----------------

" ++ showForProofTree h ++ showListOfProofTrees tl
    end.

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
proofTreeOf ({{l, s}} \by P \in (C1 /\' C2)).
apply and_intro.
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

Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf ({{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3)).
apply and_intro.
apply and_intro.
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
proofTreeOf {{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3).
apply and_intro.
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
proofTreeOf e \by a1 \in (C).
eapply (trust _ a1 a2 C trustT).
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
proofTreeOf {{{{l, s}},c}} \by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ _ _ _ trustU).
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
proofTreeOf {{{{l, s}},c}} \by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ Q Q _ trustU).
eapply (trust _ Q Q _ trustV).
eapply (trust _ _ _ _ trustU).
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
  _e : evid;
  _a : actor;
  _p : proofTreeOf (_e \by _a \in c)
}.
Instance showForProofTree_proofTreeOfClaim_instance (c : claim) : ShowForProofTree (proofTreeOfClaim c) := { showForProofTree p := showForProofTree (_p c p) }.
Instance showForNaturalLanguage_proofTreeOfClaim_instance (c : claim) : ShowForNaturalLanguage (proofTreeOfClaim c) := { showForNaturalLanguage p := showForNaturalLanguage (_p c p) }.
Instance showForLogSeq_proofTreeOfClaim_instance (c : claim) : ShowForLogSeq (proofTreeOfClaim c) := { showForLogSeq p := showForLogSeq (_p c p) }.


Definition exampleWithProofOf : proofTreeOfClaim C1.
Proof.
eexists _ _.
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
eexists _ _.
eapply (or_elim1 _ _ _ C2).
eapply or_intro1.
eapply (or_elim2).
eapply or_intro2.
eapply and_elim1.
eapply and_intro.
eapply and_elim2.
eapply and_intro.
apply (assume e2 a1).
2: apply (assume e2 a1).
eapply (trust _ _ _ _ trustT).
eapply (impl_intro e2 _ a1 _|_ C1).
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
eexists _ retailer.
eapply (impl_elim _ _ _ (nonToxic /\' organic)).
try (apply (assume belief retailer (Implies (nonToxic /\' organic) healthy))).
try (apply (assume testing vineyard nonToxic)).
try (apply (assume audit winery organic)).
eapply and_intro.
eapply (trust _ retailer vineyard _ trustT).
try (apply (assume belief retailer (Implies (nonToxic /\' organic) healthy))).
try (apply (assume testing vineyard nonToxic)).
try (apply (assume audit winery organic)).
eapply (trust _ retailer winery _ trustT).
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

Definition certifier := Actor _certifier_.
Definition applicant := Actor _applicant_.
Definition ingredients_valid := AtomicClaim _ingredients_valid_.
Definition ingredients_valid_approved := AtomicClaim _ingredients_valid_approved_.
Definition recipe_valid := AtomicClaim _recipe_valid_.
Definition percentage_ingredients_valid := AtomicClaim _percentage_ingredients_valid_.
Definition breakdown_of_formulations_valid := AtomicClaim _breakdown_of_formulations_valid_.
Definition successful_market_compliance_assessment := AtomicClaim _successful_market_compliance_assessment_.
Definition compile := AtomicEvid _compile_.
Definition review := AtomicEvid _review_.
Definition assess := AtomicEvid _assess_.
Definition business_procedure := AtomicEvid _business_procedure_.
Definition ingredients_percentage_list := AtomicEvid _ingredients_percentage_list_.
Definition breakdown_of_formulations_list := AtomicEvid _breakdown_of_formulations_list_.

Definition preAssessmentRequirements : proofTreeOfClaim recipe_valid.
Proof.
eexists _ certifier.
eapply (trust _ certifier applicant _ trustT).
eapply (impl_elim _ _ _ breakdown_of_formulations_valid).
eapply (trust _ applicant certifier  _ trustU).
eapply (impl_elim _ _ _ ingredients_valid_approved).
eapply (assume business_procedure).
eapply (impl_elim _ _ _ successful_market_compliance_assessment).
eapply (impl_elim _ _ _ (ingredients_valid)).
eapply (assume review).
eapply (trust _ certifier applicant _ trustT).
eapply (impl_elim _ _ _ percentage_ingredients_valid).
eapply (assume compile).
eapply (assume ingredients_percentage_list). 
eapply (assume assess certifier).
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

Definition problematicExample1 : proofTreeOfClaim (Implies c1 c2).
Proof.
eexists _ a1.
apply (impl_intro e1).
eapply or_elim2.
Fail eapply or_intro1. (* .unfold *)
Fail eapply (assume e1 a1 c1).
Abort.

Open Scope string_scope.

Definition allProofsAsString := 
    showForProofTree concreteProofTreeExampleWith2Conjuncts
 ++ showForProofTree concreteProofTreeExampleWith3Conjuncts
 ++ showForProofTree concreteProofTreeExampleTrust
 ++ showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrust
 ++ showForProofTree concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras
 ++ showForProofTree exampleWithProofOf
 ++ showForProofTree usingAll
 ++ showForProofTree exampleFromJosh
 ++ showForProofTree preAssessmentRequirements.

End VeracityLogic.