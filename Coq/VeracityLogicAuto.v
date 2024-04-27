(*|
Veracity Logic Mechanised in Coq (Automation Version)
=====================================================

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

(*|

Types for names
---------------

|*)

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

(*|

Types of aspects of the veracity logic
--------------------------------------

|*)

Inductive evid :=
  | HoleEvid
  | AtomicEvid (n : atomic_evid_name)
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid).

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

Notation "\by A \in C" := (JudgementPart A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Notation "_|_" := (Bottom) (at level 1).
Notation "{{ x , y , .. , z }}" := (Pair .. (Pair x y) .. z).

Inductive trustRelation :=
  | Trust (n : trust_relation_name).

Scheme Equality for trustRelation.

Inductive judgement :=
  Judgement (e : evid) (jp : judgementPart).

Scheme Equality for judgement.

(*|

The central inductive definition of valid proof trees
-----------------------------------------------------

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

| or_intro1 a C1 C2

           (M: proofTreeOf (\by a \in C1))
                          :
    proofTreeOf (\by a \in (C1 \/' C2))

| or_intro2 a C1 C2

           (M: proofTreeOf (\by a \in C2))
                          :
    proofTreeOf (\by a \in (C1 \/' C2))

| trust a1 a2 C (name : trustRelation)

(L: proofTreeOf (\by a2 \in C))
                          :
            proofTreeOf (\by a1 \in C)
.

Fixpoint computeEvidence (j : judgementPart) (p : proofTreeOf j) : evid := 
match p with
| hole _ => HoleEvid
| assume e a c => e
| bot_elim a C M => computeEvidence _ M
| and_intro a C1 C2 L R => {{computeEvidence _ L,computeEvidence _ R}}
| or_intro1 a C1 C2 M => Left (computeEvidence _ M)
| or_intro2 a C1 C2 M => Right (computeEvidence _ M)
| trust a1 a2 C name L => computeEvidence _ L
end.

Fixpoint getAssumptionsWithEvidence (j : judgementPart) (p : proofTreeOf j) : list (judgement) := 
match p with
| hole j => [(Judgement HoleEvid j)]
| assume e a C => [Judgement e (\by a \in C)]
| bot_elim a C M => getAssumptionsWithEvidence _ M
| and_intro a C1 C2 L R => 
    getAssumptionsWithEvidence _ L ++ getAssumptionsWithEvidence _ R 
| or_intro1 a C1 C2 M => getAssumptionsWithEvidence _ M
| or_intro2 a C1 C2 M => getAssumptionsWithEvidence _ M
| trust a1 a2 C name L => 
    getAssumptionsWithEvidence _ L
end.

(*|

String representations
----------------------

|*)

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

Definition showForNaturalLanguage_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgementPart) (p : proofTreeOf j) :=
  let computedEvidence := computeEvidence j p in
    match Ps with
      | [] => showForNaturalLanguage (Judgement computedEvidence j)
      | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage (Judgement computedEvidence j)
    end.

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
| or_intro1 a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 a C1 C2 M => getAllTrustRelationsUsed _ M
| trust a1 a2 C name L => 
    name :: getAllTrustRelationsUsed _ L
end.

Fixpoint getAllEvidence (j : judgementPart) (p : proofTreeOf j)
  : list evid :=
match p with
| hole _ => [HoleEvid]
| assume e a C => [e]
| bot_elim a C M => (getAllEvidence _ M)
| and_intro a C1 C2 L R => 
    getAllEvidence _ L ++ getAllEvidence _ R 
| or_intro1 a C1 C2 M => getAllEvidence _ M
| or_intro2 a C1 C2 M => getAllEvidence _ M
| trust a1 a2 C name L => getAllEvidence _ L
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Close Scope string.

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
| or_intro1 a C1 C2 M, or_intro1 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| or_intro2 a C1 C2 M, or_intro2 a' C1' C2' M' => (a =? a') && (C1 =? C1') && (C2 =? C2') && proofTreeOf_beq M M'
| trust a1 a2 C T L, trust a1' a2' C' T' L' => (a1 =? a1') && (a2 =? a2') && (C =? C') && (T =? T') && proofTreeOf_beq L L'
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
| or_intro1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| trust a1 a2 C name L => 
    showForProofTree_proofTreeOf_helper _ L
 ++ " \AxiomC{$" ++ showForProofTree a1 ++ showForProofTree name ++ showForProofTree a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ showForProofTree name
 ++ "$} \BinaryInfC{$ "
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
| trust a1 a2 C name L => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ indent ++ "by the trust relation " ++ showForNaturalLanguage name ++ "."
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
| trust a1 a2 C name L => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: trust, with relation " ++ showForLogSeq name ++ "
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L
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


(*|

Example actors, evidence and claims
-----------------------------------

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

Definition eB := AtomicEvid _eB_.
Definition T := Trust _T_.

(*|

Proof Automation
----------------

The approach taken here is to construct proofs using Coq's functional language, rather than relying on Ltac.
This will:

* Perform backwards search.
* Use "hole" to fill in holes in the current proofs search.
* Involve a function which takes a single proof tree (potentially containing holes), and generates a list of proof trees "one level deeper", potentially including holes.
* Include a depth limit, after which the proof search is halted.
* Include a function to filter out proof trees based on whether they still contain holes, (and in the future other attributes such as whether the resulting weight is above a certain value).
* Involve a function that takes a list of prooftrees and returns a list of prooftrees "one level deeper", making use of the function which takes a single proof tree as input.

|*)

Definition toProofTreeWithHole (a : actor) (c : claim) := hole (\by a \in c).

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
      | _ => []
      end
    ++
    (** Rules that can be applied to any claim, use with caution, can cause performance issues. *)
    [
      (bot_elim a c (assume eB a _|_))
    ]
  end.

Close Scope beq_scope.

Eval compute in proofStepExample1 (\by a1 \in (C /\' C)).

Fixpoint oneLevelDeeper (step : forall j : judgementPart, list (proofTreeOf j)) (j : judgementPart) (p : proofTreeOf j)
  : list (proofTreeOf j) :=
match p with
| hole j => step j
| assume e a c => [(assume e a c)]
| bot_elim a C M => map (bot_elim a C) (oneLevelDeeper step _ M)
| and_intro a C1 C2 L R => 
    map (fun L2 => and_intro a C1 C2 L2 R) (oneLevelDeeper step _ L)
    ++ map (and_intro a C1 C2 L) (oneLevelDeeper step _ R)
| or_intro1 a C1 C2 M =>
    map (or_intro1 a C1 C2) (oneLevelDeeper step _ M)
| or_intro2 a C1 C2 M =>
    map (or_intro2 a C1 C2) (oneLevelDeeper step _ M)
| trust a1 a2 C name L =>
    map (trust a1 a2 C name) (oneLevelDeeper step _ L)
end
.

Definition oneLevelDeeperOfList step j (l : list (proofTreeOf j)) : list (proofTreeOf j) :=
 removeDups (flat_map (oneLevelDeeper step j) l).

Open Scope list_scope.

Fixpoint noHoles {j : judgementPart} (p : proofTreeOf j) : bool :=
  match p with
| hole j => false
| assume e a C => true
| bot_elim a C M => noHoles M
| and_intro a C1 C2 L R => noHoles L && noHoles R
| or_intro1 a C1 C2 M => noHoles M
| or_intro2 a C1 C2 M => noHoles M
| trust a1 a2 C name L => noHoles L
end
.

Fixpoint proofSearch (d : nat) step (j : judgementPart) (l : list (proofTreeOf j))  : list (proofTreeOf j) := 
  match d with
  | 0 => []
  | S d' => let newL := removeDups (oneLevelDeeperOfList step j l) in (filter noHoles newL) ++ proofSearch d' step j (filter (fun p => negb (noHoles p)) newL) 
  end.

Open Scope beq_scope.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Timeout 20 Eval vm_compute in 
  (showListOfProofTrees
    (removeDups (proofSearch 4 proofStepExample1 _  
        [toProofTreeWithHole a1
          ((Implies _|_ C))]))).

(*|
.. coq::
|*)

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

(*|
.. coq:: unfold
   :class: coq-math
|*)

Timeout 20 Eval vm_compute in 
(showListOfProofTrees
  (removeDups
    (proofSearch 10 proofStepExample2 _
      [toProofTreeWithHole a1
         ((C /\' C) /\' (C /\' C))]))).

(*|
.. coq::
|*)

End VeracityLogic.

(*|
*The proofs on this page are rendered using MathJax which happens to require at least one explicit math command*. Hence: :math:`x`.
|*)