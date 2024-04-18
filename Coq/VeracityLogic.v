(*|
Veracity Logic Mechanised in Coq
================================

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
  | _c_
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

Inductive function_name :=
  | _f_
  | _g_
  | _h_
  | _u_
  | _v_
  | _w_
  | _b_
.

Scheme Equality for function_name.

(*|

Types of aspecs of the veracity logic
-------------------------------------

|*)

Inductive claim :=
  | AtomicClaim (n : claim_name)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Scheme Equality for claim.

Inductive evid :=
  | AtomicEvid (n : atomic_evid_name)
  | BotEvid
  | BotEvidApplied (e1 : evid)
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (n : function_name) (e1 e2 : evid) (c1 c2 : claim).

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

Inductive partialFDef :=
  FDef : function_name -> evid -> evid -> claim -> claim -> partialFDef.

Scheme Equality for partialFDef.

Notation "E \by A \in C" := (Judgement E A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Infix "->'" := Implies (at level 99, right associativity).
Notation "_|_" := (Bottom) (at level 1).
Notation "{{ x , y , .. , z }}" := (Pair .. (Pair x y) .. z).

(*|

Boolean Equality Typeclass
--------------------------

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
Instance : Beq function_name := { beq := function_name_beq }.
Instance : Beq partialFDef := { beq := partialFDef_beq }.

(*|

Helper functions for lightweight type-checking
----------------------------------------------

|*)

Open Scope beq_scope.

Definition eqFunction d d' :=
  match d,d' with
  FDef n _ _ _ _,FDef n' _ _ _ _ => (n =? n')
  end.

Definition eqTypes d d' :=
  match d,d' with
  FDef _ _ _ C1 C2,FDef _ _ _ C1' C2' => (C1 =? C1') && (C2 =? C2')
  end.

Fixpoint contains (x : partialFDef) (l : list partialFDef) : bool :=
  match l with
  | [] => false
  | h :: tl => (x =? h) || contains x tl
  end.

Fixpoint containsMatchingEvidArgument (x : partialFDef) (l : list partialFDef) : bool :=
  match l with
  | [] => false
  | h :: tl =>
    match x,h with
    | FDef n e _ _ _,FDef n' e' _ _ _ => (n =? n') && (e =? e') || containsMatchingEvidArgument x tl
    end
  end.

Fixpoint containsMatchingType (x : partialFDef) (l : list partialFDef) : bool :=
  match l with
  | [] => false
  | h :: tl =>
    match x,h with
    | FDef n _ _ C1 C2,FDef n' _ _ C1' C2' => (n =? n') && (C1 =? C1') && (C2 =? C2') || containsMatchingType x tl
    end
  end.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
    match l with
    | [] => []
    | h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
    end.

Fixpoint inconsitentTypes (l : list partialFDef) : list partialFDef :=
  match l with
  | [] => []
  | h :: tl => removeDups (filter (fun d' => negb (eqTypes h d')) (filter (eqFunction h) l) ++ inconsitentTypes tl)
  end.

Fixpoint keepOnlyDuplicates_helper (l : list partialFDef) (seenOnce : list partialFDef) (seenMultiple : list partialFDef) : list partialFDef :=
  match l with
  | [] => seenMultiple
  | h :: tl => if containsMatchingEvidArgument h seenOnce then keepOnlyDuplicates_helper tl seenOnce (h :: seenMultiple)
          else keepOnlyDuplicates_helper tl (h :: seenOnce) seenMultiple
  end.
  
Definition keepOnlyDuplicates l := keepOnlyDuplicates_helper l [] [].

Hint Unfold keepOnlyDuplicates : veracityPrf.
Hint Unfold keepOnlyDuplicates_helper : veracityPrf.
Hint Unfold containsMatchingEvidArgument : veracityPrf.

Close Scope string.

(*|

The central inductive definition of valid proof trees
-----------------------------------------------------

|*)

Inductive proofTreeOf {fDef : (list partialFDef)} {HFDefValid : (keepOnlyDuplicates fDef) ++ (inconsitentTypes fDef) = []} : judgement -> Type :=
| assume e a c : proofTreeOf ((AtomicEvid e) \by a \in c)
| and_intro e1 e2 a C1 C2

(L: proofTreeOf (e1 \by a \in C1))
                           (R: proofTreeOf (e2 \by a \in C2))
                        :
    proofTreeOf ({{e1, e2}} \by a \in (C1 /\' C2))

| or_intro1 e1 a C1 C2

           (M: proofTreeOf (e1 \by a \in C1))
                          :
    proofTreeOf ((Left e1) \by a \in (C1 \/' C2))

| or_intro2 e2 a C1 C2

           (M: proofTreeOf (e2 \by a \in C2))
                          :
    proofTreeOf ((Right e2) \by a \in (C1 \/' C2))

| trust e a1 a2 C (name : trustRelation)

(L: proofTreeOf (e \by a2 \in C))
                          :
            proofTreeOf (e \by a1 \in C)

| impl_intro (e1 : evid) e2 a (C1 : claim) C2 n
             (H : contains (FDef n e1 e2 C1 C2) fDef = true)

              (M: proofTreeOf (e2 \by a \in C2))
                              :
   proofTreeOf ((Lambda n e1 e2 C1 C2) \by a \in (Implies C1 C2))
.

Record proofTreeOf_wrapped (a : actor) (c : claim) := {
  _f : list partialFDef;
  _fDef : _;
  _e : evid;
  _p : @proofTreeOf _f _fDef (_e \by a \in c)
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
      | _c_ => "c"
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
      | _c_ => "atomic evidence c"
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

Instance : ShowForProofTree function_name := { 
  showForProofTree n := 
    match n with
      | _f_ => "f"
      | _g_ => "g"
      | _h_ => "h"
      | _u_ => "u"
      | _v_ => "v"
      | _w_ => "w"
      | _b_ => "b"
    end
  }.
Instance : ShowForNaturalLanguage function_name := {showForNaturalLanguage := showForProofTree}.
Instance : ShowForLogSeq function_name := {showForLogSeq := showForProofTree}.

Instance : ShowForProofTree evid := {
  showForProofTree :=
  fix showForProofTreeEvid e :=
      match e with
      | AtomicEvid name => showForProofTree name
      | Pair e1 e2 => "(" ++ (showForProofTreeEvid e1) ++ ", "
                          ++ (showForProofTreeEvid e2) ++ ")"
      | Left e => "i(" ++ showForProofTreeEvid e ++ ")"
      | Right e => "j(" ++ showForProofTreeEvid e ++ ")"
      | Lambda f e1 e2 _ _ => "(\lambda " ++ showForProofTree f ++ ")"
      | BotEvid => "e_{\bot}"
      | BotEvidApplied e => "R_{0}(" ++ showForProofTreeEvid e ++ ")"
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

Definition showForProofTree_judgement {fDef HFDef} (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : @proofTreeOf fDef HFDef j) :=
    match Ps with
      | [] => showForProofTree j
      | (h :: tl) as Ps => showForProofTree Ps ++ " \vdash_{" ++ showForProofTree Ts ++ "} " ++ (showForProofTree j)
    end.

Definition showForNaturalLanguage_judgement {fDef HFDef} (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : @proofTreeOf fDef HFDef j) :=
  match Ps with
    | [] => showForNaturalLanguage j
    | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage j
  end.

Definition showForLogSeq_judgement {fDef HFDef} (Ps : list judgement) (Ts : list trustRelation) (indent : string) (j : judgement) (p : @proofTreeOf fDef HFDef j) :=
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

Fixpoint getAllTrustRelationsUsed {fDef HFDef} (j : judgement) (p : @proofTreeOf fDef HFDef j)
  : list trustRelation :=
match p with
| assume e a C => []
| and_intro e1 e2 a C1 C2 L R => 
    getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
| or_intro1 e1  a C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 e2 a C1 C2 M => getAllTrustRelationsUsed _ M
| trust e a1 a2 C name L => 
    name :: getAllTrustRelationsUsed _ L
| impl_intro _ _ _ _ _ _ _ M => getAllTrustRelationsUsed _ M
end.

Fixpoint getAllEvidence {fDef HFDef} (j : judgement) (p : @proofTreeOf fDef HFDef j)
  : list evid :=
match p with
| assume e a C => [(AtomicEvid e)]
| and_intro e1 e2 a C1 C2 L R => getAllEvidence _ L ++ getAllEvidence _ R 
| or_intro1 e1 a C1 C2 M => getAllEvidence _ M
| or_intro2 e2 a C1 C2 M => getAllEvidence _ M
| trust e a1 a2 C name L => getAllEvidence _ L
| impl_intro _ _ _ _ _ _ _ M => getAllEvidence _ M
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Fixpoint getAssumptions {fDef HFDef} (j : judgement) (p : @proofTreeOf fDef HFDef j) : list judgement := 
match p with
| assume e a C => [(AtomicEvid e) \by a \in C]
| and_intro e1 e2 a C1 C2 L R => 
    getAssumptions _ L ++ getAssumptions _ R 
| or_intro1 e1 a C1 C2 M => getAssumptions _ M
| or_intro2 e2 a C1 C2 M => getAssumptions _ M
| trust e a1 a2 C name L => 
    getAssumptions _ L
| impl_intro e1 e2 a C1 C2 _ _ M => filter (fun j => negb (judgement_beq (e1 \by a \in C1) j)) (getAssumptions _ M)
end.

Fixpoint showForProofTree_proofTreeOf_helper {fDef HFDef} (j : judgement) (p : @proofTreeOf fDef HFDef j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| assume e a C => "\AxiomC{$ " 
             ++ showForProofTree C 
             ++ " \textit{ is a veracity claim} $}"
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| and_intro e1 e2 a C1 C2 L R => 
    showForProofTree_proofTreeOf_helper _ L
 ++ showForProofTree_proofTreeOf_helper _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| or_intro1 e1 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| or_intro2 e2 a C1 C2 M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
 | trust e a1 a2 C name L => 
    showForProofTree_proofTreeOf_helper _ L
 ++ " \AxiomC{$" ++ showForProofTree a1 ++ showForProofTree name ++ showForProofTree a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ showForProofTree name
 ++ "$} \BinaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p ++ " $}"
| impl_intro e1 e2 a C1 C2 n H M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
end.

Fixpoint showForNaturalLanguage_proofTreeOf_helper {fDef HFDef} (indent : string) (j : judgement) (p : @proofTreeOf fDef HFDef j)
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
| and_intro e1 e2 a C1 C2 L R => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ R ++ "
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
| trust e a1 a2 C name L => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ L ++ "
"
++ indent ++ "by the trust relation " ++ showForNaturalLanguage name ++ "."
| impl_intro _ _ _ _ _ _ _ M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for implication."
end.

Fixpoint showForLogSeq_proofTreeOf_helper {fDef HFDef} (indent : string) (j : judgement) (p : @proofTreeOf fDef HFDef j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| assume e a C => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: we assume this"
| and_intro e1 e2 a C1 C2 L R => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: and introduction
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ R
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
| trust e a1 a2 C name L => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: trust, with relation " ++ showForLogSeq name ++ "
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L
| impl_intro _ _ _ _ _ _ _ M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication introduction
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
end.

Open Scope string.

Fixpoint showForProofTree_list_newline {A} `{ShowForProofTree A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => showForProofTree h
    | h1 :: (h2 :: tl) as tl' => showForProofTree h1 ++ "
" ++ showForProofTree_list_newline tl'
  end.


Instance : ShowForProofTree partialFDef := {
  showForProofTree f := match f with
    | FDef f e1 e2 C1 C2 => 
    showForProofTree f ++ "(" ++ showForProofTree e1 ++ ") = " ++ showForProofTree e2 ++ "\text{ where }" ++ showForProofTree f ++ "\text{ has type }" ++ showForProofTree C1 ++ "\text{ to }"  ++ showForProofTree C2
    end
}.

Definition showForProofTree_proofTreeOf fDef HFDef j p
  := "\begin{prooftree}" ++ @showForProofTree_proofTreeOf_helper fDef HFDef j p
       ++ "\end{prooftree}" ++ if Nat.eqb (Datatypes.length fDef) 0 then "" else "
Functions:
" ++ showForProofTree_list_newline fDef.
Instance showForProofTree_proofTreeOf_instance fDef HFDef (j : judgement)
  : ShowForProofTree (proofTreeOf j) := { showForProofTree := @showForProofTree_proofTreeOf fDef HFDef j}.

Definition showForNaturalLanguage_proofTreeOf {fDef HFDef} j (p : @proofTreeOf fDef HFDef j) := "

" ++ showForNaturalLanguage_proofTreeOf_helper "- " j p ++ "

".
Instance showForNaturalLanguage_proofTreeOf_instance {fDef HFDef} (j : judgement)
  : ShowForNaturalLanguage (@proofTreeOf fDef HFDef j) := { showForNaturalLanguage := showForNaturalLanguage_proofTreeOf j}.

Definition printProofTitle j :=
match j with
| Judgement e a c => "### Veracity proof that " ++ showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence " ++ showForLogSeq e
end.

Instance : ShowForLogSeq string := { showForLogSeq := id}.

Definition showForLogSeq_proofTreeOf {fDef HFDef} j (p : @proofTreeOf fDef HFDef j) := 
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
Instance showForLogSeq_proofTreeOf_instance {fDef HFDef} (j : judgement)
  : ShowForLogSeq (@proofTreeOf fDef HFDef j) := { showForLogSeq := showForLogSeq_proofTreeOf j}.

Fixpoint showListOfProofTrees {fDef HFDef} {j : judgement} (l : list (@proofTreeOf fDef HFDef j)) :=
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
    
Ltac validateFDef :=
  try (intros; simpl; autounfold with veracityPrf; simpl; reflexivity);
  try (simpl; reflexivity).

(*|

Examples
--------

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

Definition l := AtomicEvid _l_ .
Definition s := AtomicEvid _s_.
Definition c := AtomicEvid _c_.
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

Eval compute in showForProofTree_judgement [(e1 \by a1 \in c1)] [] (e1 \by a1 \in c1) (assume _e1_ a1 c1).

Definition process_example : proofTreeOf_wrapped a1 (c3 ->' (c2 ->' (c1 ->' (c1 /\' c2 /\' c3)))).
Proof.
eexists [
  FDef _h_ l {{l, s, c}} c1 (c1 /\' c2 /\' c3);
  FDef _g_ s (Lambda _h_ l {{l, s, c}} c1 (c1 /\' c2 /\' c3)) c2 (c1 ->' c1 /\' c2 /\' c3);
  FDef _f_ c (Lambda _g_ s (Lambda _h_ l {{l, s, c}} c1 (c1 /\' c2 /\' c3)) c2 (c1 ->' c1 /\' c2 /\' c3)) c3 (c2 ->' c1 ->' c1 /\' c2 /\' c3)
] _ _.
eapply (impl_intro c _ _ _ _ _f_ _).
eapply (impl_intro s _ _ _ _ _g_ _).
eapply (impl_intro l _ _ _ _ _h_ _).
eapply and_intro.
eapply and_intro.
eapply (assume _l_).
eapply (assume _s_).
eapply (assume _c_).
Unshelve.
all: try reflexivity.
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
eexists [FDef _f_ e1 e1 c1 c1] _ _.
eapply (impl_intro e1 _ _ _ _ _f_ _).
eapply (assume _e1_).
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
    
Definition impl_intro2 : proofTreeOf_wrapped a1 (Implies c1 (Implies c1 c1)).
eexists [FDef _f_ e1 (Lambda _g_ e1 e1 c1 c1) c1 (Implies c1 c1); FDef _g_ e1 e1 c1 c1] _ _.
eapply (impl_intro e1 _ _ _ _ _f_ _).
eapply (impl_intro e1 _ _ _ _ _g_ _).
eapply (assume _e1_).
Unshelve.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_intro2).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_intro2).
Eval compute in (showForLogSeq impl_intro2).

Definition impl_and : proofTreeOf_wrapped a1 (Implies c1 (Implies c2 c1)).
eexists [
  FDef _g_ e2 e1 c2 c1;
  FDef _f_ e1 (Lambda _g_ e2 e1 c2 c1) c1 (Implies c2 c1)
] _ _.
  eapply (impl_intro e1 _ _ _ _ _f_ _).
  eapply (impl_intro e2 _ _ _ _ _g_ _).
  eapply (assume _e1_).
  Unshelve.
  all: try reflexivity.
Defined.
    

(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in (showForProofTree impl_and).

(*|
.. coq::
|*)

Eval compute in (showForNaturalLanguage impl_and).
Eval compute in (showForLogSeq impl_and).

Definition and_example : proofTreeOf_wrapped a1 (Implies c1 (c1 /\' c1)).
eexists [FDef _f_ e1 {{e1, e1}} c1 (c1 /\' c1)] _ _.
eapply (impl_intro e1 _ _ _ _ _f_ _ ).
eapply (and_intro).
eapply (assume _e1_).
eapply (assume _e1_).
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

Program Definition concreteProofTreeExampleWith2Conjuncts : 
@proofTreeOf [] _ ({{l, s}} \by P \in (C1 /\' C2)).
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

Program Definition concreteProofTreeExampleWith3Conjuncts : 
@proofTreeOf [] _ ({{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3)).
apply and_intro.
apply and_intro.
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
@proofTreeOf [] _ {{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3).
apply and_intro.
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
@proofTreeOf [] _ e \by a1 \in (c1).
eapply (trust _ a1 a2 c1 trustT).
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
@proofTreeOf [] _ {{{{l, s}},c}} \by Q \in (C1 /\' C2 /\' C3).
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

Program Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
@proofTreeOf [] _ {{{{l, s}},c}} \by Q \in (C1 /\' C2 /\' C3).
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


Definition exampleWithProofOf : proofTreeOf_wrapped a1 C1.
Proof.
eexists [] _ _.
apply (assume _e_ a1).
Unshelve.
reflexivity.
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

Definition usingAll : proofTreeOf_wrapped a1 (C1 \/' (C2 /\' (Implies C4 C4)) \/' C3).
Proof.
eexists [FDef _f_ e4 e4 C4 C4] _ _.
eapply (or_intro1 _).
eapply (or_intro2 _).
eapply and_intro.
apply (assume _e_ a1).
eapply (trust _ _ _ _ trustT).
eapply (impl_intro e4 _ a1 C4 C4 _f_ _).
apply (assume _e4_ a1).
Unshelve.
Show Proof.
all: reflexivity.
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

End VeracityLogic.

(*|
*The proofs on this page are rendered using MathJax which happens to require at least one explicit math command*. Hence: :math:`x`.
|*)