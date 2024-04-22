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
  | _eQ_
  | _eB_
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
  | Pair (e1 e2: evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (x : atomic_evid_name) (bx : evid).

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

Close Scope string.

(*|

The machinery for applying lambas
---------------------------------

|*)

Open Scope beq_scope.

(* Fixpoint MatchingFormat (e1 e2 : evid) :=
  match e1,e2 with
  | AtomicEvid _,AtomicEvid _ => True
  | Pair e1 e2,Pair e1' e2' => MatchingFormat e1 e1' /\ MatchingFormat e2 e2'
  | Left e,Left e' => MatchingFormat e e'
  | Right e,Right e' => MatchingFormat e e'
  | Lambda x bx,Lambda x' bx' => MatchingFormat x x' /\ MatchingFormat bx bx'
  | _,_ => False
  end. *)

(* Fixpoint matchingFormat (e1 e2 : evid) :=
  match e1,e2 with
  | AtomicEvid _,AtomicEvid _ => true
  | Pair e1 e2,Pair e1' e2' => matchingFormat e1 e1' && matchingFormat e2 e2'
  | Left e,Left e' => matchingFormat e e'
  | Right e,Right e' => matchingFormat e e'
  | Lambda x bx, Lambda x' bx' => matchingFormat x x' && matchingFormat bx bx'
  | _,_ => false
  end. *)

(* Lemma matchingFormat_bool_Prop_iff : forall e1 e2, MatchingFormat e1 e2 <-> matchingFormat e1 e2 = true.
Proof.
split.
 - revert e2. induction e1; induction e2; auto.
   + simpl in *. intros. apply andb_true_intro. destruct H.
      split.
      * apply IHe1_1. apply H.
      * apply IHe1_2. apply H0.
   + simpl in *. intros. apply IHe1. apply H.
   + simpl in *. intros. apply IHe1. apply H.
   + simpl in *. intros. apply andb_true_intro. destruct H.
      split.
          * apply IHe1_1. apply H.
          * apply IHe1_2. apply H0.
 - revert e2. induction e1; induction e2; simpl in *; (try discriminate); auto.
    + intros. apply andb_prop in H. destruct H. auto.
    + intros. apply andb_prop in H. destruct H. auto.
Qed. *)

(* Lemma matchingFormat_bool_to_Prop : forall e1 e2, matchingFormat e1 e2 = true -> MatchingFormat e1 e2.
Proof.
apply matchingFormat_bool_Prop_iff.
Qed. *)

(* Lemma matchingFormat_Prop_to_bool : forall e1 e2, MatchingFormat e1 e2 -> matchingFormat e1 e2 = true.
Proof.
apply matchingFormat_bool_Prop_iff.
Qed. *)

(* Program Fixpoint substitutions (x a : evid) (HMatching : MatchingFormat x a) (n : atomic_evid_name) : option atomic_evid_name :=
  match x,a with
  | AtomicEvid name,AtomicEvid name' => if n =? name then Some name' else None
  | Pair e1 e2,Pair e1' e2' => match substitutions e1 e1' _ n with
                               | Some name' => Some name'
                               | None => substitutions e2 e2' _ n
                               end
  | Left e,Left e' => substitutions e e' _ n
  | Right e,Right e' => substitutions e e' _ n
  | Lambda x bx,Lambda x' bx' => substitutions bx bx' _ n
  | _,_ => except _
  end
.
Next Obligation.
simpl in *. destruct HMatching. assumption.
Defined.
Next Obligation.
simpl in *. destruct HMatching. assumption.
Defined.
Next Obligation.
simpl in *. destruct HMatching. assumption.
Defined.
Next Obligation.
destruct x.
  - destruct a; try (simpl in *; contradiction).
    + eapply H3. split; reflexivity.
  - destruct a; try (simpl in *; contradiction).
    + eapply H. split; reflexivity.
  - destruct a; try (simpl in *; contradiction).
    + eapply H0. split; reflexivity.
  - destruct a; try (simpl in *; contradiction).
    + eapply H1. split; reflexivity.
  - destruct a; try (simpl in *; contradiction).
    + eapply H2. split; reflexivity.
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined.
Next Obligation.
repeat ((try split); (try (intros; unfold not; intros; destruct H; (try inversion H; try inversion H0)))).
Defined. *)

(* Fixpoint allAtomicEvidenceContainedBy (e : evid) : list evid := 
  match e with
  | AtomicEvid e => [AtomicEvid e] 
  | Pair e1 e2 => allAtomicEvidenceContainedBy e1 ++ allAtomicEvidenceContainedBy e2
  | Left e => allAtomicEvidenceContainedBy e
  | Right e => allAtomicEvidenceContainedBy e
  | Lambda x' bx' => allAtomicEvidenceContainedBy x' ++ allAtomicEvidenceContainedBy bx'
end. *)

Fixpoint contains {A} `{Beq A} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: tl => (x =? h) || contains x tl
  end.

(* Fixpoint shareAtLeastOneElement {A} `{Beq A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => false
  | h :: tl => contains h l2 || shareAtLeastOneElement tl l2
  end. *)

(* Definition noOverlappingAtomicEvidence e1 e2 : bool :=
  let l1 := allAtomicEvidenceContainedBy e1 in
  let l2 := allAtomicEvidenceContainedBy e2 in
  negb (shareAtLeastOneElement l1 l2). *)

Fixpoint notUsedInInnerLambda (x : atomic_evid_name) (bx : evid) : bool :=
match bx with
  | AtomicEvid _ => true
  | Pair e1 e2 => notUsedInInnerLambda x e1 && notUsedInInnerLambda x e2
  | Left e => notUsedInInnerLambda x e
  | Right e => notUsedInInnerLambda x e
  | Lambda x' bx' => (negb (x =? x')) && notUsedInInnerLambda x bx'
end.

Program Fixpoint apply_lambda (x : atomic_evid_name) (bx : evid) (a : evid) (H2 : notUsedInInnerLambda x bx = true) : evid := 
  match bx with
  | AtomicEvid name => if name =? x then a else AtomicEvid name
  | Pair e1 e2 => Pair (apply_lambda x e1 a _) (apply_lambda x e2 a _)
  | Left e => (apply_lambda x e a _)
  | Right e => (apply_lambda x e a _)
  | Lambda x' bx' => Lambda x' (apply_lambda x bx' a _)
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

The central inductive definition of valid proof trees
-----------------------------------------------------

|*)

Inductive proofTreeOf : judgement -> Type :=
| assume e a c : proofTreeOf ((AtomicEvid e) \by a \in c)

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

| trust e a1 a2 C (name : trustRelation)

(L: proofTreeOf (e \by a2 \in C))
                          :
            proofTreeOf (e \by a1 \in C)

| impl_intro (x : atomic_evid_name) (bx : evid) a (C1 : claim) C2
                    (H : notUsedInInnerLambda x bx = true)

              (M: proofTreeOf (bx \by a \in C2))
                              :
   proofTreeOf ((Lambda x bx) \by a \in (Implies C1 C2))
| impl_elim x bx y a C1 C2
               (H1 : notUsedInInnerLambda x bx = true)                
                
(L: proofTreeOf ((Lambda x bx) \by a \in (Implies C1 C2)))
                           (R: proofTreeOf (y \by a \in C1))
                        :
    proofTreeOf ((apply_lambda x bx y H1) \by a \in C2)
.

Record proofTreeOf_wrapped (a : actor) (c : claim) := {
  _e : evid;
  _p : proofTreeOf (_e \by a \in c)
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
      | _eQ_ => "e_{?}"
      | _eB_ => "e_{\bot}"
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
      | _eQ_ =>  "unknown evidence"
      | _eB_ =>  "evidence for bottom"
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

Definition showForProofTree_atomic_as_variable (n : atomic_evid_name) :=
  match n with
  | _e_ => "x_{e}"
  | _e1_ => "x_{1}"
  | _e2_ => "x_{2}"
  | _e3_ => "x_{3}"
  | _e4_ => "x_{4}"
  | _eQ_ => "x_{?}"
  | _eB_ => "x_{\bot}"
  | _l_ => "x"
  | _s_ => "y"
  | _c_ => "z"
  | _belief_ => "x_{b}"
  | _testing_ => "x_{t}"
  | _audit_ => "x_{a}"
  | _compile_=> "x_{c}"
  | _review_=> "x_{r}"
  | _assess_ => "x_{assess}"
  | _business_procedure_ => "x_{p}"
  | _ingredients_percentage_list_ => "x_{PI}"
  | _breakdown_of_formulations_list_=> "x_{BF}"
    end.

Fixpoint showForProofTreeEvid (atomicAsVariables : list atomic_evid_name) e :=
  let showMaybeAsVariable l n :=
    if contains n l then showForProofTree_atomic_as_variable n else showForProofTree n in
  match e with
  | AtomicEvid name => showMaybeAsVariable atomicAsVariables name
  | Pair e1 e2 => "(" ++ (showForProofTreeEvid atomicAsVariables e1) ++ ", "
                      ++ (showForProofTreeEvid atomicAsVariables e2) ++ ")"
  | Left e => "i(" ++ showForProofTreeEvid atomicAsVariables e ++ ")"
  | Right e => "j(" ++ showForProofTreeEvid atomicAsVariables e ++ ")"
  | Lambda e1 e2 => "\lambda(" ++ showMaybeAsVariable (e1 :: atomicAsVariables) e1 ++ ")(" ++ showForProofTreeEvid (e1 :: atomicAsVariables) e2 ++ ")"
end.

Instance : ShowForProofTree evid := {
  showForProofTree := showForProofTreeEvid []
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

Definition showForProofTree_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : proofTreeOf j) :=
    match Ps with
      | [] => showForProofTree j
      | (h :: tl) as Ps => showForProofTree Ps ++ " \vdash_{" ++ showForProofTree Ts ++ "} " ++ (showForProofTree j)
    end.

Definition showForNaturalLanguage_judgement (Ps : list judgement) (Ts : list trustRelation) (j : judgement) (p : proofTreeOf j) :=
  match Ps with
    | [] => showForNaturalLanguage j
    | (h :: tl) as Ps => "Assuming " ++ showForNaturalLanguage Ps ++ " then " ++ showForNaturalLanguage j
  end.

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
| trust e a1 a2 C name L =>     name :: getAllTrustRelationsUsed _ L
| impl_intro _ _ _ _ _ _ M => getAllTrustRelationsUsed _ M
| impl_elim _ _ _ _ _ _ _ _ M => getAllTrustRelationsUsed _ M
end.

Fixpoint getAllEvidence (j : judgement) (p : proofTreeOf j)
  : list evid :=
match p with
| assume e a C => [(AtomicEvid e)]
| bot_elim e a C M => (getAllEvidence _ M)
| and_intro e1 e2 a C1 C2 L R => getAllEvidence _ L ++ getAllEvidence _ R 
| and_elim1 e1 e2 a C1 C2 M => getAllEvidence _ M
| and_elim2 e1 e2 a C1 C2 M => getAllEvidence _ M
| or_intro1 e1 a C1 C2 M => getAllEvidence _ M
| or_intro2 e2 a C1 C2 M => getAllEvidence _ M
| or_elim1 e1 a C1 C2 M => getAllEvidence _ M
| or_elim2 e2 a C1 C2 M => getAllEvidence _ M
| trust e a1 a2 C name L => getAllEvidence _ L| impl_intro _ _ _ _ _ _ M => getAllEvidence _ M
| impl_elim _ _ _ _ _ _ _ _ M => getAllEvidence _ M
end.

Definition isAtomicEvidence (e : evid) : bool :=
match e with
  | AtomicEvid _ => true
  | _ => false
end.

Fixpoint getAssumptions (j : judgement) (p : proofTreeOf j) : list judgement := 
match p with
| assume e a C => [(AtomicEvid e) \by a \in C]
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
| impl_intro e1 e2 a C1 C2 _ M => filter (fun j => negb (judgement_beq ((AtomicEvid e1) \by a \in C1) j)) (getAssumptions _ M)
| impl_elim _ _ _ _ _ _ _ L R => getAssumptions _ L ++ getAssumptions _ R
end.

Fixpoint removeDups {A} `{Beq A} (l : list A) : list A :=
    match l with
    | [] => []
    | h :: tl => if existsb (beq h) tl then removeDups tl else h :: removeDups tl
    end.

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
| impl_intro e1 e2 a C1 C2 H M => showForProofTree_proofTreeOf_helper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showForProofTree_judgement Ps Ts _ p
 ++ " $}"
| impl_elim x bx y a C1 C2 H1 L R => 
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
| impl_intro _ _ _ _ _ _ M => 
indent ++ showForNaturalLanguage_judgement Ps Ts _ p ++ ", because
" 
++ showForNaturalLanguage_proofTreeOf_helper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for implication."
| impl_elim _ _ _ _  _ _ _ L R => 
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
| impl_intro _ _ _ _ _ _ M => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication introduction
    " ++ indent ++ "- " ++ "Sub-proof:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ M
| impl_elim _ _ _ _  _ _ _ L R => 
indent ++ "- " ++ showForLogSeq_judgement Ps Ts ("  " ++ indent) _ p ++ "
  " ++ indent ++ "- " ++ "Logical rule used: implication elimination
    " ++ indent ++ "- " ++ "Sub-proofs:
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ L ++ "
" ++ showForLogSeq_proofTreeOf_helper ("      " ++ indent) _ R
end.

Open Scope string.

Fixpoint showForProofTree_list_newline {A} `{ShowForProofTree A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => showForProofTree h
    | h1 :: (h2 :: tl) as tl' => showForProofTree h1 ++ "
" ++ showForProofTree_list_newline tl'
  end.

Definition showForProofTree_proofTreeOf j p
  := "\begin{prooftree}" ++ showForProofTree_proofTreeOf_helper j p
       ++ "\end{prooftree}".
Instance showForProofTree_proofTreeOf_instance (j : judgement)
  : ShowForProofTree (proofTreeOf j) := { showForProofTree := showForProofTree_proofTreeOf j}.

Definition showForNaturalLanguage_proofTreeOf j (p : proofTreeOf j) := "

" ++ showForNaturalLanguage_proofTreeOf_helper "- " j p ++ "

".
Instance showForNaturalLanguage_proofTreeOf_instance (j : judgement)
  : ShowForNaturalLanguage (proofTreeOf j) := { showForNaturalLanguage := showForNaturalLanguage_proofTreeOf j}.

Definition printProofTitle j :=
match j with
| Judgement e a c => "### Veracity proof that " ++ showForLogSeq c ++ " is held by " ++ showForLogSeq a ++ " by the evidence " ++ showForLogSeq e
end.

Instance : ShowForLogSeq string := { showForLogSeq := id}.

Definition showForLogSeq_proofTreeOf j (p : proofTreeOf j) := 
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

Definition eB := AtomicEvid  _eB_.

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

Definition process_example : proofTreeOf_wrapped P (c3 ->' (c2 ->' (c1 ->' (c1 /\' c2 /\' c3)))).
Proof.
eexists  _.
eapply (impl_intro _c_ _ _ _ _ _).
eapply (impl_intro _s_ _ _ _ _ _).
eapply (impl_intro _l_ _ _ _ _ _).
eapply and_intro.
eapply and_intro.
eapply (assume _l_).
eapply (assume _s_).
eapply (assume _c_).
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
eexists _.
eapply (impl_intro _e1_ _ _ _ _ _).
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

Definition impl_intro_elim : proofTreeOf_wrapped a1 (c1).
eexists _.
eapply (impl_elim _e1_ _ e2 a1 C1 C1).
eapply (impl_intro _e1_ _ _ _ _ _).
eapply (assume _e1_).
eapply (assume _e2_).
Unshelve.
all: reflexivity.
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

Definition impl_intro_elim2 : proofTreeOf_wrapped a1 (c1).
eexists _.
eapply (impl_elim _ _ {{e1,e2}} a1 (C1 /\' C2) C1).
Fail eapply (impl_intro {{e3,e4}} _ _ _ _ _).
(* eapply (and_elim1 _ _ _ _ C2).
eapply and_intro.
eapply (assume _e3_).
eapply (assume _e4_).
eapply and_intro.
eapply (assume).
eapply (assume).
Unshelve.
all: reflexivity.
Defined. *)
Abort.
    
(*|
.. coq:: unfold
   :class: coq-math
|*)

(* Eval compute in (showForProofTree impl_intro_elim2). *)

(*|
.. coq::
|*)

(* Eval compute in (showForNaturalLanguage impl_intro_elim2).
Eval compute in (showForLogSeq impl_intro_elim2). *)

Definition impl_intro_elim3 : proofTreeOf_wrapped a1 (c1 ->' c1).
eexists _.
Fail eassert (apply_lambda {{e4,e2}} (Lambda e3 (Lambda e1 e1)) {{e3,e4}} _ _ = Lambda e3 (Lambda e1 e1)).
(* reflexivity.
Unshelve.
3,4: reflexivity.
eapply (impl_elim _e3_ (Lambda e1 e1) e2 a1 C3 (C1 ->' C1)).
rewrite <- H.
eapply impl_elim.
eapply (impl_intro _ _ _ _ _ _).
eapply (impl_intro _ _ _ _ _ _).
eapply (impl_intro _ _ _ _ _ _).
eapply assume.
eapply and_intro.
eapply assume.
eapply assume.
eapply assume.
Unshelve.
all: try reflexivity.
eapply C2.
eapply C2.
Defined. *)
Abort.

(*|
.. coq:: unfold
   :class: coq-math
|*)

(* Eval compute in (showForProofTree impl_intro_elim3). *)

(*|
.. coq::
|*)

(* Eval compute in (showForNaturalLanguage impl_intro_elim3). *)
(* Eval compute in (showForLogSeq impl_intro_elim3). *)


Definition impl_intro_elim4_problematic : proofTreeOf_wrapped a1 (Implies (C1 /\' C2) C1).
eexists _.
Fail eapply (impl_intro (Left(Left(e3))) _ _ _ _ _).
(* eapply (and_elim1 _ _ _ _ C2).
eapply and_intro.
eapply (assume _e3_).
eapply (assume _e4_).
Unshelve.
all: reflexivity.
Defined. *)
Abort.
    
(*|
.. coq:: unfold
   :class: coq-math
|*)

(* Eval compute in (showForProofTree impl_intro_elim4_problematic). *)

(*|
.. coq::
|*)

(* Eval compute in (showForNaturalLanguage impl_intro_elim4_problematic). *)
(* Eval compute in (showForLogSeq impl_intro_elim4_problematic). *)


Definition impl_intro2 : proofTreeOf_wrapped a1 (Implies c1 (Implies c1 c1)).
eexists  _.
eapply (impl_intro _e1_ _ _ _ _ _).
eapply (impl_intro _e2_ _ _ _ _ _).
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
eexists _.
  eapply (impl_intro _e1_ _ _ _ _ _).
  eapply (impl_intro _e2_ _ _ _ _ _).
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
eexists  _.
eapply (impl_intro _e1_ _ _ _ _ _ ).
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

Program Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf ({{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3)).
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
proofTreeOf {{{{l, s}},c}} \by P \in (C1 /\' C2 /\' C3).
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
proofTreeOf e \by a1 \in (c1).
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

Program Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
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


Definition exampleWithProofOf : proofTreeOf_wrapped a1 C1.
Proof.
eexists _.
apply (assume _e_ a1).
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

Definition usingMost : proofTreeOf_wrapped a1 (C1 \/' (C2 /\' (Implies C4 C4)) \/' C3).
Proof.
eexists _.
eapply (or_intro1 _).
eapply (or_intro2 _).
eapply and_intro.
apply (assume _e_ a1).
eapply (trust _ _ _ _ trustT).
eapply (impl_intro _e4_ _ a1 C4 C4 _).
apply (assume _e4_ a1).
Unshelve.
Show Proof.
all: reflexivity.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree usingMost.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage usingMost.
Eval compute in showForLogSeq usingMost.

Definition bot_example : proofTreeOf_wrapped a1 (_|_ ->' (C1 /\' C2)).
Proof.
eexists _.
eapply (impl_intro _eB_ _ a1 _ _ _).
apply bot_elim.
apply (assume _eB_).
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
eexists _.
eapply (impl_intro _eB_ _ a1 _ _ _).
apply bot_elim.
apply (assume _eB_).
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

Definition abstraction_example1 : proofTreeOf_wrapped a1 c1.
Proof.
eexists _.
eapply (impl_elim _ _ _ a1 (C1 \/' C2) C1).
Fail eapply (impl_intro (Left e2) _ _ _ _ _).
(* apply (assume _e2_).
eapply (or_intro1).
apply (assume _e1_).
Unshelve.
all: reflexivity.
Defined. *)
Abort.
 
(*|
.. coq:: unfold
   :class: coq-math
|*)


(* Eval compute in showForProofTree abstraction_example1. *)

(*|
.. coq::
|*)

(* Eval compute in showForNaturalLanguage abstraction_example1. *)
(* Eval compute in showForLogSeq abstraction_example1. *)

Definition abstraction_example2 : proofTreeOf_wrapped a1 c1.
Proof.
eexists _.
eapply (impl_elim _ _ _ a1 (C1 /\' C2) C1).
eapply (impl_intro _e2_ _ _ _ _ _).
apply (assume _e2_).
eapply (and_intro).
apply (assume _e1_).
apply (assume _e2_).
Unshelve.
all: reflexivity.
Defined.
 
(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in showForProofTree abstraction_example2.

(*|
.. coq::
|*)

Eval compute in showForNaturalLanguage abstraction_example2.
Eval compute in showForLogSeq abstraction_example2.


End VeracityLogic.

(*|
*The proofs on this page are rendered using MathJax which happens to require at least one explicit math command*. Hence: :math:`x`.
|*)