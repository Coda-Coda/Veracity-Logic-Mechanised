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

Inductive namePair :=
  | NamePair (short long : string).

Inductive evid :=
  | AtomicEvid (name : namePair)
  | Pair (e1 e2 : evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2 : evid)
  | Apply (e1 e2 : evid).

Inductive claim :=
  | AtomicClaim (name : namePair)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Inductive actor :=
  | Actor (s : namePair).

Inductive singleJudgement :=
  | SingleJudgement (e : evid) (a : actor) (c: claim).

(*|

Judgements are a list of **single** judgements entailing some single judgement, or state that some claim :coq:`c` is a veracity claim.

|*)

Inductive judgement :=
  | Entail (s : singleJudgement)
  | IsAVeracityClaim (c : claim).

(*|
Next, we introduce some notation for Coq.
|*)

Notation "||- S" := (Entail S) (at level 3).
Notation "E \by A \in C" := (SingleJudgement E A C) (at level 2).
Infix "/\'" := And (at level 81, left associativity).
Infix "\/'" := Or (at level 86, left associativity). 
Notation "_|_" := (Bottom) (at level 1).
Notation "( x , y , .. , z )" := (Pair .. (Pair x y) .. z).

(*|

We define a tagged type representing a trust relation.

|*)

Inductive trustRelationInfo :=
  | Trust (name : namePair).

(*|

And we define equality for the tagged type.

|*)

Class Beq A : Type :=
  {
    beq : A -> A -> bool
  }.

Instance : Beq string := { beq := String.eqb }.

Definition beqNamePair (n1 n2 : namePair) : bool :=
match n1,n2 with
| NamePair short1 long1,NamePair short2 long2 => beq short1 short2 && beq long1 long2
end.
Instance : Beq namePair := { beq := beqNamePair }.

Definition beqTrust (t1 t2 : trustRelationInfo) : bool :=
match t1,t2 with
| Trust name1,Trust name2 => beq name1 name2
end.
Instance : Beq trustRelationInfo := { beq := beqTrust }.

Definition beqActor (a1 a2 : actor) : bool :=
match a1,a2 with
| Actor name1,Actor name2 => beq name1 name2
end.
Instance : Beq actor := { beq := beqActor }.

(* Inductive evid :=
  | AtomicEvid (name : string)
  | Pair (e1 e2 : evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2 : evid). *)

Fixpoint beqEvid (e1 e2 : evid) : bool :=
match e1,e2 with
| AtomicEvid name1,AtomicEvid name2 => beq name1 name2
| AtomicEvid name1,_ => false
| Pair e11 e12,Pair e21 e22 => beqEvid e11 e21 && beqEvid e12 e22
| Pair e11 e12,_ => false
| Left e11,Left e21 => beqEvid e11 e21
| Left e11,_ => false
| Right e11,Right e21 => beqEvid e11 e21
| Right e11,_ => false
| Lambda e11 e12,Lambda e21 e22 => beqEvid e11 e21 && beqEvid e12 e22
| Lambda e11 e12,_ => false
| Apply e11 e12,Apply e21 e22 => beqEvid e11 e21 && beqEvid e12 e22
| Apply e11 e12,_ => false
end.
Instance : Beq evid := { beq := beqEvid }.

(* Inductive claim :=
  | AtomicClaim (name : string)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim). *)

Fixpoint beqClaim (c1 c2 : claim) : bool :=
match c1,c2 with
| AtomicClaim name1,AtomicClaim name2 => beq name1 name2
| AtomicClaim name1,_ => false
| Bottom,Bottom => true
| Bottom,_ => false
| And c11 c12,And c21 c22 => beqClaim c11 c21 && beqClaim c12 c22
| And c11 c12,_ => false
| Or c11 c12,Or c21 c22 => beqClaim c11 c21 && beqClaim c12 c22
| Or c11 c12,_ => false
| Implies c11 c12,Implies c21 c22 => beqClaim c11 c21 && beqClaim c12 c22
| Implies c11 c12,_ => false
end
.
Instance : Beq claim := { beq := beqClaim }.

(* Inductive singleJudgement :=
  | SingleJudgement (e : evid) (a : actor) (c: claim). *)

Definition beqSingleJudgement (j1 j2 : singleJudgement) : bool :=
match j1,j2 with
SingleJudgement e1 a1 c1,SingleJudgement e2 a2 c2 => beq e1 e2 && beq a1 a2 && beq c1 c2
end.
Instance : Beq singleJudgement := { beq := beqSingleJudgement }.

(*|

For now, I have only implemented one inference rule, :coq:`and_intro`, as well as the :coq:`assume` rule and a rule :coq:`leaf` that declares that it is correct for a proof tree to stop on a statement such as :math:`C_1 \textit{ is a claim}`.

:coq:`proofTreeOf` is a data type, a tree, which depends on a judgement. The type :coq:`tree j` describes a tree which correctly proves :coq:`j`.

But this is not a proposition. This is best thought of as the datatype for (correct) proof trees.

The remaining rules will be easy to add, this will be done in 2024.

|*)

Inductive proofTreeOf : judgement -> Type :=
| admit p : proofTreeOf p
| leaf c : proofTreeOf (IsAVeracityClaim c)
| assume e a C

       (M : proofTreeOf (IsAVeracityClaim C)) 
                         :
  proofTreeOf ( ||- e \by a \in C)
| bot_elim e a C

        (M : proofTreeOf ( ||- (e \by a \in _|_)))
                           :
           proofTreeOf ( ||- (e \by a \in C))

| and_intro a e1 e2 C1 C2

(L: proofTreeOf ( ||- e1 \by a \in C1))
                           (R: proofTreeOf ( ||- e2 \by a \in C2))
                        :
    proofTreeOf ( ||- (e1, e2) \by a \in (C1 /\' C2))

| and_elim1 a e1 e2 C1 C2

    (M : proofTreeOf ( ||- ((e1, e2) \by a \in (C1 /\' C2))))
                           :
             proofTreeOf ( ||- (e1 \by a \in C1))

| and_elim2 a e1 e2 C1 C2

    (M : proofTreeOf ( ||- ((e1, e2) \by a \in (C1 /\' C2))))
                          :
        proofTreeOf ( ||- (e2 \by a \in C2))

| or_intro1 a e1 C1 C2

           (M: proofTreeOf ( ||- (e1 \by a \in C1)))
                          :
    proofTreeOf ( ||- ((Left e1) \by a \in (C1 \/' C2)))

| or_intro2 a e2 C1 C2

           (M: proofTreeOf ( ||- (e2 \by a \in C2)))
                          :
    proofTreeOf ( ||- ((Right e2) \by a \in (C1 \/' C2)))

| or_elim1 a e1 C1 C2

      (M: proofTreeOf ( ||- ((Left e1) \by a \in (C1 \/' C2))))
                          :
        proofTreeOf ( ||- (e1 \by a \in C1))

| or_elim2 a e2 C1 C2

      (M : proofTreeOf ( ||- ((Right e2) \by a \in (C1 \/' C2))))
                            :
          proofTreeOf ( ||- (e2 \by a \in C2))

| trust a1 a2 e C (name : trustRelationInfo)

(L: proofTreeOf ( ||- (e \by a2 \in C)))
                          :
            proofTreeOf ( ||- (e \by a1 \in C))

| impl_intro (e1 : evid) (C1 : claim) a e2 C2

(M: proofTreeOf
                      ( ||- (e2 \by a \in C2)))
                              :
proofTreeOf
              ( ||- ((Lambda e1 e2) \by a \in (Implies C1 C2)))

| impl_elim a e1 e2 C1 C2

(L: proofTreeOf ( ||- e1 \by a \in (Implies C1 C2)))
                           (R: proofTreeOf ( ||- e2 \by a \in C1))
                        :
    proofTreeOf ( ||- (Apply e1 e2) \by a \in C2)
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

Definition e := AtomicEvid (NamePair "e" "example evidence e").
Definition C := AtomicClaim (NamePair "C" "example evidence C").

Definition a1 := Actor (NamePair "a_{1}" "actor 1").
Definition e1 := AtomicEvid (NamePair "e_{1}" "example evidence 1").
Definition c1 := AtomicClaim (NamePair "c_{1}" "example claim 1").

Definition a2 := Actor (NamePair "a_{2}" "actor 2").
Definition e2 := AtomicEvid (NamePair "e_{2}" "example evidence 2").
Definition c2 := AtomicClaim (NamePair "c_{2}" "example claim 2").

Definition a3 := Actor (NamePair "a_{3}" "actor 3").
Definition e3 := AtomicEvid (NamePair "e_{3}" "example evidence 3").
Definition c3 := AtomicClaim (NamePair "c_{3}" "example claim 3").

Definition a4 := Actor (NamePair "a_{4}" "actor 4").
Definition e4 := AtomicEvid (NamePair "e_{4}" "example evidence 4").
Definition c4 := AtomicClaim (NamePair "c_{4}" "example claim 4").

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

Definition j1 := ||- e2 \by a2 \in c2.
Definition j2 := ||- e4 \by a4 \in c4.

(*|
Example use of notation:
|*)

Check ||- e1 \by a1 \in c1.
Check e1 \by a1 \in c1.
Check ||- e1 \by a1 \in c1.

(*|
Machinery for printing to LaTeX
-------------------------------
|*)

(*| We define and make use of the :coq:`show` typeclass, for simplicity. |*)
Class Show A : Type :=
  {
    show : A -> string
  }.

(*| We also define a typeclass for showing longer versions, used for the english-language output. |*)
Class ShowLong A : Type :=
  {
    showLong : A -> string
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
  | AtomicEvid (NamePair name _) => name
  | Pair e1 e2 => "(" ++ (showEvid e1) ++ ", "
                      ++ (showEvid e2) ++ ")"
  | Left e => "i(" ++ showEvid e ++ ")"
  | Right e => "j(" ++ showEvid e ++ ")"
  | Lambda e1 e2 => "(\lambda " ++ showEvid e1 ++ " \rightarrow "
                       ++ showEvid e2 ++ ")"
  | Apply e1 e2 => showEvid e1 ++ "(" ++ showEvid e2 ++ ")"
end.
Instance : Show evid := { show := showEvid }.
Instance : ShowLong evid := { showLong := showEvid }.

Fixpoint showClaim (c : claim) :=
match c with
  | AtomicClaim (NamePair name _) => name
  | Bottom => "\bot"
  | And c1 c2 => showClaim c1 ++ " \wedge " ++ showClaim c2
  | Or c1 c2 => showClaim c1 ++ " \vee " ++ showClaim c2
  | Implies c1 c2 => showClaim c1 ++ " \rightarrow " ++ showClaim c2
  end.
Instance : Show claim := { show := showClaim }.

Fixpoint showLongClaim (c : claim) :=
match c with
  | AtomicClaim (NamePair _ name) => name
  | Bottom => "impossible"
  | And c1 c2 => "(" ++ showLongClaim c1 ++ " and " ++ showLongClaim c2  ++ ")"
  | Or c1 c2 => "(" ++ showLongClaim c1 ++ " or " ++ showLongClaim c2 ++ ")"
  | Implies c1 c2 => "(" ++ showLongClaim c1 ++ " implies " ++ showLongClaim c2 ++ ")"
  end.
Instance : ShowLong claim := { showLong := showLongClaim }.

Definition showActor (a : actor) := 
  match a with
    | Actor (NamePair s _) => s 
  end.
Instance : Show actor := { show := showActor }.

Definition showLongActor (a : actor) := 
  match a with
    | Actor (NamePair _ s) => s 
  end.
Instance : ShowLong actor := { showLong := showLongActor }.

Definition showTrustRelationInfo (t : trustRelationInfo) := 
  match t with
    | Trust (NamePair name _) => name
  end.
Instance : Show trustRelationInfo := { show := showTrustRelationInfo }.

Definition showLongTrustRelationInfo (t : trustRelationInfo) := 
  match t with
    | Trust (NamePair _ name) => name
  end.
Instance : ShowLong trustRelationInfo := { showLong := showLongTrustRelationInfo }.

Fixpoint showList {A} `{Show A} (l : list A) :=
  match l with
    | [] => ""
    | [h] => show h
    | h1 :: (h2 :: tl) as tl' => show h1 ++ ", " ++ showList tl'
  end.
Instance showListInstance {A : Type} `{Show A} : Show (list A) 
  := { show l := showList l}.

(* This approach gives us the Oxford comma, which is OK. *)
Fixpoint showLongList {A} `{ShowLong A} (l : list A) :=
  match l with
    | [] => "no items"
    | [h] => showLong h
    | h1 :: (h2 :: tl) as tl' => showLong h1 ++ ", " ++ showLongList tl'
  end.
Instance showLongListInstance {A : Type} `{ShowLong A} : ShowLong (list A) 
  := { showLong l := showLongList l}.

Definition showSingleJudgement (s : singleJudgement) := 
  match s with
    | SingleJudgement e a c => show e ++ "^{" ++ show a ++ "} \in "
                                 ++ show c
  end.
Instance : Show singleJudgement := { show := showSingleJudgement }.

Definition showLongSingleJudgement (s : singleJudgement) := 
  match s with
    | SingleJudgement e a c => showLong c ++ " is supported by $" ++ showLong e ++ "$ which " ++ showLong a ++ " uses"
  end.
Instance : ShowLong singleJudgement := { showLong := showLongSingleJudgement }.

Definition showJudgement (Ps : list singleJudgement) (Ts : list trustRelationInfo) (j : judgement) :=
  match j with
  | Entail s => 
      match Ps with
        | [] => show s
        | (h :: tl) as Ps => show Ps ++ " \vdash_{" ++ show Ts ++ "} " ++ show s
      end
  | IsAVeracityClaim c => show c ++ " \em{ is a veracity claim}"
  end.

Eval compute in showJudgement [] [] j1.
Eval compute in showJudgement [e1 \by a1 \in c1] [] j1.

Definition showLongJudgement (Ps : list singleJudgement) (Ts : list trustRelationInfo) (j : judgement) (p : proofTreeOf j) :=
  match j with
  | Entail s => 
      match Ps with
        | [] => showLong s
        | (h :: tl) as Ps => "Assuming " ++ showLong Ps ++ " then " ++ showLong s
      end
  | IsAVeracityClaim c => showLong c ++ " is a veracity claim"
  end.

Fixpoint getAllTrustRelationsUsed (j : judgement) (p : proofTreeOf j)
  : list trustRelationInfo :=
match p with
| admit _ => []
| leaf c => []
| assume e a name M => getAllTrustRelationsUsed _ M
| bot_elim e a C M => getAllTrustRelationsUsed _ M
| and_intro a e1 e2 C1 C2 L R => 
    getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
| and_elim1 a e1 e2 C1 C2 M => getAllTrustRelationsUsed _ M
| and_elim2 a e1 e2 C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro1 a e1 C1 C2 M => getAllTrustRelationsUsed _ M
| or_intro2 a e2 C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim1 a e1 C1 C2 M => getAllTrustRelationsUsed _ M
| or_elim2 a e2 C1 C2 M => getAllTrustRelationsUsed _ M
| trust a1 a2 e C name L => 
    name :: getAllTrustRelationsUsed _ L
| impl_intro e1 C1 a e2 C2 M => getAllTrustRelationsUsed _ M
| impl_elim a e1 e2 C1 C2 L R => 
   getAllTrustRelationsUsed _ L ++ getAllTrustRelationsUsed _ R 
end.

Fixpoint getAssumptions (j : judgement) (p : proofTreeOf j) : list singleJudgement := 
match p with
| admit _ => []
| leaf c => []
| assume e a c M => e \by a \in c :: getAssumptions _ M
| bot_elim e a C M => getAssumptions _ M
| and_intro a e1 e2 C1 C2 L R => 
    getAssumptions _ L ++ getAssumptions _ R 
| and_elim1 a e1 e2 C1 C2 M => getAssumptions _ M
| and_elim2 a e1 e2 C1 C2 M => getAssumptions _ M
| or_intro1 a e1 C1 C2 M => getAssumptions _ M
| or_intro2 a e2 C1 C2 M => getAssumptions _ M
| or_elim1 a e1 C1 C2 M => getAssumptions _ M
| or_elim2 a e2 C1 C2 M => getAssumptions _ M
| trust a1 a2 e C name L => 
    getAssumptions _ L
| impl_intro e1 C1 a e2 C2 M => filter (beq (e1 \by a \in C1)) (getAssumptions _ M)
| impl_elim a e1 e2 C1 C2 L R => 
   getAssumptions _ L ++ getAssumptions _ R 
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

Fixpoint showProofTreeOfHelper (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| admit p => "\AxiomC{?}"
| leaf c => "\AxiomC{$ " 
             ++ show c 
             ++ " \textit{ is a veracity claim} $}"
| assume e a c M => showProofTreeOfHelper _ M
    ++ " \RightLabel{ $ assume $}\UnaryInfC{$ "
    ++ showJudgement Ps Ts ( ||- e \by a \in c) ++ " $}"
| bot_elim e a C M => showProofTreeOfHelper _ M
    ++ " \RightLabel{ $ \bot^{-} $} \UnaryInfC{$ "
    ++ showJudgement Ps Ts ( ||- (e \by a \in C))
    ++ " $}"
| and_intro a e1 e2 C1 C2 L R => 
    showProofTreeOfHelper _ L
 ++ showProofTreeOfHelper _ R 
 ++ " \RightLabel{ $ \wedge^{+} $} \BinaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e1, e2) \by a \in (C1 /\' C2)) ++ " $}"
| and_elim1 a e1 e2 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \land^{-1} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e1 \by a \in C1))
 ++ " $}"
| and_elim2 a e1 e2 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \land^{-2} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e2 \by a \in C2))
 ++ " $}"
| or_intro1 a e1 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \lor^{+1} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- ((Left e1) \by a \in (C1 \/' C2)))
 ++ " $}"
| or_intro2 a e2 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \lor^{+2} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- ((Right e2) \by a \in (C1 \/' C2)))
 ++ " $}"
| or_elim1 a e1 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \lor^{-1} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e1 \by a \in C1))
 ++ " $}"
| or_elim2 a e2 C1 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \lor^{-2} $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e2 \by a \in C2))
 ++ " $}"
| trust a1 a2 e C name L => 
    showProofTreeOfHelper _ L
 ++ " \AxiomC{$" ++ show a1 ++ show name ++ show a2 ++ "$} "
 ++ " \RightLabel{ $ trust\ " ++ show name
 ++ "$} \BinaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (e \by a1 \in C)) ++ " $}"
| impl_intro e1 C1 a e2 C2 M => showProofTreeOfHelper _ M
 ++ " \RightLabel{ $ \rightarrow^+ $} \UnaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- ((Lambda e1 e2) \by a \in (Implies C1 C2)))
 ++ " $}"
| impl_elim a e1 e2 C1 C2 L R => 
     showProofTreeOfHelper _ L
 ++ showProofTreeOfHelper _ R 
 ++ " \RightLabel{ $ \rightarrow^{-} $} \BinaryInfC{$ "
 ++ showJudgement Ps Ts ( ||- (Apply e1 e2) \by a \in C2) ++ " $}"
end.

Fixpoint showLongProofTreeOfHelper (indent : string) (j : judgement) (p : proofTreeOf j)
  : string :=
let Ts := (removeDups (getAllTrustRelationsUsed j p)) in
let Ps := (removeDups (getAssumptions j p)) in
match p with
| admit p => indent ++ "we stopped the proof at this point and assumed it was provable."
| leaf c => indent ++ showLong c ++ " is a veracity claim."
| assume e a c M => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by assumption."
| bot_elim e a C M =>
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by the logical principle of explosion."
| and_intro a e1 e2 C1 C2 L R => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ L ++ "
"
++ showLongProofTreeOfHelper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim1 a e1 e2 C1 C2 M =>
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| and_elim2 a e1 e2 C1 C2 M => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'and'."
| or_intro1 a e1 C1 C2 M =>
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_intro2 a e2 C1 C2 M =>
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim1 a e1 C1 C2 M =>
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| or_elim2 a e2 C1 C2 M => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for 'or'."
| trust a1 a2 e C name L => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ L ++ "
"
++ indent ++ "by the trust relation " ++ showLong name ++ "."
| impl_intro e1 C1 a e2 C2 M => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ M ++ "
"
++ indent ++ "by a logical rule for implication."
| impl_elim a e1 e2 C1 C2 L R => 
indent ++ showLongJudgement Ps Ts _ p ++ ", because
" 
++ showLongProofTreeOfHelper ("  " ++ indent) _ L ++ "
"
++ showLongProofTreeOfHelper ("  " ++ indent) _ R ++ "
"
++ indent ++ "by a logical rule for implication."
end.

Open Scope string.

Definition showProofTreeOf j p
  := "\begin{prooftree}" ++ showProofTreeOfHelper j p
       ++ "\end{prooftree}".
Instance showProofTreeOfInstance (j : judgement)
  : Show (proofTreeOf j) := { show := showProofTreeOf j}.

Definition showLongProofTreeOf j p := "

" ++ showLongProofTreeOfHelper "- " j p ++ "

".
Instance showLongProofTreeOfInstance (j : judgement)
  : ShowLong (proofTreeOf j) := { showLong := showLongProofTreeOf j}.

(*|

An example from the paper
-------------------------

This example is the top half of the proof tree on p13 (Section 4.2) of the draft paper.

The proof trees visualised in this section are **automatically generated** by Coq.

|*)

Definition l := AtomicEvid (NamePair "l" "example evidence l").
Definition s := AtomicEvid (NamePair "s" "example evidence s").
Definition c := AtomicEvid (NamePair "c" "example evidence c").
Definition P := Actor (NamePair "P" "Penelope").
Definition Q := Actor (NamePair "Q" "Quintin").
Definition C1 := AtomicClaim (NamePair "C_1" "claim 1").
Definition C2 := AtomicClaim (NamePair "C_2" "claim 2").
Definition C3 := AtomicClaim (NamePair "C_3" "claim 3").
Definition C4 := AtomicClaim (NamePair "C_4" "claim 4").
Definition C5 := AtomicClaim (NamePair "C_5" "claim 5").

Definition trustT := Trust (NamePair "T" "T").
Definition trustU := Trust (NamePair "U" "U").
Definition trustV := Trust (NamePair "V" "V").

Definition concreteProofTreeExampleWith2Conjuncts : 
proofTreeOf ( ||- (l, s) \by P \in (C1 /\' C2)).
epose proof (and_intro _ _ _ C1 C2).
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

Eval compute in (showLong concreteProofTreeExampleWith2Conjuncts).

Definition concreteProofTreeExampleWith3Conjuncts : 
proofTreeOf ( ||- ((l, s),c) \by P \in (C1 /\' C2 /\' C3)).
epose proof (and_intro) P (l, s) c (C1 /\' C2) C3.
simpl in H.
apply H.
epose proof (and_intro) _ _ _ C1 C2.
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

Eval compute in (showLong concreteProofTreeExampleWith3Conjuncts).

(*|
We can also combine existing trees into new trees, when appropriate. For example:
|*)

Definition concreteProofTreeExampleWith3ConjunctsUsingExistingTree : 
proofTreeOf  ||- ((l, s),c) \by P \in (C1 /\' C2 /\' C3).
epose proof (and_intro) P (l, s) c (C1 /\' C2) C3.
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

Eval compute in (showLong concreteProofTreeExampleWith3Conjuncts).

Definition concreteProofTreeExampleTrust : 
proofTreeOf ||- e \by a1 \in (C).
apply (trust a1 a2 e C trustT).
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

Eval compute in (showLong concreteProofTreeExampleTrust).

Definition concreteProofTreeExampleWith3ConjunctsWithTrust : 
proofTreeOf ||- ((l, s),c) \by Q \in (C1 /\' C2 /\' C3).
eapply (trust _ _ _ _ trustU).
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

Eval compute in (showLong concreteProofTreeExampleWith3ConjunctsWithTrust).

Definition concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras : 
proofTreeOf ||- ((l, s),c) \by Q \in (C1 /\' C2 /\' C3).
eapply (trust Q Q _ _ trustU).
eapply (trust Q Q _ _ trustV).
eapply (trust _ _ _ _ trustU).
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

Eval compute in (showLong concreteProofTreeExampleWith3ConjunctsWithTrustAndExtras). 

Record proofTreeOfClaim (c : claim) := {
  _e : evid;
  _a : actor;
  _p : proofTreeOf ||- (_e \by _a \in c)
}.
Instance showProofTreeOfClaim (c : claim) : Show (proofTreeOfClaim c) := { show p := show (_p c p) }.
Instance showLongProofTreeOfClaim (c : claim) : ShowLong (proofTreeOfClaim c) := { showLong p := showLong (_p c p) }.

Definition exampleWithProofOf : proofTreeOfClaim C1.
Proof.
eexists _ _.
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

Eval compute in showLong exampleWithProofOf.

Definition usingAll : proofTreeOfClaim (Implies _|_ C1).
Proof.
eexists _ _.
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
eapply (trust _ _ _ _ trustT).
eapply (impl_intro ).
simpl.
eapply bot_elim.
apply (assume _ _ _|_).
apply leaf.
Unshelve.
1,8: apply a1.
1,2,4,6: apply C2.
all: apply e2.
Defined.

(*|
.. coq:: unfold
   :class: coq-math
|*)


Eval compute in show usingAll.

(*|
.. coq::
|*)

Eval compute in showLong usingAll.

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
+ unshelve apply leaf
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

Definition eQ := AtomicEvid (NamePair "e_{?}" "unknown evidence").
Definition CQ := AtomicClaim (NamePair "C_{?}" "unknown claim").
Definition aQ := Actor (NamePair "a_{?}" "unknown actor").

(* Ltac2 maybePrintMessage1 s := Message.print (Message.of_string s). *)
(* Ltac2 maybePrintMessage2 s := Message.print (Message.of_string s). *)
Ltac2 maybePrintMessage1 s := ().
Ltac2 maybePrintMessage2 s := ().
Ltac2 Type exn ::= [ VeracityProofSearchException(string) ].

Ltac2 tryLeaf etc :=
maybePrintMessage1 "Trying leaf";
match! goal with
   | [ |- proofTreeOf (IsAVeracityClaim _) ] => (maybePrintMessage2 "Applying leaf"); (eapply leaf); etc
   | [ |- _ ] => fail
end.

Ltac2 tryAssumeWitha1 etc :=
(maybePrintMessage1 "Trying assume");
match! goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying assume"); eapply (assume _ a1); etc
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Ltac2 tryAndIntro etc :=
(maybePrintMessage1 "Trying and_intro");
match! goal with
   | [ |- (proofTreeOf _ ||- _ \by _ \in (_ /\' _)) ] => (maybePrintMessage2 "Applying and_intro"); eapply and_intro; Control.enter (fun _ => etc)
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Ltac2 tryTrust etc :=
(maybePrintMessage1 "Trying trust");
match! goal with
   | [ |- proofTreeOf _ ] => (maybePrintMessage2 "Applying trust"); (eapply (trust _ _ _ _ _ _)); etc
   | [ |- _ ] => Control.zero (VeracityProofSearchException "Didn't match")
end.

Ltac2 fillConstant () :=
solve [ apply CQ | apply aQ | apply eQ | apply ([] : list singleJudgement) | apply (Trust "?") ].

Set Default Proof Mode "Ltac2".
(* Set Ltac2 Backtrace. *)

Ltac2 rec autoProveMain max_depth :=
match Int.equal 0 max_depth with
  | true => Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [
      eapply and_intro; autoProveMain (Int.sub max_depth 1)
    | eapply (assume _ a1); autoProveMain (Int.sub max_depth 1)
    | eapply leaf; autoProveMain (Int.sub max_depth 1)
    | eapply (trust _ _ _ _ _); autoProveMain (Int.sub max_depth 1)
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
eexists _ _.
autoProve ().
Unshelve.
all: fillConstant ().
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

Eval compute in showLong exampleC1.

Set Default Proof Mode "Ltac2".


(*|
The following demonstrates automatically proving a larger claim.
|*)
(*  *)
(* Set Default Goal Selector "!". *)

Definition automatedProof : proofTreeOfClaim (C1 /\' C2 /\' C3 /\' C4 /\' C5).
Proof.
eexists _ _.
Time autoProve ().  (* Finished transaction in 0.1 secs (0.099u,0.s) (successful) *)
(* Time autoProve (). Using match statements Finished transaction in 0.188 secs (0.181u,0.004s) (successful) *)
(* Time autoProveMain 7. Finished transaction in 0.002 secs (0.002u,0.s) (successful) *)
(* Time autoProveMain ().  Finished transaction in 1.503 secs (1.475u,0.s) (successful) *)
Unshelve.
all: fillConstant ().
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

Eval compute in showLong automatedProof.

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
    | eapply leaf; autoProveMain1 (Int.sub max_depth 1)
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
eexists _ _.
autoProve1 ().
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show fromPaper1.

(*|
.. coq::
|*)

Eval compute in showLong fromPaper1.

Definition healthy := AtomicClaim (NamePair "H" "healthy").
Definition nonToxic := AtomicClaim (NamePair "N" "non-toxic").
Definition organic := AtomicClaim (NamePair "O" "organic").
Definition belief := AtomicEvid (NamePair "b" "belief").
Definition testing := AtomicEvid (NamePair "t" "testing").
Definition audit := AtomicEvid (NamePair "a" "audit").
Definition retailer := Actor (NamePair "r" "retailer").
Definition vineyard := Actor (NamePair "v" "vineyard").
Definition winery := Actor (NamePair "w" "winery").


Definition exampleFromJosh : proofTreeOfClaim healthy.
eexists _ retailer.
eapply (impl_elim _ belief (testing, audit) (nonToxic /\' organic)).
eapply assume.
eapply leaf.
eapply and_intro.
eapply (trust retailer vineyard _ _ trustT).
eapply assume.
eapply leaf.
eapply (trust retailer winery _ _ trustT).
eapply assume.
eapply leaf.
Unshelve.
all: fillConstant ().
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show exampleFromJosh.

(*|
.. coq::
|*)

Eval compute in showLong exampleFromJosh.

Ltac2 rec autoProveMain2 max_depth :=
match Int.equal 0 max_depth with
  | true => Control.zero (VeracityProofSearchException ("Ran out of depth."))
  (* | true => () *)
  | false => solve [
      eapply and_intro; autoProveMain2 (Int.sub max_depth 1)
    | eapply (impl_elim); autoProveMain2 (Int.sub max_depth 1)
    | eapply (trust retailer vineyard _ _ trustT); autoProveMain2 (Int.sub max_depth 1)
    | eapply (trust retailer winery _ _ trustT); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume testing vineyard nonToxic); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume belief retailer (Implies (nonToxic /\' organic) healthy)); autoProveMain2 (Int.sub max_depth 1)
    | eapply (assume audit winery organic); autoProveMain2 (Int.sub max_depth 1)
    | eapply leaf; autoProveMain2 (Int.sub max_depth 1)
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
eexists _ retailer.
autoProve2 ().
Show Proof.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show exampleFromJoshAuto.

(*|
.. coq::
|*)

Eval compute in (showLong exampleFromJoshAuto).

Definition whiteboardExample : proofTreeOfClaim (Implies C1 C2).
Proof.
eexists _ _.
eapply (impl_intro e1).
eapply (trust a2 _ e2 _ trustT).
eapply (assume e2 a1).
eapply leaf.
Defined.


(*|
.. coq:: unfold
   :class: coq-math
|*)

Eval compute in show whiteboardExample.

(*|
.. coq::
|*)

Eval compute in (showLong whiteboardExample).

