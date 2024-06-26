
theory LogicVeracBoolA imports Main begin

no_notation HOL.conj (infixr "\<and>" 35)
no_notation HOL.disj (infixr "\<or>" 30)
no_notation Set.member  ("(_/ \<in> _)" [51, 51] 50)

(*********************************************************************)
section \<open>Basic Syntax\<close>

typedecl a
typedecl e
typedecl c

datatype evid
  = Atomic e
  | Pair evid evid (infix "\<cedilla>" 80)
  | Left evid
  | Right evid
  | Lambda evid evid

datatype claim
  = Atomic c
  | False ("\<bottom>")
  | And claim claim (infix "\<and>" 75)
  | Or claim claim (infix "\<or>" 70)
  | Implies claim claim (*(infixr "\<Rightarrow>" 25)*)

datatype sentence
= Judgement a evid claim ("_:_\<in>_" [61, 61, 61] 60)
| Trusts a a (infix "T" 85)


(*********************************************************************)
section \<open>Inference Rules\<close>

inductive Entail :: "sentence list \<Rightarrow> sentence \<Rightarrow> bool" ("_\<turnstile>_") where

  bot_elim: "Ps \<turnstile> (a : e \<in> \<bottom>) \<Longrightarrow> Ps \<turnstile> (a : e \<in> C)"

| and_intro: "Ps \<turnstile> (a : e1 \<in> C1) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)
          \<Longrightarrow> Ps \<turnstile> (a : (e1 \<cedilla> e2) \<in> (C1 \<and> C2))"

| and_elim1: "Ps \<turnstile> (a : (e1 \<cedilla> e2) \<in> C1 \<and> C2) \<Longrightarrow> Ps \<turnstile> (a : e1 \<in> C1)"
| and_elim2: "Ps \<turnstile> (a : (e1 \<cedilla> e2) \<in> C1 \<and> C2) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)"

| or_intro1: "Ps \<turnstile> (a : e1 \<in> C1) \<Longrightarrow> Ps \<turnstile> (a : Left e1 \<in> C1 \<or> C2)"
| or_intro2: "Ps \<turnstile> (a : e2 \<in> C2) \<Longrightarrow> Ps \<turnstile> (a : Right e2 \<in> C1 \<or> C2)"

| or_elim1: "Ps \<turnstile> (a : Left e1 \<in> C1 \<or> C2) \<Longrightarrow> Ps \<turnstile> (a : e1 \<in> C1)"
| or_elim2: "Ps \<turnstile> (a : Right e2 \<in> C1 \<or> C2) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)"

| trust: "Ps \<turnstile> (a2 : e \<in> C) \<Longrightarrow> Ps \<turnstile> (a1 T a2) \<Longrightarrow> Ps \<turnstile> (a1 : e \<in> C)"

(* Recall that @ means list-concatenation, and # is like "cons", here
   used to add (a : e1 \<in> C1) to the front of Qs. *)
| impl_intro: "(Ps @ ((a : e1 \<in> C1) # Qs)) \<turnstile> (a : e2 \<in> C2)
           \<Longrightarrow> (Ps @ Qs) \<turnstile> (a : Lambda e1 e2 \<in> (Implies C1 C2))"

print_theorems

(*********************************************************************)
section \<open>Examples: Incorrect Statements\<close>

lemma "[] \<turnstile> (a : e \<in> C)"
  by (blast intro: Entail.intros)

(* This next statement is actually correct,
     possibly because the antecedent is false? *)
lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) \<rbrakk> \<Longrightarrow> [] \<turnstile> (a : (e1 \<cedilla> e2) \<in> (C1 \<and> C2))"
   by (rule LogicVeracBoolA.Entail.induct)


(*********************************************************************)
section \<open>Examples: Correct Statements\<close>

lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) ; [] \<turnstile> (a : e2 \<in> C2) ; [] \<turnstile> (a : e3 \<in> C3) \<rbrakk>
     \<Longrightarrow> [] \<turnstile> (a : ((e1 \<cedilla> e2) \<cedilla> e3) \<in> (C1 \<and> C2) \<and> C3)"
  apply(rule and_intro)
  apply(rule and_intro)
  apply(auto)
  done

lemma assumes "[] \<turnstile> (a1 : e1 \<in> C1)" 
          and "[] \<turnstile> (a2 : e2 \<in> C2)" 
          and "[] \<turnstile> (a2 T a1)"
        shows "[] \<turnstile> (a2 : (e1 \<cedilla> e2) \<in> C1 \<and> C2)"
  apply(rule and_intro)
   apply(rule trust)   
    apply(rule assms)
   apply(rule assms)
  apply(rule assms)
  done




lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) \<rbrakk>
     \<Longrightarrow> [] \<turnstile> (a : (e1\<cedilla> e2) \<in> C1 \<and> C2)"
  by (rule LogicVeracBoolA.Entail.induct)

end