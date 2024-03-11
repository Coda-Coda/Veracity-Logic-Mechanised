
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
  | Pair evid evid
  | Left evid
  | Right evid
  | Lambda evid evid

datatype claim
  = Atomic c
  | False ("\<bottom>")
  | And claim claim (infixr "\<and>" 35)
  | Or claim claim (infixr "\<or>" 30)
  | Implies claim claim (*(infixr "\<Rightarrow>" 25)*)

datatype sentence
= Judgement a evid claim ("_:_\<in>_" [61, 61, 61] 60)
| Trusts a a (infix "T" 60)


(*********************************************************************)
section \<open>Inference Rules\<close>

inductive Entail :: "sentence list \<Rightarrow> sentence \<Rightarrow> bool" ("_\<turnstile>_") where

  bot_elim: "Ps \<turnstile> (a : e \<in> \<bottom>) \<Longrightarrow> Ps \<turnstile> (a : e \<in> C)"

| and_intro: "Ps \<turnstile> (a : e1 \<in> C1) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)
          \<Longrightarrow> Ps \<turnstile> (a : (Pair e1 e2) \<in> (And C1 C2))"

| and_elim1: "Ps \<turnstile> (a : Pair e1 e2 \<in> And C1 C2) \<Longrightarrow> Ps \<turnstile> (a : e1 \<in> C1)"
| and_elim2: "Ps \<turnstile> (a : Pair e1 e2 \<in> And C1 C2) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)"

| or_intro1: "Ps \<turnstile> (a : e1 \<in> C1) \<Longrightarrow> Ps \<turnstile> (a : Left e1 \<in> Or C1 C2)"
| or_intro2: "Ps \<turnstile> (a : e2 \<in> C2) \<Longrightarrow> Ps \<turnstile> (a : Right e2 \<in> Or C1 C2)"

| or_elim1: "Ps \<turnstile> (a : Left e1 \<in> Or C1 C2) \<Longrightarrow> Ps \<turnstile> (a : e1 \<in> C1)"
| or_elim2: "Ps \<turnstile> (a : Right e2 \<in> Or C1 C2) \<Longrightarrow> Ps \<turnstile> (a : e2 \<in> C2)"

| trust: "Ps \<turnstile> (a2 : e \<in> C) \<Longrightarrow> Ps \<turnstile> (a1 T a2) \<Longrightarrow> Ps \<turnstile> (a1 : e \<in> C)"

(* Recall that @ means list-concatenation *)
| impl_intro: "(Ps @ ((a : e1 \<in> C1) # Qs)) \<turnstile> (a : e2 \<in> C2)
           \<Longrightarrow> (Ps @ Qs) \<turnstile> (a : Lambda e1 e2 \<in> (Implies C1 C2))"

print_theorems

(*********************************************************************)
section \<open>Examples: Incorrect Statements\<close>

lemma "[] \<turnstile> (a : e \<in> C)"
  by (blast intro: Entail.intros)


lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) \<rbrakk> \<Longrightarrow> [] \<turnstile> (a : Pair e1 e2 \<in> And C1 C2)"
  apply (rule and_intro)
   apply (simp)
  oops


(*********************************************************************)
section \<open>Examples: Correct Statements\<close>

lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) ; [] \<turnstile> (a : e2 \<in> C2) ; [] \<turnstile> (a : e3 \<in> C3) \<rbrakk>
     \<Longrightarrow> [] \<turnstile> (a : Pair (Pair e1 e2) e3 \<in> And (And C1 C2) C3)"
  apply(rule and_intro)
  apply(rule  and_intro)
  apply(auto)
  done


lemma assumes "[] \<turnstile> (a1 : e1 \<in> C1)" 
          and "[] \<turnstile> (a2 : e2 \<in> C2)" 
          and "[] \<turnstile> (a2 T a1)"
        shows "[] \<turnstile> (a2 : Pair e1 e2 \<in> And C1 C2)"
  apply(rule and_intro)
   apply(rule trust)   
    apply(rule assms)
   apply(rule assms)
  apply(rule assms)
  done




lemma "\<lbrakk> [] \<turnstile> (a : e1 \<in> C1) \<rbrakk>
     \<Longrightarrow> [] \<turnstile> (a : Pair e1 e2 \<in> And C1 C2)"
  apply(rule and_intro)
   apply(auto)
  oops

end