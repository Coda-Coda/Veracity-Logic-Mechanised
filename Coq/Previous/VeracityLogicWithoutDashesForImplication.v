Require Import List.
Import ListNotations.

Section VeracityLogic.

Inductive evid :=
  | AtomicEvid (name : nat)
  | Pair (e1 e2 : evid)
  | Left (e1 : evid)
  | Right (e1 : evid)
  | Lambda (e1 e2 : evid).

Inductive claim :=
  | AtomicClaim (name : nat)
  | Bottom
  | And (c1 c2 : claim)
  | Or  (c1 c2 : claim)
  | Implies  (c1 c2 : claim).

Inductive sentence := 
| Judgement (a : nat) (e : evid) (c : claim)
| Trusts (a1 a2 : nat).

Infix "/\'" := And (at level 80, right associativity).
Infix "\/'" := Or (at level 85, right associativity). 
Notation "A : E \in C" := (Judgement A E C) (at level 1).
Notation "_|_" := (Bottom) (at level 1).
Notation "( x , y , .. , z )" := (Pair .. (Pair x y) .. z).

Reserved Notation "A |- B" (at level 80).

Inductive Entail : list sentence -> sentence -> Prop :=
| bot_elim : forall Ps a e C,

                      (Ps |- (a : e \in _|_))
                               ->
                       (Ps |- (a : e \in C))

| and_intro : forall Ps a e1 e2 C1 C2,

               Ps |- (a : e1 \in C1) /\ Ps |- (a : e2 \in C2)
                                   ->
                   Ps |- (a : (e1, e2) \in (C1 /\' C2))

| and_elim1 : forall Ps a e1 e2 C1 C2,

                Ps |- (a : (e1, e2) \in (C1 /\' C2))
                                ->
                       Ps |- (a : e1 \in C1)

| and_elim2 : forall Ps a e1 e2 C1 C2,

                Ps |- (a : (e1, e2) \in (C1 /\' C2))
                                ->
                       Ps |- (a : e2 \in C2)

| or_intro1 : forall Ps a e1 C1 C2,

                         Ps |- (a : e1 \in C1)
                                 ->
                  Ps |- (a : Left e1 \in (C1 \/' C2))

| or_intro2 : forall Ps a e2 C1 C2,

                         Ps |- (a : e2 \in C2)
                                   ->
                  Ps |- (a : Right e2 \in (C1 \/' C2))

| or_elim1 : forall Ps a e1 C1 C2,

                  Ps |- (a : Left e1 \in (C1 \/' C2))
                                  ->
                         Ps |- (a : e1 \in C1)

| or_elim2 : forall Ps a e2 C1 C2,

                  Ps |- (a : Right e2 \in (C1 \/' C2))
                                  ->
                          Ps |- (a : e2 \in C2)

| trust : forall Ps a1 a2 e C,

                  Ps |- (a2 : e \in C) /\ Ps |- (Trusts a1 a2)
                                   ->
                          Ps |- (a1 : e \in C)

| impl_intro : forall Ps Qs a e1 e2 C1 C2,

                  Ps ++ ((a : e1 \in C1) :: Qs) |- (a : e2 \in C2)
                                          ->
                (Ps ++ Qs) |- (a : Lambda e1 e2 \in (Implies C1 C2))
             
where "A |- B"  := (Entail A B).