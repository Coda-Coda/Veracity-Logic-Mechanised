#! /usr/bin/env python

# Python Script to Generate Coq Notations for Inference Rules

import functools

def notationAB(n):
  return 'Notation "A ' + '-'*n + ' B" := (A -> B) (at level 95, right associativity).\n'

def notationABC(n):
  return 'Notation "A | B ' + '-'*n + ' C" := ((A /\ B) -> C) (at level 94, right associativity).\n'

def notationABCD(n):
  return 'Notation "A | B | C ' + '-'*n + ' D" := ((A /\ B /\ C) -> D) (at level 93, right associativity).\n'

def flatten(s):
  return functools.reduce(lambda a, b : a + b, s)

def notationCommands(minDashes, maxDashes):
  return flatten(map(notationAB, range(minDashes, maxDashes + 1))) + "\n" + (flatten(map(notationABC, range(minDashes, maxDashes + 1)))) + "\n" + flatten(map(notationABCD, range(minDashes, maxDashes + 1)))

minDashes = 3
maxDashes = 50
print(notationCommands(minDashes, maxDashes))