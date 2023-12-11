#! /usr/bin/env python

# Python Script to Generate Coq Notations for Inference Rules

import functools

def notationLine(n):
  return 'Notation "A ' + '-'*n + ' B" := (A -> B) (at level 99, right associativity, only parsing).\n'

def flatten(s):
  return functools.reduce(lambda a, b : a + b, s)

def notationCommands(minDashes, maxDashes):
  return flatten(map(notationLine, range(minDashes, maxDashes + 1)))

minDashes = 3
maxDashes = 100
print(notationCommands(minDashes, maxDashes))