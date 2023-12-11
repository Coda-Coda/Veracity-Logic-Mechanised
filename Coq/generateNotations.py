#! /usr/bin/env python

# Python Script to Generate Coq Notations for Inference Rules

import functools

def notationLine(n):
  return 'Notation "{ x | .. | y } ' + '-'*n + '  C" := ((and x .. (and y True) ..) -> C) (at level 99, right associativity).\n'

def flatten(s):
  return functools.reduce(lambda a, b : a + b, s)

def notationCommands(minDashes, maxDashes):
  return flatten(map(notationLine, range(minDashes, maxDashes + 1)))

minDashes = 3
maxDashes = 100
print(notationCommands(minDashes, maxDashes))