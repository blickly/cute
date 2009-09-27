#!/usr/bin/python
###########################################################
#                 Fall 2009 CS 265, HW 1
# Author:   Ben Lickly
# Created:  September 22, 2009
# Date Due: September 28, 2009
# Filename: mycute.py
###########################################################

import sys
import os
import subprocess
import re
import cPickle

yices = "../yices-linux32/bin/yices"

MAX = {}
MIN = {}
A = {}

class stackelt:
  def __init__(self, branch):
    self.branch = branch
    self.done = False

  def __str__(self):
    return "(" + self.branch + "," + str(self.done) + ")"

def debuginfo():
  print "stack:"
  for i in stack:
    print i

if os.path.exists('stack'):
  stackfile = open('stack', 'rb')
  stack = cPickle.load(stackfile)
  stackfile.close()
else:
  stack = []

if os.path.exists('seenbranches'):
  branchfile = open('seenbranches', 'rb')
  seenbranches = cPickle.load(branchfile)
  branchfile.close()
else:
  seenbranches = set()

def bounds():
  sizes = {"char":8, "short":16, "int":32, "long":64, "long long":128}
  for (type, size) in sizes.items():
    MAX[type] = str(2 ** (size-1) - 1)
    MIN[type] = str(-(2** (size-1)))
    MAX["unsigned " + type] = str(2 ** (size) - 1)
    MIN["unsigned " + type] = '0'

def main():
  bounds()
  runProgram()
  stackfile = open('stack', 'wb')
  cPickle.dump(stack, stackfile)
  stackfile.close()
  branchfile = open('seenbranches', 'wb')
  cPickle.dump(seenbranches, branchfile)
  branchfile.close()
  return 1

def runProgram():
  (assignment, operation, branch) = regexCompile()
  defineConstraints = ""
  branchConstraints = []
  k = 0
  for line in open('trace', 'r'):
    ma = assignment.match(line)
    mo = operation.match(line)
    mb = branch.match(line)
    if ma:
      defineConstraints += matched_assignment(ma.groupdict())
    elif mo:
      matched_operation(mo.groupdict())
      pass
    elif mb:
      d = mb.groupdict()
      seenbranches.add(d["num"])
      c = matched_branch(d)
      if c != None:
        branchConstraints.append(c)
      updateStack(d["dir"], k)
      k = k + 1
    else:
      print "Failed to match line: <" + line + ">"
  return solveConstraints(k, defineConstraints, branchConstraints)

def solveConstraints(k, dConstraints, constraints):
  print "========== In solve path constraint ===="
  debuginfo()
  print "k:",k
  for j in range(k-1, -2, -1):
    if stack[j].done == False:
      break
  if j == -1:
    print "Done with search!"
    return 1
  print "j:",j, constraints[j], stack[j]
  constraints[j] = negateCons(constraints[j])
  stack[j].branch = negateDir(stack[j].branch)
  del constraints[j+1:]
  del stack[j+1:]
  if runYices(dConstraints + \
      reduce(lambda x, y: x+ "(assert " + y + ")\n", constraints, "")):
    print constraints
    debuginfo()
    return 0
  else:
    return solveConstraints(j, dConstraints, constraints)
  

def updateStack(branch, k):
  print "=== update stack === (k=",k," stack size=", len(stack), ")"
  debuginfo()
  if k < len(stack):
    if stack[k].branch != branch:
      raise Exception('try new inputs')
    elif k == len(stack) - 1:
      stack[k].branch = branch
      stack[k].done = True
  else:
    stack.append(stackelt(branch))

def negateCons(c):
  return "(not " + c + ")"

def negateDir(d):
  if d == "then":
    return "else"
  elif d == "else":
    return "then"

def matched_assignment(d):
  if d["type"]:
    var = d["raddr"]
    t = d["type"]
    A[d["laddr"]] = var
    return ("(define " + var + "::int)\n"
                   "(assert (<= " + var + " " + MAX[t] +"))\n"
                   "(assert (>= " + var + " " + MIN[t] +"))\n")
  if d["raddr"] in A:
    A[d["laddr"]] = A[d["raddr"]]
  elif d["laddr"] in A:
    del A[d["laddr"]]
  return ""

def matched_operation(d):
  A[d["laddr"]] = symbolic_expression(d)
  #if A[d["laddr"]] == None:
  #  del A[d["laddr"]]

def symbolic_expression(d):
  isSymbolic1, isSymbolic2 = d["raddr1"] in A, d["raddr2"] in A
  if d["op"] == "==":
    d["op"] = "="
  if d["op"] == "!=":
    d["op"] = "/="
  if isSymbolic1 and isSymbolic2 and d["op"] != "*":
    arg1, arg2 = A[d["raddr1"]], A[d["raddr2"]]
  elif isSymbolic1:
    arg1, arg2 = A[d["raddr1"]], d["rval2"]
  elif isSymbolic2:
    arg1, arg2 = d["rval1"], A[d["raddr2"]]
  else:
    arg1, arg2 = d["rval1"], d["rval2"]
  return "(" + d["op"] + " " + arg1 + " " + arg2 + ")"

def matched_branch(d):
  c = symbolic_expression(d)

  if d["dir"] == "then" or c == None:
    return c
  elif d["dir"] == "else":
    return negateCons(c)
  else:
    print "Unknown direction:",d["dir"]

def generateYicesInput(str):
  return ("(set-evidence! true)\n"
          + str
          + "(check)\n")

def runYices(yicesConstraints):
  yicesInput = generateYicesInput(yicesConstraints)
  f = open('yicesIn', 'w')
  f.write(yicesInput)
  f.close()
  f = open('input', 'w')
  subprocess.call([yices, 'yicesIn'], stdout=f)
  f.close()
  f = open('input', 'r')
  firstline = f.readline()
  f.close()
  sucess = firstline == 'sat\n'
  print firstline, sucess
  return sucess

def regexCompile():
  assignment = re.compile("""
      \((?P<laddr>\w+),(?P<lval>-?\w+)\)
      \s=\s
        (\((?P<type>[ a-z]+)\))?
      \((?P<raddr>\w+),(?P<rval>-?\w+)\)
      $""", re.VERBOSE)
  operation = re.compile("""
      \((?P<laddr>\w+),(?P<lval>-?\w+)\)
      \s=\s
      \((?P<raddr1>\w+),(?P<rval1>-?\w+)\)
      \s(?P<op>\S)\s
      \((?P<raddr2>\w+),(?P<rval2>-?\w+)\)
      $""", re.VERBOSE)
  branch = re.compile("""
      (?P<dir>\w+):(?P<num>\d+)\s
      \((?P<raddr1>\w+),(?P<rval1>-?\w+)\)
      \s(?P<op>\S+)\s
      \((?P<raddr2>\w+),(?P<rval2>-?\w+)\)""", re.VERBOSE)
  return (assignment, operation, branch)



if __name__ == "__main__":
  sys.exit(main())
