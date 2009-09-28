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
import random

yices = "../yices-linux32/bin/yices"

class stackelt:
  def __init__(self, branch):
    self.branch = branch
    self.done = False

  def __str__(self):
    return "(" + self.branch + "," + str(self.done) + ")"

def pickle(filename, obj):
  file = open(filename, 'wb')
  cPickle.dump(obj, file)
  file.close()

def unpickle(filename):
  file = open(filename, 'rb')
  obj = cPickle.load(file)
  file.close()
  return obj

class mycute:
  random.seed(95)
  MAX = {}
  MIN = {}

  def __init__(self):
    self.bounds()
    self.A = {}
    self.debug = False
    self.clearstack = False

    self.stack = []
    if os.path.exists('stack'):
      self.stack = unpickle('stack')

    self.seenbranches = set()
    if os.path.exists('seenbranches'):
      self.seenbranches = unpickle('seenbranches')
    self.prevseen = self.seenbranches

  def bounds(self):
    sizes = {"char":8, "short":16, "int":32, "long":64, "long long":128}
    for (type, size) in sizes.items():
      mycute.MAX[type] = str(2 ** (size-1) - 1)
      mycute.MIN[type] = str(-(2** (size-1)))
      mycute.MAX["unsigned " + type] = str(2 ** (size) - 1)
      mycute.MIN["unsigned " + type] = '0'

  def debuginfo(self):
    print "stack:"
    for i in self.stack:
      print i

  def main(self):
    print "mycute started...",
    retval = self.runProgram()
    if retval == 1:
      try:
        os.unlink('stack')
        os.unlink('seenbranches')
      except:
        pass
    else:
      pickle('stack', self.stack)
      pickle('seenbranches', self.seenbranches)
    total = int(open('branchcount').read())
    seen = len(self.seenbranches)
    print "Branch coverage: %d/%d (%.2f%%)" % (seen, total, 100.0*seen/total)
    if self.clearstack:
      try:
        os.unlink('stack')
      except:
        pass
    return retval

  def runProgram(self):
    (assignment, operation, branch) = self.regexCompile()
    defineConstraints = []
    branchConstraints = []
    k = 0
    for line in open('trace', 'r'):
      ma = assignment.match(line)
      mo = operation.match(line)
      mb = branch.match(line)
      if ma:
        defineConstraints += self.matched_assignment(ma.groupdict())
      elif mo:
        self.matched_operation(mo.groupdict())
        pass
      elif mb:
        d = mb.groupdict()
        self.seenbranches.add(d["num"])
        c = self.matched_branch(d)
        if c == None:
          branchConstraints.append("true")
        else:
          branchConstraints.append(c)
        self.updatestack(d["dir"], k)
        k = k + 1
      else:
        print "Failed to match line: <" + line + ">"
    return self.solveConstraints(k, defineConstraints, branchConstraints)

  def solveConstraints(self, k, dConstraints, constraints):
    if self.debug:
      print "========== In solve path constraint ===="
      self.debuginfo()
      print "k:",k
    if self.seenbranches == self.prevseen and random.randrange(100) < 3:
      return self.randomSolve(k, dConstraints, constraints)
    changePoints = [i for i in xrange(k) if self.stack[i].done == False]
    if changePoints == []:
      print "Done with search!"
      return 1
    j = max(changePoints)
    self.stack[j].branch = self.negateDir(self.stack[j].branch)
    del constraints[j+1:]
    del self.stack[j+1:]
    if self.debug:
      print "j:",j, constraints[j], self.stack[j]
    constraints[j] = self.negateCons(constraints[j])
    if self.satisfiable(dConstraints, constraints):
      if self.debug:
        print constraints
        self.debuginfo()
      return 0
    else:
      return self.solveConstraints(j, dConstraints, constraints)

  def randomSolve(self, k, dCons, bCons):
    if self.debug:
      print "in randomSolve..."
    self.clearstack = True
    while True:
      changePoints = [i for i in xrange(k)
          if self.stack[i].done == False and bCons[i] != "true"]
      if changePoints == []:
        if self.debug:
           print "*ALL RANDOM*"
        bCons = []
        for (var, t) in dCons:
          val = random.randrange(int(mycute.MIN[t]), int(mycute.MAX[t]))
          bCons.append("(= " + var + " " + str(val) + ")")
        assert self.satisfiable(dCons, bCons)
        return 0
      j = random.choice(changePoints)
      bCons[j] = self.negateCons(bCons[j])
      self.stack[j].branch = self.negateDir(self.stack[j].branch)
      del bCons[j+1:]
      del self.stack[j+1:]
      k = j
      if self.satisfiable(dCons, bCons):
        return 0

  def satisfiable(self, dCons, bCons):
    if self.negateCons(bCons[-1]) in bCons:
      return False
    return self.runYices(dCons, bCons)

  def updatestack(self, branch, k):
    if self.debug:
      print "=== updatestack === (k=",k," stack size=", len(self.stack), ")"
      self.debuginfo()
    if k < len(self.stack):
      if self.stack[k].branch != branch:
        raise Exception('try new inputs')
      elif k == len(self.stack) - 1:
        self.stack[k].branch = branch
        self.stack[k].done = True
    else:
      self.stack.append(stackelt(branch))

  def negateCons(self, c):
    if c[:5] == "(not " and c[-1] == ")":
      return c[5:-1]
    else:
      return "(not " + c + ")"

  def negateDir(self, d):
    if d == "then":
      return "else"
    elif d == "else":
      return "then"

  def matched_assignment(self, d):
    if d["type"]:
      var = d["raddr"]
      self.A[d["laddr"]] = var
      return [(var, d["type"])]
    if d["raddr"] in self.A:
      self.A[d["laddr"]] = self.A[d["raddr"]]
    else:
      self.A.pop(d["laddr"], None)
    return []

  def matched_operation(self, d):
    e = self.symbolic_expression(d)
    if e == None:
      self.A.pop(d["laddr"], None)
    else:
      if d["op"] in ["=","/=","==","!=","<",">","<=",">="]:
        e = "(if " + e + " 1 0)"
      self.A[d["laddr"]] = e

  def symbolic_expression(self, d):
    isSymbolic1, isSymbolic2 = d["raddr1"] in self.A, d["raddr2"] in self.A
    if d["op"] == "==":
      d["op"] = "="
    if d["op"] == "!=":
      d["op"] = "/="
    if isSymbolic1 and isSymbolic2 and d["op"] != "*":
      arg1, arg2 = self.A[d["raddr1"]], self.A[d["raddr2"]]
    elif isSymbolic1:
      arg1, arg2 = self.A[d["raddr1"]], d["rval2"]
    elif isSymbolic2:
      arg1, arg2 = d["rval1"], self.A[d["raddr2"]]
    else:
      #arg1, arg2 = d["rval1"], d["rval2"]
      return None
    return "(" + d["op"] + " " + arg1 + " " + arg2 + ")"

  def matched_branch(self, d):
    c = self.symbolic_expression(d)
    if d["dir"] == "then" or c == None:
      return c
    elif d["dir"] == "else":
      return self.negateCons(c)
    else:
      print "Unknown direction:",d["dir"]

  def runYices(self, dCons, bCons):
    yicesInput = "(set-evidence! true)\n"
    for (var, t) in dCons:
      yicesInput += "(define " + var + "::int)\n" + \
                    "(assert (<= " + var + " " + mycute.MAX[t] +"))\n" + \
                    "(assert (>= " + var + " " + mycute.MIN[t] +"))\n"
    for line in bCons:
      yicesInput += "(assert " + line + ")\n"
    yicesInput += "(check)\n"
    f = open('yicesIn', 'w')
    f.write(yicesInput)
    f.close()
    f = open('input', 'w')
    subprocess.call([yices, 'yicesIn'], stdout=f)
    f.close()
    f = open('input', 'r')
    firstline = f.readline()
    f.close()
    if self.debug:
      print firstline
    return (firstline == 'sat\n')

  def regexCompile(self):
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
        \s(?P<op>\S+)\s
        \((?P<raddr2>\w+),(?P<rval2>-?\w+)\)
        $""", re.VERBOSE)
    branch = re.compile("""
        (?P<dir>\w+):(?P<num>\d+)\s
        \((?P<raddr1>\w+),(?P<rval1>-?\w+)\)
        \s(?P<op>\S+)\s
        \((?P<raddr2>\w+),(?P<rval2>-?\w+)\)""", re.VERBOSE)
    return (assignment, operation, branch)

if __name__ == "__main__":
  cute = mycute()
  sys.exit(cute.main())
