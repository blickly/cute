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

if os.path.exists('stack'):
  stackfile = open('stack', 'r+b')
  stack = cPickle.load(stackfile)
else:
  stack = []
  stackfile = open('stack', 'wb')

def bounds():
  sizes = {"char":8, "short":16, "int":32, "long":64, "long long":128}
  for (type, size) in sizes.items():
    MAX[type] = str(2 ** (size-1) - 1)
    MIN[type] = str(-(2** (size-1)))
    MAX["unsigned " + type] = str(2 ** (size) - 1)
    MIN["unsigned " + type] = '0'

def main():
  bounds()
  runYices(generateYicesInput(readTrace()))
  #print "A:",A
  cPickle.dump(stack, stackfile)
  stackfile.close()
  return 1

def readTrace():
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
      \((?P<addr1>\w+),(?P<val1>-?\w+)\)
      \s(?P<op>\S+)\s
      \((?P<addr2>\w+),(?P<val2>-?\w+)\)""", re.VERBOSE)
  defineConstraints = ""
  branchConstraints = []
  k = 0
  for line in open('trace', 'r'):
    ma = assignment.match(line)
    mo = operation.match(line)
    mb = branch.match(line)
    mb = branch.match(line)
    if ma:
      defineConstraints += matched_assignment(ma.groupdict())
    elif mo:
      matched_operation(mo.groupdict())
      pass
    elif mb:
      d = mb.groupdict()
      c = matched_branch(d)
      updateStack(d["dir"], k)
      #if d["num"] < stacksize:
        #c = negateCons(c)
        #pass
      branchConstraints.append(c)
      k = k + 1
    else:
      print "Failed to match line: <" + line + ">"
  branchConstraints = negateLastBranch(k, branchConstraints)
  return defineConstraints + \
      reduce(lambda x, y: x+ "(assert " + y + ")\n", branchConstraints, "")

def negateLastBranch(k, constraints):
  for j in range(k-1, -1, -1):
    if stack[j].done == False:
      break
    elif j == 0:
      print "Done with search!"
  constraints[j] = negateCons(constraints[j])
  stack[j].branch = negateDir(stack[j].branch)
  return constraints


def updateStack(branch, k):
  if k < len(stack):
    if stack[k].branch == branch:
      print "Error"
    elif k == len(stack) - 1:
      stack[k].branch = branch
      stack[k].branch = True
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
  #print "operation:",d
  isSymbolic1, isSymbolic2 = d["raddr1"] in A, d["raddr2"] in A
  if isSymbolic1 and isSymbolic2 and d["op"] != "*":
    A[d["laddr"]] = "(" + d["op"] +\
        " " + A[d["raddr1"]] + " " + A[d["raddr2"]] + ")"
  elif isSymbolic1:
    A[d["laddr"]] = "(" + d["op"] +\
        " " + A[d["raddr1"]] + " " + d["rval2"] + ")"
  elif isSymbolic2:
    A[d["laddr"]] = "(" + d["op"] +\
        " " + d["rval1"] + " " + A[d["raddr2"]] + ")"
  elif d["laddr"] in A:
    del A[d["laddr"]]

def matched_branch(d):
  isSymbolic1, isSymbolic2 = d["addr1"] in A, d["addr2"] in A
  if d["op"] == "==":
    d["op"] = "="
  if d["op"] == "!=":
    d["op"] = "/="
  if isSymbolic1 and isSymbolic2:
    c = "(" + d["op"] +\
        " " + A[d["addr1"]] + " " + A[d["addr2"]] + ")"
  elif isSymbolic1:
    c = "(" + d["op"] +\
        " " + A[d["addr1"]] + " " + d["val2"] + ")"
  elif isSymbolic2:
    c = "(" + d["op"] +\
        " " + d["val1"] + " " + A[d["addr2"]] + ")"
  else:
    return "true"

  if d["dir"] == "then":
    return c
  elif d["dir"] == "else":
    return negateCons(c)
  else:
    print "Unknown direction:",d["dir"]

def generateYicesInput(str):
  return ("(set-evidence! true)\n"
          + str
          + "(check)\n")

def runYices(yicesInput):
  f = open('yicesIn', 'w')
  f.write(yicesInput)
  f.close()
  f = open('input', 'w')
  subprocess.call([yices, 'yicesIn'], stdout=f)

if __name__ == "__main__":
  sys.exit(main())
