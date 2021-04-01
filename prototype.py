#!/usr/bin/env python3
from pysmt.shortcuts import Symbol, And, Or, Not, Ite, GT, GE, LT, LE, Plus, Minus, Times, Equals, Int, Solver, get_model
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import QF_UFLIRA
from pysmt.typing import INT
from functools import reduce
from secrets import randbelow
import sys

#Example CoinJoin config:
#a list of (party, satoshis) tuples
example_inputs = [(1, 100000000), (2, 130000000), (3, 70000000), (3, 70000000)]
#a set of (party, satoshis) tuples
example_txfees = {(1, 0), (2, 17), (3, 0)}
#a set of (party, satoshis) tuples
example_cjfee = {(1, 0), (2, 28), (3, 5)}
#which party will be responsible for the bulk of the tx fees?
example_taker = 1
#how much? (0 means sweep all)
example_amt = 0
parties = range(1, len(example_txfees) + 1)

feerate = 5 #sats per vbyte target
solver_iteration_timeout = 60000 #allowed to use up to 60 seconds per SMT solver call

def parse_model_lines(model_lines):
  ret = dict()
  for line in model_lines:
    split = line.split(' := ')
    k = split[0]
    v = split[1]
    ret[k] = int(v)

  return ret

def solve_smt_problem(max_outputs, max_unique = None, timeout = None):
  #constraints:
  input_constraints = set()
  output_constraints = set()
  anonymityset_constraints = set()
  txfee_constraints = set()
  invariants = set()

  #variables:
  total_in = Symbol("total_in", INT) #total satoshis from inputs
  total_out = Symbol("total_out", INT) #total satoshis sent to outputs
  num_outputs = Symbol("num_outputs", INT) #num outputs actually used in the tx
  num_outputs_in_anonymity_set = Symbol("num_outputs_in_anonymity_set", INT) #num outputs that are not (unique or non-unique but all owned by the same party)
  txsize = Symbol("txsize", INT) #estimated tx size in vbytes, given the number of inputs and outputs in the tx
  txfee = Symbol("txfee", INT) #estimated tx fee, given the supplied feerate
  party_gives = dict() #party ID -> total satoshis on inputs contributed by that party
  party_gets = dict() #party ID -> total satoshis on outputs belonging to that party
  party_txfee = dict() #party ID -> satoshis contributed by that party towards the txfee
  party_cjfee = dict() #party ID -> satoshis earned by that party as a cjfee
  input_party = dict() #index into inputs -> party ID that contributed that input
  input_amt = dict() #index into inputs -> satoshis contributed by that input
  output_party = dict() #index into outputs -> party ID to whom the output belongs
  output_amt = dict() #index into outputs -> satoshis sent to that output
  output_not_unique = dict() #index into outputs -> 1 if output is uniquely identifiable, else 0
  main_cj_amt = Symbol("main_cj_amt", INT) #satoshi size of the outputs in the biggest anonymity set including all parties

  for (party, _) in example_txfees:
    party_gives[party] = Symbol("party_gives[%d]" % party, INT)
    party_gets[party] = Symbol("party_gets[%d]" % party, INT)
    party_txfee[party] = Symbol("party_txfee[%d]" % party, INT)
    party_cjfee[party] = Symbol("party_cjfee[%d]" % party, INT)
  for i in range(0, len(example_inputs)):
    input_party[i] = Symbol("input_party[%d]" % i, INT)
    input_amt[i] = Symbol("input_amt[%d]" % i, INT)
  for i in range(0, max_outputs):
    output_party[i] = Symbol("output_party[%d]" % i, INT)
    output_amt[i] = Symbol("output_amt[%d]" % i, INT)
    output_not_unique[i] = Symbol("output_not_unique[%d]" % i, INT)

  #constraint construction:

  #party_txfee and party_cjfee bindings:
  for (party, fee_contribution) in example_txfees:
    txfee_constraints.add(Equals(party_txfee[party], Int(fee_contribution)))
  for (party, fee) in example_cjfee:
    txfee_constraints.add(Equals(party_cjfee[party], Int(fee)))

  #input_party and input_amt bindings:
  for i in range(0, len(example_inputs)):
    input_constraints.add(Equals(input_party[i],\
                                 Int(example_inputs[i][0])))
    input_constraints.add(Equals(input_amt[i],\
                                 Int(example_inputs[i][1])))

  #add constraints on output_party and output_amt:
  # -either output_party[i] == -1 and output_amt[i] == 0
  # -or else output_amt[i] > 0
  output_is_used = list()
  for i in range(0, max_outputs):
    output_is_used.append(Ite(Equals(output_party[i],\
                                     Int(-1)),\
                              Int(0),\
                              Int(1)))
    output_constraints.add(Ite(Equals(output_party[i],\
                                      Int(-1)),\
                               Equals(output_amt[i],\
                                      Int(0)),\
                               GT(output_amt[i],\
                                  Int(0))))
  #calculate num_outputs:
  output_constraints.add(Equals(num_outputs, Plus(output_is_used)))

  #txfee, party_gets, and party_gives calculation/constraints/binding:
  for party in parties:
    #party_gives and input constraint/invariant
    input_constraints.add(Equals(party_gives[party],\
                                 Plus([Int(a)\
                                      for (p, a) in filter(lambda x: x[0] == party, example_inputs)])))

    #txfee calculations:
    if party != example_taker:
      txfee_constraints.add(Equals(party_gets[party],\
                                   Plus(party_cjfee[party],\
                                        Minus(party_gives[party],\
                                              party_txfee[party]))))
    else:
      fee_contributions = Plus([party_txfee[p] for p in filter(lambda x: x != example_taker, parties)])
      cjfees = Plus([party_cjfee[p] for p in filter(lambda x: x != example_taker, parties)])
      txfee_constraints.add(Equals(party_gets[party],\
                                   Plus(fee_contributions,
                                        Minus(party_gives[party],\
                                              Plus(cjfees,\
                                                   txfee)))))

    #party_gets and output constraint/invariant:
    amt_vec = list()
    for i in range(0, max_outputs):
      amt = Ite(Equals(output_party[i],\
                       Int(party)),\
                output_amt[i],\
                Int(0))
      amt_vec.append(amt)
    output_constraints.add(Equals(party_gets[party], Plus(amt_vec)))

  #build anonymity set constraints:
  #first, no matter what, we retain the core CoinJoin with the biggest anonymity set:
  num_outputs_at_main_cj_amt = Plus([Ite(Equals(v,\
                                                main_cj_amt),\
                                         Int(1),\
                                         Int(0))\
                                     for (k, v) in output_amt.items()])
  anonymityset_constraints.add(Equals(main_cj_amt,\
                                      Int(example_amt) if example_amt != 0 else party_gets[example_taker]))
  anonymityset_constraints.add(GE(num_outputs_at_main_cj_amt,\
                                  Int(len(parties))))

  #also, each party should only have at most one output not part of any anonymity set:
  for party in parties:
    def belongs_and_unique(idx):  #does it belong to party, and is it unique among output amounts?
      disequal = [Not(Equals(v, output_amt[idx])) for (k, v) in filter(lambda x: x[0] != idx, output_amt.items())]
      return And(Equals(output_party[idx],\
                        Int(party)),\
                 And(disequal))
    unique_amt_count = Plus([Ite(belongs_and_unique(k),\
                                 Int(1),\
                                 Int(0)) \
                             for (k, v) in output_amt.items()])
    anonymityset_constraints.add(LE(unique_amt_count, Int(1)))

  #calculate how many outputs are uniquely identifiable:
  in_anonymity_set = list()
  for (idx, amt) in output_amt.items():
    not_unique = Or([And(Equals(v,\
                                amt),\
                         Not(Equals(output_party[k],\
                                    output_party[idx])))\
                     for (k, v) in filter(lambda x: x[0] != idx, output_amt.items())])
    anonymityset_constraints.add(Equals(output_not_unique[idx],\
                                        Ite(not_unique,\
                                            Int(1),\
                                            Int(0))))
    in_anonymity_set.append(output_not_unique[idx])
  anonymityset_constraints.add(Equals(num_outputs_in_anonymity_set,
                                      Plus(in_anonymity_set)))

  #constrain (if set) the number of uniquely-identifiable outputs
  #(i.e. those not in an anonymity set with cardinality > 1):
  if max_unique is not None:
    anonymityset_constraints.add(LE(Minus(num_outputs,
                                          num_outputs_in_anonymity_set),
                                    Int(max_unique)))

  #set transaction invariants:
  invariants.add(Equals(total_in, Plus(total_out, txfee)))
  invariants.add(Equals(total_in, Plus([v for (k, v) in input_amt.items()])))
  invariants.add(Equals(total_in, Plus([v for (k, v) in party_gives.items()])))
  invariants.add(Equals(total_out, Plus([v for (k, v) in output_amt.items()])))
  invariants.add(Equals(total_out, Plus([v for (k, v) in party_gets.items()])))

  #build txfee calculation constraint: 11 + 68 * num_inputs + 31 * num_outputs
  txfee_constraints.add(Equals(txsize,
                               Plus(Int(11 + 68 * len(example_inputs)),
                               Times(Int(31),
                                     num_outputs))))
  txfee_constraints.add(Equals(txfee, Times(txsize, Int(feerate))))

  #finish problem construction:
  constraints = list()
  for x in [input_constraints, invariants, txfee_constraints,\
            output_constraints, anonymityset_constraints]:
    for c in x:
      constraints.append(c)
  problem = And(constraints)

  with Solver(name='z3', solver_options={'timeout': solver_iteration_timeout}) as s:
    try:
      if s.solve([problem]):
        model_lines = sorted(str(s.get_model()).replace("'", "").split('\n'))
        result = ([s.get_py_value(num_outputs), s.get_py_value(num_outputs_in_anonymity_set)], parse_model_lines(model_lines))
        return result
      else:
        return None
    except SolverReturnedUnknownResultError:
      return None

def optimization_procedure():
  needed_outputs = 3 * len(parties)
  min_outputs = needed_outputs
  max_unique = len(parties)
  max_unique_minimized = False

  while True:
    if not max_unique_minimized:
      result = solve_smt_problem(needed_outputs, max_unique - 1, timeout = solver_iteration_timeout)
    else:
      result = solve_smt_problem(min_outputs - 1, max_unique, timeout = solver_iteration_timeout)

    if result is None:
      print("------------------")
      print("No solution found")
      if not max_unique_minimized:
        max_unique_minimized = True
        print("max_unique has been minimized at %d" % max_unique)
      else:
        break
    else:
      print("------------------")
      min_outputs = result[0][0]
      max_unique = result[0][0] - result[0][1]
      if max_unique == 0:
        max_unique_minimized = True
      print("%d outputs with %d uniquely identifiable" % (min_outputs, max_unique))

  return (min_outputs, max_unique)

(min_outputs, max_unique) = optimization_procedure()
result = solve_smt_problem(min_outputs, max_unique)
assert(result is not None)
assert(result[0][0] == min_outputs)
assert(result[0][1] == (min_outputs - max_unique))
print("------------------")
print("Best CoinJoin solution found has %d outputs, of which %d are uniquely identifiable:\n" % (min_outputs, max_unique))

#randomly shuffle output order, then sort by decreasing amount:
example_outputs = list()
output_buf = list()
for i in range(0, min_outputs):
  output_buf.append((result[1]["output_party[%d]" % i], result[1]["output_amt[%d]" % i]))
while len(output_buf) > 0:
  x = randbelow(len(output_buf))
  example_outputs.append(output_buf.pop(x))
print(sorted(example_outputs, key = lambda x: x[1], reverse = True))

print("\nraw model:\n")
print(result[1])
