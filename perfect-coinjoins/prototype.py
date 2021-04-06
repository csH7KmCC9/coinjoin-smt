#!/usr/bin/env python3
from pysmt.shortcuts import Symbol, And, Or, Not, Ite, GT, GE, LT, LE, Plus, Minus, Times, Equals, Int, Solver, get_model
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import QF_UFLIRA
from pysmt.typing import INT
from functools import reduce
from secrets import randbelow
import sys

#Example community CoinJoin config:
min_feerate = 5 #sats per vbyte target minimum
max_feerate = 11 #sats per vbyte maximum we're willing to pay
solver_iteration_timeout = 180000 #allowed to use up to 180 seconds per SMT solver call
min_output_amt = 30000 #minimum number of satoshis that can go to each output
min_output_amt_delta = 3000 #minimum number of satoshis that output amounts must differ by, if they differ
max_party_fragmentation_factor = 3 #if party provides x inputs, allow giving that party up to x times this number of outputs

#a list of (party, satoshis) tuples
example_inputs = [(1, 100000000),
(2, 130000000),
(3, 70000000), (3, 70000000),
(4, 107354073),
(5, 101063506),
(6, 122929194),
(7, 27490915), (7, 85582261),
(8, 58595885), (8, 22478305), (8, 22438276)]
#a set of (party, satoshis) tuples, maximum amounts each party is willing to pay
example_txfees = {(1, 757), (2, 500), (3, 1337), (4, 520), (5, 511), (6, 505), (7, 1030), (8, 1508)}

#auto-calculated constants given the example configuration above: 
parties = range(1, len(example_txfees) + 1)
num_inputs = len(example_inputs)

def parse_model_lines(model_lines):
  ret = dict()
  for line in model_lines:
    split = line.split(' := ')
    k = split[0]
    v = split[1]
    ret[k] = int(v)

  return ret

def recover_cj_config_from_model(model):
  selected_inputs = list()
  outputs = list()
  input_buf = list()
  output_buf = list()

  for i in range(0, model["max_outputs"]):
    party = model["output_party[%d]" % i]
    amt = model["output_amt[%d]" % i]
    if party != -1:
      output_buf.append((party, amt))
  while len(output_buf) > 0:
    x = randbelow(len(output_buf))
    outputs.append(output_buf.pop(x))

  for i in range(0, num_inputs):
    party = model["input_party[%d]" % i]
    amt = model["input_amt[%d]" % i]
    if party != -1:
      input_buf.append((party, amt))
  while len(input_buf) > 0:
    x = randbelow(len(input_buf))
    selected_inputs.append(input_buf.pop(x))

  return (selected_inputs, sorted(outputs, key = lambda x: x[1], reverse = True))

def bool_to_int(x):
    return Ite(x, Int(1), Int(0))

def solve_smt_problem(max_outputs, min_anonymity_score = None, timeout = None):
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
  max_outputs_sym = Symbol("max_outputs", INT) #the symbolic variable for max_outputs
  anonymity_score = Symbol("anonymity_score", INT) #see below for meaning. higher is better.
  txsize = Symbol("txsize", INT) #estimated tx size in vbytes, given the number of inputs and outputs in the tx
  txfee = Symbol("txfee", INT) #estimated tx fee, given the supplied feerate
  party_gives = dict() #party ID -> total satoshis on inputs contributed by that party
  party_gets = dict() #party ID -> total satoshis on outputs belonging to that party
  party_txfee = dict() #party ID -> satoshis contributed by that party towards the txfee
  party_numinputs = dict()
  party_numoutputs = dict()
  input_party = dict() #index into inputs -> party ID that contributed that input
  input_amt = dict() #index into inputs -> satoshis contributed by that input
  output_party = dict() #index into outputs -> party ID to whom the output belongs
  output_amt = dict() #index into outputs -> satoshis sent to that output
  output_score = dict() #index into outputs -> number of other outputs in the same amount not owned by that output's owner

  for (party, _) in example_txfees:
    party_gives[party] = Symbol("party_gives[%d]" % party, INT)
    party_gets[party] = Symbol("party_gets[%d]" % party, INT)
    party_txfee[party] = Symbol("party_txfee[%d]" % party, INT)
    party_numinputs[party] = Symbol("party_numinputs[%d]" % party, INT)
    party_numoutputs[party] = Symbol("party_numoutputs[%d]" % party, INT)
  for i in range(0, num_inputs):
    input_party[i] = Symbol("input_party[%d]" % i, INT)
    input_amt[i] = Symbol("input_amt[%d]" % i, INT)
  for i in range(0, max_outputs):
    output_party[i] = Symbol("output_party[%d]" % i, INT)
    output_amt[i] = Symbol("output_amt[%d]" % i, INT)
    output_score[i] = Symbol("output_score[%d]" % i, INT)

  #constraint construction:

  #party_txfee constraints:
  for (party, fee_contribution) in example_txfees:
    txfee_constraints.add(LE(party_txfee[party], Int(fee_contribution)))

  #input_party and input_amt bindings:
  for i in range(0, num_inputs):
    input_used_conditions = And(Equals(input_party[i],
                                       Int(example_inputs[i][0])),
                                Equals(input_amt[i],
                                       Int(example_inputs[i][1])))
    input_not_used_conditions = And(Equals(input_party[i],
                                           Int(-1)),
                                     Equals(input_amt[i],
                                           Int(0)))
    input_constraints.add(Or(input_used_conditions, input_not_used_conditions))

  #add constraints on output_party and output_amt:
  # -either output_party[i] == -1 and output_amt[i] == 0
  # -or else output_amt[i] > 0
  output_unused = list()
  for i in range(0, max_outputs):
    output_is_unused = Equals(output_party[i],
                              Int(-1))
    output_unused.append(output_is_unused)
    min_delta_satisfied = Or(output_is_unused,
                             And([Or(Equals(output_amt[i],
                                            output_amt[j]),
                                     Or(GE(output_amt[j],
                                           Plus(output_amt[i],
                                                Int(min_output_amt_delta))),
                                        LE(output_amt[j],
                                           Minus(output_amt[i],
                                                 Int(min_output_amt_delta)))))\
                                  for j in filter(lambda j: j != i, range(0, max_outputs))]))
    output_constraints.add(min_delta_satisfied)
    output_constraints.add(Ite(output_is_unused,
                               Equals(output_amt[i],
                                      Int(0)),
                               GT(output_amt[i],
                                  Int(min(0, min_output_amt-1)))))
  #calculate num_outputs and bind max_outputs:
  output_constraints.add(Equals(num_outputs, Plus([bool_to_int(Not(x)) for x in output_unused])))
  output_constraints.add(Equals(max_outputs_sym, Int(max_outputs)))

  #txfee, party_gets, and party_gives calculation/constraints/binding:
  for party in parties:
    #party_gives and input constraint/invariant
    owned_vec = list()
    amt_vec = list()
    for i in range(0, num_inputs):
      owned = Equals(input_party[i],
                     Int(party))
      amt = Ite(owned, input_amt[i], Int(0))
      owned_vec.append(bool_to_int(owned))
      amt_vec.append(amt)
    input_constraints.add(Equals(party_numinputs[party], Plus(owned_vec)))
    input_constraints.add(Equals(party_gives[party], Plus(amt_vec)))

    #txfee calculations:
    txfee_constraints.add(Equals(party_gets[party],
                                 Minus(party_gives[party],
                                       party_txfee[party])))

    #party_gets and output constraint/invariant:
    owned_vec = list()
    amt_vec = list()
    for i in range(0, max_outputs):
      owned = Equals(output_party[i],
                     Int(party))
      amt = Ite(owned, output_amt[i], Int(0))
      owned_vec.append(bool_to_int(owned))
      amt_vec.append(amt)
    output_constraints.add(Equals(party_gets[party], Plus(amt_vec)))
    output_constraints.add(Equals(party_numoutputs[party], Plus(owned_vec)))

    #build party fragmentation constraints:
    output_constraints.add(LE(party_numoutputs[party],
                              Times(Int(max_party_fragmentation_factor),
                                    party_numinputs[party])))

  #build anonymity set constraints:
  #each party should not have any uniquely-identifiable output:
  for (idx, amt) in output_amt.items():
    not_unique = Or(Equals(output_party[idx],
                           Int(-1)),
                    Or([And(Equals(v,
                                   amt),
                            Not(Equals(output_party[k],
                                       output_party[idx])))\
                        for (k, v) in filter(lambda x: x[0] != idx, output_amt.items())]))
    anonymityset_constraints.add(not_unique)

  #constrain the anonymity score, if set:
  def score_output(idx):  #how many other outputs in the same amount that do not belong to us?
    outputs_equal_not_ours = [And(Equals(v,
                                         output_amt[idx]),
                                  Not(Equals(output_party[k],
                                             output_party[idx])))\
                              for (k, v) in filter(lambda x: x[0] != idx, output_amt.items())]
    score = Plus([bool_to_int(x) for x in outputs_equal_not_ours])
    anonymityset_constraints.add(Equals(output_score[idx], score))
    return score
  anonymityset_constraints.add(Equals(anonymity_score, Plus([score_output(idx) for (idx, _) in output_amt.items()])))
  if min_anonymity_score is not None:
    anonymityset_constraints.add(GE(anonymity_score, Int(min_anonymity_score)))

  #set transaction invariants:
  invariants.add(Equals(total_in, Plus(total_out, txfee)))
  invariants.add(Equals(total_in, Plus([v for (k, v) in input_amt.items()])))
  invariants.add(Equals(total_in, Plus([v for (k, v) in party_gives.items()])))
  invariants.add(Equals(total_out, Plus([v for (k, v) in output_amt.items()])))
  invariants.add(Equals(total_out, Plus([v for (k, v) in party_gets.items()])))

  #build txfee calculation constraint: 11 + 68 * num_inputs + 31 * num_outputs
  num_used_inputs = Plus([party_numinputs[party] for party in parties])
  txfee_constraints.add(Equals(txsize,
                               Plus(Plus(Int(11),
                                         Times(Int(68),
                                               num_used_inputs)),
                                    Times(Int(31),
                                          num_outputs))))
  txfee_constraints.add(GE(txfee, Times(txsize, Int(min_feerate))))
  txfee_constraints.add(LE(txfee, Times(txsize, Int(max_feerate))))

  #finish problem construction:
  constraints = list()
  for x in [input_constraints, invariants, txfee_constraints,
            output_constraints, anonymityset_constraints]:
    for c in x:
      constraints.append(c)
  problem = And(constraints)

  with Solver(name='z3', solver_options={'timeout': solver_iteration_timeout}) as s:
    try:
      if s.solve([problem]):
        model_lines = sorted(str(s.get_model()).replace("'", "").split('\n'))
        result = ([s.get_py_value(num_outputs), s.get_py_value(anonymity_score)], parse_model_lines(model_lines))
        return result
      else:
        return None
    except SolverReturnedUnknownResultError:
      return None

def optimization_procedure():
  max_outputs = 3 * len(parties)
  min_outputs = max_outputs
  min_anonymity_score = 0
  anonymity_score_maximized = False
  best_model = None

  while True:
    if not anonymity_score_maximized:
      anonymity_score_threshold = min_anonymity_score + 1 if min_anonymity_score != 0 else 0
      result = solve_smt_problem(max_outputs, anonymity_score_threshold, timeout = solver_iteration_timeout)
    else:
      result = solve_smt_problem(min_outputs - 1, min_anonymity_score, timeout = solver_iteration_timeout)

    if result is None:
      print("------------------")
      print("No solution found")
      if not anonymity_score_maximized:
        if best_model is None:
          return (None, None, None) #we couldn't even solve the initial, most relaxed constraint. bail out.
        else:
          anonymity_score_maximized = True
          print("Now constraining anonymity score to >= %d and attempting to minimize transaction size" % min_anonymity_score)
      else:
        break
    else:
      print("------------------")
      min_outputs = result[0][0]
      min_anonymity_score = result[0][1]
      best_model = result[1]
      (selected_inputs, outputs) = recover_cj_config_from_model(best_model)
      print("%d inputs, %d outputs with anonymity score %d" % (len(selected_inputs), min_outputs, min_anonymity_score))
      print("inputs:")
      print(selected_inputs)
      print("outputs:")
      print(outputs)

  return (min_outputs, min_anonymity_score, best_model)

(min_outputs, min_anonymity_score, model) = optimization_procedure()
print("------------------")
if model is None:
    print("Could not find a CoinJoin solution with less than %d seconds of solver time" % (solver_iteration_timeout / 1000))
    sys.exit(1)
else:
  #randomly shuffle output order, then sort by decreasing amount:
  (selected_inputs, example_outputs) = recover_cj_config_from_model(model)
  def uniqueify(what):
    buf = set()
    for x in what:
      buf.add(x)
    return buf
  num_contributing_parties = len(uniqueify([x[0] for x in example_outputs]))

  print("Best CoinJoin solution found has %d inputs from %d parties:" % (len(selected_inputs), num_contributing_parties))
  print(selected_inputs)
  print("and has %d outputs with anonymity score %d:" % (min_outputs, min_anonymity_score))
  print(example_outputs)
  print("\nraw model:\n")
  print(model)
