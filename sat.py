import z3
import prague
import phonologica
import data_utils
from flag import *

POSITIONS = ['left', 'target', 'right']
INCLUDED = ' included'
POSITIVE = ' positive'

"""
DOCS
"""
def to_ident(feature, position):
  return f'|{feature} {position}|'

"""
DOCS
"""
def infer_rule(data, change_rule):
  if (S_INFERR):
    print("In sat.infer_rules\n")
  
  # mark every triple that exhibits this change, remove vacuous applications
  triples_changed = []
  for und_rep, surf_rep in data:
    # if the change occurs here, consider
    if prague.HashableArray(surf_rep[1]) == prague.HashableArray(data_utils.apply_rule_to_fv(und_rep[1], change_rule)):
      # do not consider vacuous applications, remove
      if prague.HashableArray(surf_rep[1]) != prague.HashableArray(und_rep[1]):
        triples_changed.append(((und_rep, surf_rep), True))
    else:
      triples_changed.append(((und_rep, surf_rep), False))
  
  # DEBUG OUTPUT: in features not phoneme
  if (S_INFERR):
    print("For each triple, constraints are added based on relationship to change_rule.\n")

  if (S_INFER_V):
    print("changed triples: \n")
    for ((l, t, r), (ls, ts, rs)), b in triples_changed:
      if (b):
        print("features list - underlying triple: ", l, t, r)
        print("features list - surface triple: ", ls, ts, rs)

  if (S_INFER_V):
    print("non-changed triples: \n")
    for ((l, t, r), (ls, ts, rs)), b in triples_changed:
      if (not b):
        print("features list - underlying triple: ", l, t, r)
        print("features list - surface triple: ", ls, ts, rs)
  # DEBUG END

  # find rule
  rule = query_z3(triples_changed)
  return rule

def infer_rule_order(rule_pairs, data):
  for rule_1, rule_2 in rule_pairs:
    # get rule dictionary and context dictionary

    # first examine for feeding / bleeding relationship

    # then examine underlying data

    # determine order

    pass

"""
Docs
"""
def shared_features(triples):
  shared = None

  # get the contexts for the rule - left surface, target underlying, and right surface
  contexts = [(left, target, right) for (_, target, _), (left, _, right) in triples]

  # for each context, collect features seen
  for context in contexts:
    features = set()

    # for each context position, add into set
    for pos_idx, phone_fv in enumerate(context):
      features |= {((feature, POSITIONS[pos_idx]), value) for value, feature in zip(phone_fv, phonologica.FEAT_ORDERING) if value != '0'}
    
    # create shared set using intersection
    if shared == None:
      shared = features
    else:
      shared &= features

  # output format: {('feature', 'position') : value, ...} for every feature / position shared
  return dict(shared)

"""
Docs
"""
def collect_features(triples):
  feat_collection = []

  # get the contexts for the rule - left surface, target underlying, and right surface
  contexts = [(left, target, right) for (_, target, _), (left, _, right) in triples]

  # for each context, collect features seen
  for context in contexts:
    features = set()

    # for each context position, add into set
    for pos_idx, phone_fv in enumerate(context):
      features |= {((feature, POSITIONS[pos_idx]), value) for value, feature in zip(phone_fv, phonologica.FEAT_ORDERING) if value != '0'}

    # add to list of contexts
    feat_collection.append(dict(features))
  # output format: {('feature', 'position') : value, ...} for every feature / position shared
  return feat_collection

"""
TODO ????
"""
def apply_change(features, rule):

  new_features = dict(features)
  new_features.update(rule)

  # DEBUG OUTPUT: TODO could output the feature changed?
  if (S_APCH):
    print("In sat.apply_change\n")
  if (S_APCH_V):
    print("rule", rule, "\n")
  # END DBEUG

  return new_features

"""
TODO
"""
def query_z3(triples_changed):
  
  # compute context -> output format: {('feature', 'position') : value, ...} for every feature / position shared
  context = shared_features([triple for triple, changed in triples_changed if changed])

  # collect not context -> output format: [{('feature', 'position') : value, ...}, {...}, ...] for each triple
  not_context = collect_features([triple for triple, changed in triples_changed if not changed])
  unchanged = [triple for triple, changed in triples_changed if not changed]

  # DEBUG OUTPUT
  if(S_QUERY):
    print("context: ", context)
  # END DEBUG
  
  # create dictionary for converting z3 output from both of the above
  idents_to_feat = {to_ident(feature, position): (feature, position) for feature, position in context.keys()}

  # delete? TODO
  # for triple_context in not_context:
  #   for feature, position in triple_context.keys():
  #     idents_to_feat[to_ident(feature, position)] = (feature, position)
  
  # create solver for inference
  solver = z3.Optimize()

  # add a soft constraint against all variables to bias towards minimizing True values in the included set
  for ident in idents_to_feat.keys():
    solver.add_soft(z3.Not(z3.Bool(ident + INCLUDED)))

  # encode the known shared features of the change, if a feature is included then we can infer the value of the feature
  for (feature, position) in context.keys():
    # get value
    value = context[(feature, position)]
    
    # create a boolean that will encode if the value of a feature is positive (non zero value garenteed)
    feat_value = z3.Bool(to_ident(feature, position) + POSITIVE)

    # if the value is negative, then 'positive' must be false
    if value == -1:
      feat_value = z3.Not(feat_value)

    # add infered value
    solver.add(z3.Implies(z3.Bool(to_ident(feature, position) + INCLUDED), feat_value))

  # use counter-examples to determine which feature position pairs are necessary and their value
  conjunction = []
  for counter_example, triple in zip(not_context, unchanged):

    # for each example, consider which features exempted the triple from the rule
    example_constraints = []
    for (feature, position) in counter_example:

      # only consider features that are shared among examples
      if (feature, position) in context.keys():

        # get value
        value = counter_example[(feature, position)]

        # ignore matching values
        if value == context[(feature, position)]:
          continue

        # calculate feature value in rule to create counter-example
        not_feat_value = z3.Bool(to_ident(feature, position) + POSITIVE)
        if value == 1:
          not_feat_value = z3.Not(not_feat_value)
        # feat can have any value for 0
        elif value == 0:
          not_feat_value = True

        # if this is the feature that exempted the example, then the value in the context must be opposite of counter example
        included = z3.Bool(to_ident(feature, position) + INCLUDED)
        feat_is_constraint = z3.And(included, not_feat_value)
        feat_is_not_con = z3.Not(included)
        example_constraints.append(z3.Or(feat_is_constraint, feat_is_not_con))
    
    # add to counter examples
    if example_constraints != []:
      conjunction.append(z3.And(*example_constraints))
    
  # rule must satisfy all examples
  solver.add(z3.And(*conjunction))


  # TODO HERE
  if solver.check() == z3.sat:
    rule = {}
    model = solver.model()
    for ident in model:
      if z3.is_true(model[ident]):
        print(ident)
    #     feature, position = idents_to_features[str(ident)]
    #     rule[POSITIONS.index(position)][feature] = shared[(feature, position)]
    #     print ("rule: ", rule)
    return {'left': 0, 'right': 0, 'target': 0}
  else:
    print('unsat')
    return None




