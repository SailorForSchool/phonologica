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
    change = False
    target = und_rep[1]
    surface_t = surf_rep[1]

    # if the change occurs here, consider for this change_rule (no vacuous application)
    if prague.HashableArray(target) != prague.HashableArray(surface_t):
      
      # check each featuire for the correct combination of changes
      for (t_feat, s_feat, ch_feat) in zip(target, surface_t, change_rule):
        # check if a different rule applied
        if t_feat != s_feat and ch_feat == 0:
          change = False
          break
        # check if this rule did not apply
        elif t_feat == s_feat and ch_feat != 0:
          change = False
          break
        # if the rule applies, then we should see the change in the surface form
        elif t_feat != s_feat and s_feat == ch_feat:
          change = True
      
    triples_changed.append(((und_rep, surf_rep), change))
    
  # DEBUG OUTPUT: in features not phoneme
  if (S_INFERR):
    print("For each triple, constraints are added based on relationship to change_rule.\n")

  if (S_INFER_V):
    print("changed triples: \n")
    for ((l, t, r), (ls, ts, rs)), b in triples_changed:
      if (b):
        print("underlying triple: ", data_utils.get_phoneme(l, phonologica.FV_TO_SYMBOLS), data_utils.get_phoneme(t, phonologica.FV_TO_SYMBOLS), data_utils.get_phoneme(r, phonologica.FV_TO_SYMBOLS))
        print("surface triple: ", data_utils.get_phoneme(ls, phonologica.FV_TO_SYMBOLS), data_utils.get_phoneme(ts, phonologica.FV_TO_SYMBOLS), data_utils.get_phoneme(rs, phonologica.FV_TO_SYMBOLS))
  # DEBUG END

  # find rule
  return query_z3(triples_changed)

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
      features |= {((feature, POSITIONS[pos_idx]), value) for value, feature in zip(phone_fv, phonologica.FEAT_ORDERING) if value != 0}
    
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

        # examine if the value is opposite to that of the 'context'
        if value != context[(feature, position)]:
          # at least one of the features in common must be either missing or the value is does not match
          example_constraints.append(z3.Bool(to_ident(feature, position) + INCLUDED))

    # add to counter examples
    if example_constraints != []:
      conjunction.append(z3.Or(*example_constraints))
    
  # rule must satisfy all examples
  solver.add(z3.And(*conjunction))

  # TODO HERE
  if solver.check() == z3.sat:
    rule = {'left': [], 'target': [], 'right': []}
    model = solver.model()
    
    # add features that are included
    feat_included =[]
    for ident in model:
      if z3.is_true(model[ident]) and INCLUDED in str(ident):
        ident= str(ident).replace(INCLUDED, "")
        feat_included.append(idents_to_feat[ident])
    
  # TODO add values here!!!

    print(feat_included)

    # use to construct rule
    for position in POSITIONS:
      for feature in phonologica.FEAT_ORDERING:
        if (feature, position) in feat_included:
          value = z3.is_true(model[to_ident(feature, position) + POSITIVE])
          if value:
            rule[position].append(1)
          else:
            rule[position].append(-1)
        else:
          rule[position].append(0)

    print(rule)
    return rule

  else:
    print('unsat')
    return None




