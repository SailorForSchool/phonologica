import z3
import prague
import phonologica
import data_utils
import itertools
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

"""
TODO
"""
def infer_rule_order(rules, comb_contexts, data):

  # check for edge case - one rule
  if len(rules.keys()) == 1:
    change = list(rules.keys())[0]
    return {1: [{'change': change.unwrap(), 'left': rules[change]['left'],'target': rules[change]['target'], 'right': rules[change]['right']}]}

  # list of tuples of pairwise ranking
  less_than = []
  # for ouput later
  ident_to_change = {str(change.unwrap()): change for change in rules.keys()}

  # classify interactions pairwise
  rule_pairs = list(itertools.combinations(rules.keys(), 2))
  for rule1, rule2 in rule_pairs:
    # TODO!!! add counterbleeding, feeding on focus consideration
    # infer order, remove extraneous rule
    
    # first try rule 1 - get rule dictionary and context dictionary
    P = rules[rule1]
    Q = rules[rule2]
    P_Q = (rule1, rule2)

    for _ in range(2):

      # for classifying
      feeding = []
      bleeding = []
      c_feeding = []
      c_bleeding = []

      # init boolean checks
      q_change = False
      ur_context = False
      sr_context = False
      change_context = False

      # examine underlying / surface data
      for und_triple, sur_triple in data:
        # examine for change
        if data_utils.feat_vector_in_class(sur_triple[1], P_Q[1].unwrap(), phonologica.OBJ_NP):
          q_change = True
        # examine for context in UR
        if data_utils.feat_vector_in_class(und_triple[0], Q['left'], phonologica.OBJ_NP) and data_utils.feat_vector_in_class(und_triple[2], Q['right'], phonologica.OBJ_NP):
          ur_context = True
        # examine for context in SR
        if data_utils.feat_vector_in_class(sur_triple[0], Q['left'], phonologica.OBJ_NP) and data_utils.feat_vector_in_class(sur_triple[2], Q['right'], phonologica.OBJ_NP):
          sr_context = True
        # examine for change in context
        if (data_utils.feat_vector_in_class(sur_triple[0], P_Q[0].unwrap(), phonologica.OBJ_NP) and data_utils.feat_vector_in_class(und_triple[0], P['target'], phonologica.OBJ_NP))\
           or (data_utils.feat_vector_in_class(sur_triple[2], P_Q[0].unwrap(), phonologica.OBJ_NP) and data_utils.feat_vector_in_class(und_triple[2], P['target'], phonologica.OBJ_NP)):
          change_context = True
        
        # if there is a rule inetraction in this example, classify
        if change_context and not all([q_change, sr_context, ur_context]) and any([sr_context, ur_context]):
          feeding.append(q_change and not ur_context and sr_context)

          if not feeding[-1]:
            print(data_utils.get_phoneme(und_triple[0], phonologica.FV_TO_SYMBOLS))
            print(data_utils.get_phoneme(und_triple[1], phonologica.FV_TO_SYMBOLS))
            print(data_utils.get_phoneme(und_triple[2], phonologica.FV_TO_SYMBOLS))
            print(q_change, ur_context, sr_context)


          c_feeding.append(not q_change and not ur_context and sr_context)
          c_bleeding.append(q_change and ur_context and not sr_context)
          bleeding.append(not q_change and ur_context and not sr_context)

      # if classified correctly for all examples, add ordering
      # TODO: add error processing, should be consistent

      # add check for each
      if (all(feeding) or all(bleeding)) and len(feeding) != 0:
        less_than.append(P_Q)
      elif (all(c_feeding) or all(c_bleeding)) and len(feeding) != 0:
        less_than.append((P_Q[1], P_Q[0]))

      # change P and Q and try other order
      P = rules[rule2]
      Q = rules[rule1]
      P_Q = (rule2, rule1)

    # determine order
    solver = z3.Optimize()

    # add all rules to model, make sure positive integers only
    z3_changes = {change_str: z3.Int(change_str) for change_str in ident_to_change.keys()}
    for ident in z3_changes.keys():
      solver.add(z3_changes[ident] > 0)


    # add all pairwise rankings
    for (change1, change2) in less_than:
      solver.add(z3_changes[str(change1.unwrap())] < z3_changes[str(change2.unwrap())])


    # check model
    if solver.check() == z3.sat:
      out = solver.model()
      print(out)
    else:
      return None # {1: [{'left':}], 2: [...]}

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
DOCS
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
  for counter_example, triple in zip(not_context, unchanged): # NOTE: triple is for debug

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

  # collect results and return rule
  if solver.check() == z3.sat:
    rule = {'left': [], 'target': [], 'right': []}
    model = solver.model()
    
    # add features that are included
    feat_included =[]
    pos_features = []
    for ident in model:
      if z3.is_true(model[ident]) and INCLUDED in str(ident):
        ident= str(ident).replace(INCLUDED, "")
        feat_included.append(idents_to_feat[ident])
      elif z3.is_true(model[ident]) and POSITIVE in str(ident):
        ident= str(ident).replace(POSITIVE, "")
        pos_features.append(idents_to_feat[ident])

    print(feat_included)

    # use to construct rule
    for position in POSITIONS:
      for feature in phonologica.FEAT_ORDERING:
        if (feature, position) in feat_included:
          value = (feature, position) in pos_features
          if value:
            rule[position].append(1)
          else:
            rule[position].append(-1)
        else:
          rule[position].append(0)

    print(rule)
    # rule is of the form {'position': [-1, 1, 0 ...], etc...}
    return rule

  else:
    print('unsat')
    return None
    
"""
NOTE: the contexts are hashable arrays, returns a hashable array
"""
def combine_contexts(context1, context2):

  context1_fv = context1.unwrap()
  context2_fv = context2.unwrap()
  new_context = []
  for feat in range(len(phonologica.FEAT_ORDERING)):
    
    if context1_fv[feat] != 0 and context2_fv[feat] !=0:
      
      # NOTE: it is not possible to have two contexts that will be input to combine with incompatible fv, so return None
      if context1_fv[feat] != context2_fv[feat]:
        return None
      
      # append common value
      else:
        new_context.append(context1_fv[feat])
    
    # otherwise take union 
    elif context1_fv[feat] == 0:
      new_context.append(context2_fv[feat])
    else:
      new_context.append(context1_fv[feat])
  
  return prague.HashableArray(new_context)