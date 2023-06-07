import csv, itertools, unicodedata
import prague
import data_utils
import sat
import numpy as np
from flag import *

POSITIONS = ['left', 'target', 'right']

"""
ADD DOCS
"""
input_filepath = "data/features.tsv"
output_filepath = "data/features_data.npy"
features_list_filepath = f"data/features.txt"
FEAT_ORDERING, OBJ_NP, SYMBOLS, SYMBOL_TO_FL, FV_TO_SYMBOLS = \
  data_utils.preprocess_phoneme_data( input_filepath, output_filepath,
                                      features_list_filepath, columns_to_remove=('symbol',))

SYMBOL_MODIFIERS = {
  # add here later! TODO
}

"""
DOC
"""
def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

"""
DOCS
"""
def parse_word(word):
  phonemes = []
  for char in unicodedata.normalize('NFD', word):
    # TODO add error handling + symbol modifiers (?)
    phonemes.append(SYMBOL_TO_FL[char])

  return phonemes

"""
DOCS
"""
def parse(words):

  # DEBUG STATEMENT
  if (PARSE):
    print ("In phonologica.parse\n")
  # END DEBUG


  # data is a list of tuples of triples of feature vectors
  data = []
  for underlying_form, realization in words:

    # parse each word
    underlying_features = parse_word('#' + underlying_form + '#')
    realized_features = parse_word('#' + realization + '#')

    # add triples to data
    for u_triple, s_triple in zip(triples(underlying_features), triples(realized_features)):
      data.append((u_triple, s_triple))

  # DEBUG OUTPUT
  if (PARSE_V):
    print("parsed triples:\n")
    for (l, t, r), (sl, st, sr) in data:
      print("underlying triple: ", data_utils.get_phoneme(l, FV_TO_SYMBOLS), data_utils.get_phoneme(t, FV_TO_SYMBOLS), data_utils.get_phoneme(r, FV_TO_SYMBOLS))
      print("surface triple: ", data_utils.get_phoneme(sl, FV_TO_SYMBOLS), data_utils.get_phoneme(st, FV_TO_SYMBOLS), data_utils.get_phoneme(sr, FV_TO_SYMBOLS))
    print ("\n")
  # END DEBUG

  return data

"""
DOCS
"""
def infer_changes(data):

  # DEBUG STATEMENT
  if (P_CHANGE):
    print ("In phonologica.infer_changes\n")
  # END DEBUG

  # identify any phoneme that is different in the surface representation than in the underlying representation
  changes = [(old, new) for ((_, old, _), (_, new, _)) in data if prague.HashableArray(old) != prague.HashableArray(new)]
  changes_to_infer = set()

  # for every pair of changed phonemes
  for und_featv, sur_featv in changes:
    rule_target = []

    if (P_CHANGE_V):
      print("In phonologica.infer_changes:\nUnderlying Phoneme: ", und_featv, "\nSurface Phoneme: ", sur_featv)

    # evaluate every feature
    for idx in range(len(FEAT_ORDERING)):

      # first check for zero features (cannot be part of context)
      if und_featv[idx] == 0 or sur_featv[idx] == 0:
        rule_target.append(0)

      # if the feature is distinct, add to the feature vector
      elif und_featv[idx] != sur_featv[idx]:
        rule_target.append(sur_featv[idx])

      # otherwise, not part of rule
      else:
        rule_target.append(0)
    
    # add to set of changes seen
    changes_to_infer.add(prague.HashableArray(np.array(rule_target)))

  # DEBUG OUTPUT
  if (P_CHANGE_V):
    print ("Changes to infer: ", changes_to_infer)
  # END DEBUG

  # return a list of the changes, as partial feature vectors (np.arrays)
  return [change.unwrap() for change in changes_to_infer]

"""
DOCS
"""
def infer_rules(original_data, data, changes_to_infer, old_rules):

  rules = {}

  # for each change, infer the rule
  for change in changes_to_infer:

    # if this change has not been seen yet, add to rules
    if prague.HashableArray(change) not in old_rules.keys():
      rules[prague.HashableArray(change)] = infer_rule(data, change)

  # combine rules that were split and remove unsat changes
  rules |= old_rules
  rules, comb_cont = process_rules(rules)

  # examine pairwise to discover ordering
  # NOTE: rule_ordering = {1: [{rules}], 2: [...], ...}
  # and a rule now has the form {'left': [...], 'target': [...], 'right': [...], 'change': [...]}
  rule_ordering = infer_rule_order(rules, comb_cont, data)

  # work back from the original data
  new_data = apply_rules_from_surface(rule_ordering, original_data)

  # check to see if all rules have been discovered 
  # TODO add sanity check for unsat? Like none found...
  if check_data_equality(new_data):
    return rule_ordering
  else:
    return infer_rules(original_data, new_data, infer_changes(new_data), rules)

"""
DOCS
"""
def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule)

"""
DOCS
"""
def infer_rule_order(rules, comb_cont, data):
  return sat.infer_rule_order(rules, comb_cont, data)

"""
TODO
"""
def process_rules(rules):
  # if there is only one rule, return it
  if len(rules.keys()) == 1:
    return rules, {}
  
  new_rules = {}
  comb_contexts = {}
  
  # remove nulls
  for rule in rules.keys():
    if rules[rule] == None:
      del rules[rule]


  # TODO: this broke...
  # # examine every pair of rules
  # rule_pairs = list(itertools.combinations(rules.keys(), 2))
  # for rule1, rule2 in rule_pairs:

  #   # check if the two contexts are the same, merge change
  #   same = [prague.HashableArray(rules[rule1][position]) == prague.HashableArray(rules[rule2][position]) for position in POSITIONS]
  #   if all(same):
  #     #combine the changes to create new rule, TODO add error handling here
  #     new_rules[sat.combine_contexts(rule1, rule2)] = rules[rule1]

  #   # if they are not the same, record combined contexts to find feeding and counter-bleeding on focus interactions
  #   else:
  #     new_rules[rule1] = rules[rule1]  
  #     new_rules[rule2] = rules[rule2]

  #     # create combined left and right contexts
  #     left_comb = sat.combine_contexts(prague.HashableArray(rules[rule1]['left']), prague.HashableArray(rules[rule2]['left']))
  #     right_comb = sat.combine_contexts(prague.HashableArray(rules[rule1]['right']), prague.HashableArray(rules[rule2]['right']))
      
  #     # because were only using this to consider on focus exmaples, anything with conflicting contexts will not be recording
  #     if left_comb != None and right_comb != None:
  #       comb_contexts[(left_comb, right_comb)] = (rule1, rule2)

  # TODO: ADD DEBUG
  print("new_rules:", new_rules)
  print("comb_contexts",comb_contexts)

  # TODO: return new_rules
  return rules, comb_contexts

  # now that there are no duplicates, look for feeding on focus / counter-bleeding on focus


"""
docs
"""
def apply_rules_from_surface(rule_ordering, data):

  new_data = []
  # go through every triple
  for und_triple, sur_triple in data:
    # go through stratum backwards
    for stratum in reversed(range(len(rule_ordering.keys()))):
      # apply every rule in the stratum to the triple
      for rule in rule_ordering[stratum + 1]:
        new_data = []

        left = rule['left']
        target = rule['target']
        right = rule['right']
        change = rule['change']

        rule_apply = []
        rule_apply.append(data_utils.feat_vector_in_class(sur_triple[0], left, OBJ_NP))
        rule_apply.append(data_utils.feat_vector_in_class(sur_triple[1], change, OBJ_NP))
        rule_apply.append(data_utils.feat_vector_in_class(sur_triple[1], target, OBJ_NP))
        rule_apply.append(data_utils.feat_vector_in_class(sur_triple[2], right, OBJ_NP))

        # avoids vacuous application
        if all(rule_apply):
          sur_triple = (sur_triple[0], data_utils.apply_rule_backwards_to_fv(und_triple[1], sur_triple[1], change), sur_triple[2])

    # after all rules applied, add to new_data
    new_data.append((und_triple, sur_triple))
  return new_data



"""
docs
"""
def check_data_equality(data_in_triples):
  for und_triple, sur_triple in data_in_triples:
    # check every phoneme in triple
    for idx in range(3):
      if prague.HashableArray(und_triple[idx]) != prague.HashableArray(sur_triple[idx]):
        print(data_utils.get_phoneme(und_triple[idx-1], FV_TO_SYMBOLS), data_utils.get_phoneme(und_triple[idx], FV_TO_SYMBOLS), data_utils.get_phoneme(sur_triple[idx], FV_TO_SYMBOLS))
        return False
  
  # if every phoneme is identical, data is equal
  return True