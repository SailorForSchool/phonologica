import csv, itertools, unicodedata
import prague
import data_utils
import sat
import numpy as np
from flag import *

"""
ADD DOCS TODO
"""
input_filepath = "data/features.tsv"
output_filepath = "data/features_data.npy"
features_list_filepath = f"data/features.txt"
FEAT_ORDERING, OBJ_NP, SYMBOLS, SYMBOL_TO_FL, FV_TO_SYMBOLS = \
  data_utils.preprocess_phoneme_data( input_filepath, output_filepath,
                                      features_list_filepath, columns_to_remove=('symbol',))

# TODO? FEATURE_TO_INDEX???

SYMBOL_MODIFIERS = {
  # add here later! TODO
}

"""KEEP"""
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
def infer_rules(original_data, data, changes_to_infer):

  # for each change, infer the rule
  rules = {prague.HashableArray(change): infer_rule(data, change) for change in changes_to_infer}

  # combine rules that were split
  rules = combine_rules(rules)

  # examine pairwise to discover ordering
  # NOTE: rule_ordering = {1: [{rules}], 2: [...], ...}
  rule_pairs = list(itertools.combinations(rules, 2))
  rule_ordering = sat.infer_rule_order(rule_pairs, data)

  # work back from the original data
  new_data = apply_rules_from_surface(rule_ordering, original_data)

  # check to see if all rules ahve been discovered
  if all([prague.HashableArray(und) == prague.HashableArray(surf) for und, surf in data]):
    return rule_ordering
  else:
    return infer_rules(original_data, new_data, infer_changes(new_data))

"""
TODO: logic for single rule here
"""
def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule)

"""
TODO: apply the rules backwards here, use new quality of life features
"""
def apply_rules_from_surface(rule_ordering, original_data):
  pass

"""
TODO
"""
def combine_rules(rules):
  pass