import csv, itertools, unicodedata
import prague
import data_utils
import sat
import numpy as np
from flag import *

"""
ADD DOCS TODO
"""
FEAT_ORDERING, OBJ_NP, SYMBOLS, SYMBOL_TO_FL, FV_TO_SYMBOLS = \
  data_utils.preprocess_phoneme_data( input_filepath="data/features.tsv", output_filepath="data/feat_enc.npy",
                                      features_list_filepath="data/features.txt", columns_to_remove=('symbol',))

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


  # TODO equality?
  changes = [(old, new) for ((_, old, _), (_, new, _)) in data if old != new]
  changes_to_infer = set()

  # for every pair of changed phonemes
  for und_featv, sur_featv in changes:
    rule_target = []

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
    changes_to_infer.add(rule_target)

  # DEBUG OUTPUT
  if (P_CHANGE_V):
    print ("Changes to infer: ", changes_to_infer)
  # END DEBUG

  return changes_to_infer

"""
TODO: LOGIC FOR ITERATION HERE
"""
def infer_rules(data, change_rule):

  pass

"""
TODO: logic for single rule here
"""
def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule)

"""TODO"""
def combine_rules(rules):
  pass