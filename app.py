#!/usr/bin/env python3
from flask import Flask, abort, jsonify, request
import phonologica
import data_utils

from flag import *

app = Flask(__name__, static_url_path='')

@app.route('/')
def handle_homepage():
  return app.send_static_file('index.html')

@app.route('/api/infer_rules', methods=['POST'])
def handle_infer_rule():
  if not request.json or not 'wordStems' in request.json:
    abort(400)

  if (H_INFER):
    print("In app.handle_infer_rule\n")
  words = []
  for stem in request.json['wordStems']:
    words.append((stem['underlyingForm'], stem['realization']))

  if (H_INFER_V):
    print ("calling infer_rule with the following:\n\n", words, "\n")
  return jsonify(infer_rules(words))

"""
DOCS
"""
def format_rule(rule):
  f_rule = {}
  f_rule['context'] = {}
  for pos, feat_list in rule.items():
    context = []
    for idx, feat_value in enumerate(feat_list):
      if feat_value != 0:
        context.append({'feature': phonologica.FEAT_ORDERING[idx], 'positive': feat_value == 1})
    if pos == 'left' or pos == 'right':
      f_rule['context'][pos] = context
    elif pos == 'target':
      f_rule['phone'] = context
    else:
      f_rule[pos] = context


"""
DOCS
"""
def infer_rules(words):
  if (INFER):
    print("In app.infer_rule\n")
  
  # data is a list of tuples of triples of feature vectors
  # [(underlying_featv, surface_featv), (..., ...), ....]
  data = phonologica.parse(words)

  # list of partial feature vectors
  changes = phonologica.infer_changes(data)
  
  # dictionary with rule ordering, each "order" contains  rules - list of dictionaries with left, right, target, change
  rules = phonologica.infer_rules(data, data, changes, {})
  
  # TODO add inline here! Also won't appear on website...
  formated_rules = {}
  for stratum in rules.keys():
    for i, rule in enumerate(rules[stratum]):
      if(INFER_V):
        print(f"In stratum: {stratum}\n")
        print("\tleft: ", rule['left'])
        print("\tphone: ", rule['target'])
        print("\tright: ", rule['right'])
        print("\tchange: ", rule['change'], "\n")
    
    formated_rules[f'Stratum {stratum} - Rule {i}'] = format_rule(rule)

  return formated_rules
