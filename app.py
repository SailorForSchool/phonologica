#!/usr/bin/env python3
from flask import Flask, abort, jsonify, request
import phonologica

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
  # list of dictionaries with left, right, target, change
  simple_rules = phonologica.infer_rules(data, changes)
  # list of dictionaries with left, right, target, change (same as above)
  rules = phonologica.combine_rules(simple_rules)
  
  # TODO add inline here!
  formated_rules = []
  for i, rule in enumerate(rules):
    if(INFER_V):
      print("left: ", rule['left'])
      print("phone: ", rule['target'])
      print("right: ", rule['right'])
      print("change: ", rule['change'], "\n")
    
    formated_rules[f'Rule {i}'] = format_rule(rule)

  return formated_rules
