import sys
sys.path.append('.')

import argparse
import generator.generate_data as generate_data
import data_utils

def sample_context_phoneme_t(context, fv_to_symbols, objects_np):
    sample = set()
    for i in range(100):
        sample.add(generate_data.sample_context_phoneme(context, fv_to_symbols, objects_np))
    print(sample)

def sample_non_context_phoneme_t(context, fv_to_symbols, symbols, objects_np):
    sample = set()
    for i in range(100):
        sample.add(generate_data.sample_non_context_phoneme(context, objects_np, symbols, fv_to_symbols))
    print(sample)

def gen_random_word_t(w_len, rule, objects_np, symbols, fv_to_symbols):
    sample = set()
    for i in range(20):
        sample.add(generate_data.gen_random_word(w_len, rule, objects_np, symbols, fv_to_symbols))
    print(sample, len(sample))

def apply_rule_t(target, change, objects_np, symbols, symbol_to_fl, fv_to_symbols):
    sample = {}
    for i in range(100):
        input = generate_data.sample_context_phoneme(target, fv_to_symbols, objects_np)
        sample[input] = generate_data.apply_rule(input, change, symbol_to_fl, fv_to_symbols)
    print(sample)

def gen_triple_t(rule, fv_to_symbols, objects_np, symbol_to_fl):
    sample = set()
    for i in range(20):
        sample.add(generate_data.gen_rule_triple(rule, fv_to_symbols, objects_np, symbol_to_fl))
    print (sample, len(sample))

"""
DOCS
"""
def main():
    
    # process data
    input_filepath = f"data/f_data.tsv"
    output_filepath = "test/test_data/data_utils_test.npy"
    features_list_filepath = "test/test_data/data_utils_test.txt"
    columns_to_remove=('symbol',)

    # get neccesary objects
    feature_ordering, objects_np, symbols, symbol_to_fl, fv_to_symbols = \
        data_utils.preprocess_phoneme_data( input_filepath, output_filepath, 
                                            features_list_filepath, columns_to_remove)

    # rule to test
    rule = {'left': [0,0,0,-1], 'target': [0,0,0,1], 'right': [0,0,0,-1], 'change': [0,0,0,-1]}
    
    # tests running!
    sample_context_phoneme_t(rule['target'], fv_to_symbols, objects_np)
    sample_non_context_phoneme_t(rule['target'], fv_to_symbols, symbols, objects_np)
    gen_random_word_t(6, rule, objects_np, symbols, fv_to_symbols)
    apply_rule_t(rule['target'], rule['change'], objects_np, symbols, symbol_to_fl, fv_to_symbols)
    gen_triple_t(rule, fv_to_symbols, objects_np, symbol_to_fl)


if __name__ == "__main__":
    main()