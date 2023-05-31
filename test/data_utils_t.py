import sys
sys.path.append('.')
sys.path.append('./prague')

import data_utils
import argparse
import prague
import numpy as np
from funcy import *

"""
DOCS
"""
def preprocess_phoneme_data_t(input_filepath):

    output_filepath = "test/test_data/data_utils_test.npy"
    features_list_filepath = "test/test_data/data_utils_test.txt"
    columns_to_remove=('symbol',)

    feature_ordering, objects_np, symbols, symbol_to_fl, fv_to_symbols = data_utils.preprocess_phoneme_data(input_filepath, output_filepath, features_list_filepath, columns_to_remove)
    
    """ The following are sanity checks for above: """
    # print (feature_ordering)
    # print (objects_np)
    # print (symbol_to_fl['a'])
    # print(data_utils.get_natural_class([1, 0,0, 0], fv_to_symbols, objects_np))

"""
DOCS
"""
def main(args):
    preprocess_phoneme_data_t(args.input_filepath)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_filepath", type=str, required=True)

    args = parser.parse_args()
    print(vars(args))
    main(args)