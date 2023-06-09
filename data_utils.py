from os.path import exists
import prague
import numpy as np
from funcy import *

"""
DOCS

"""
def preprocess_phoneme_data(input_filepath, output_filepath, features_list_filepath, columns_to_remove="None"):

    # get phonemes
    objects = prague.convert.load_objects(input_filepath)

    if (exists(output_filepath) and exists(features_list_filepath)):
        # get numpy vectors directly
        objects_np = np.load(output_filepath)

        # get feature ordering
        feature_ordering = []
        with open(features_list_filepath, 'r') as feature_file:
            for feature in feature_file:
                feature_ordering.append(feature.strip())

    else:
        # check well formedness
        prague.convert.have_universal_feature_definitions(objects, 
                                                        behavior='Exception')
        prague.convert.objects_are_unique(objects,
                                        features_to_ignore=None,
                                        behavior='Exception')

        # preprocess and transform
        preprocessed_objects = prague.convert.preprocess_objects(objects, 
                                                                keys_to_remove=columns_to_remove)

        # TODO: handle duplicates in future
        # get ordering of the features and convert, assuming no duplicates
        feature_ordering = tuple(sorted(preprocessed_objects[0].keys()))
        objects_np, _ = prague.convert.to_ternary_feature_vectors(preprocessed_objects,
                                                                feature_ordering=feature_ordering)
        
        # export to load in future
        prague.convert.export_ternary_feature_vectors(objects_np,
                                                    feature_ordering,
                                                    output_filepath,
                                                    features_list_filepath)

    # create symbols / feature maps
    symbols = [o['symbol'] for o in objects]
    symbol_to_fv = {o['symbol']:objects_np[i] for i,o in enumerate(objects)}
    fv_to_symbols = {prague.HashableArray(fv):{s for s in symbol_to_fv
                                               if np.array_equal(fv, symbol_to_fv[s])}
                     for fv in objects_np}

    return feature_ordering, objects_np, symbols, symbol_to_fv, fv_to_symbols


"""
DOCS
"""
def get_natural_class(partial_feat_list, fv_to_symbols, objects_np):

    # use to retrieve feature vectors (fv) for each phoneme in class
    feat_vectors = get_vector_ntrl_class(partial_feat_list, objects_np)

    # construct natural class
    nat_class = []
    for fv in feat_vectors:
        phonemes = fv_to_symbols[prague.HashableArray(fv)]
        nat_class += list(phonemes)

    # generate and output list of symbols
    return nat_class

"""
Docs
"""
def get_vector_ntrl_class(partial_feat_list, objects_np):
    # get list of objects described by partial feature vector (one hot)
    ext = prague.extension(np.array(partial_feat_list), objects_np)
    # use to retrieve feature vectors (fv) for each phoneme in class
    return(prague.extension_vector_to_objects(ext, objects_np))

"""
Docs
"""
def feat_vector_in_class(feat_vector, partial_feat_v, objects_np):
    # get natural class from partial feature vector
    nat_class = get_vector_ntrl_class(partial_feat_v, objects_np)

    # create hashable list
    nat_class = [prague.HashableArray(fv) for fv in nat_class]

    return prague.HashableArray(feat_vector) in nat_class

"""
DOCS
"""
def get_phoneme(feat_list, fv_to_symbols):
    return list(fv_to_symbols[prague.HashableArray(feat_list)])[0]

"""
DOC
"""
def apply_rule_to_phoneme(target_phoneme, change, symbol_to_fl, fv_to_symbols):

    # transform to feature vector
    feature_list = symbol_to_fl[target_phoneme]

    # generate new array
    new_array = apply_rule_to_fv(feature_list, change)
    
    # return phoneme
    return get_phoneme(new_array, fv_to_symbols)

"""
DOC
"""
def apply_rule_to_fv(target_fv, change):

    new_array = np.copy(target_fv)
    
    # create new phoneme target with changes
    for i, context_value in enumerate(change):
        if context_value != 0:
            new_array[i] = context_value

    # return the SR feature vector of the target
    return new_array

"""
DOCS
"""
def apply_rule_backwards_to_fv(und_fv,target_fv, change):

    new_array = np.copy(target_fv)
    
    # create new phoneme target with changes
    for i, context_value in enumerate(change):
        if context_value != 0:
            new_array[i] = und_fv[i]

    # return the SR feature vector of the target
    return new_array