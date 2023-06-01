import prague
import numpy as np
from funcy import *

"""
DOCS

TODO: add check for npy / features and load instead
"""
def preprocess_phoneme_data(input_filepath, output_filepath, features_list_filepath, columns_to_remove="None"):

    # get phonemes
    objects = prague.convert.load_objects(input_filepath)

    # check well formedness
    prague.convert.have_universal_feature_definitions(objects, 
                                                    behavior='Exception')
    prague.convert.objects_are_unique(objects,
                                    features_to_ignore=None,
                                    behavior='Exception')

    # preprocess and transform
    preprocessed_objects = prague.convert.preprocess_objects(objects, 
                                                            keys_to_remove=columns_to_remove)

    # get ordering of the features and convert, assuming no duplicates
    feature_ordering = tuple(sorted(preprocessed_objects[0].keys()))
    objects_np, _ = prague.convert.to_ternary_feature_vectors(preprocessed_objects,
                                                            feature_ordering=feature_ordering)

    # create symbols / feature maps
    symbols = [o['symbol'] for o in objects]
    symbol_to_fv = {o['symbol']:objects_np[i] for i,o in enumerate(objects)}
    fv_to_symbols = {prague.HashableArray(fv):{s for s in symbol_to_fv
                                               if np.array_equal(fv, symbol_to_fv[s])}
                     for fv in objects_np}

    # export
    prague.convert.export_ternary_feature_vectors(objects_np,
                                                feature_ordering,
                                                output_filepath,
                                                features_list_filepath)

    return feature_ordering, objects_np, symbols, symbol_to_fv, fv_to_symbols


"""
DOCS
"""
def get_natural_class(partial_feat_list, fv_to_symbols, objects_np):

    # use to retrieve feature vectors (fv) for each phoneme in class
    feat_vectors = get_vector_nt_class(partial_feat_list, objects_np)

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
def get_vector_nt_class(partial_feat_list, objects_np):
    # get list of objects described by partial feature vector (one hot)
    ext = prague.extension(np.array(partial_feat_list), objects_np)
    # use to retrieve feature vectors (fv) for each phoneme in class
    return(prague.extension_vector_to_objects(ext, objects_np))

"""
Docs
"""
def feat_vector_in_class(feat_vector, partial_feat_v, objects_np):
    # get natural class from partial feature vector
    nat_class = get_vector_nt_class(partial_feat_v, objects_np)

    # create hashable list
    nat_class = [prague.HashableArray(fv) for fv in nat_class]

    return prague.HashableAraay(feat_vector) in nat_class

"""
DOCS
"""
def get_phoneme(feat_list, fv_to_symbols):
    return list(fv_to_symbols[prague.HashableArray(feat_list)])[0]
