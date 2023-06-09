"""
FILE HEADER
"""
import sys
sys.path.append('.')
sys.path.append('./prague')

import argparse
import prague
import csv
import data_utils
import numpy as np

""" Here is the rule the data will be generated to follow """
# eighth fourth odd upper
rules = [{'target': [-1,-1,-1,-1], 'change': [0,1,0,0], 'left': [1, -1, 1, 0], 'right': [0,0,0,0] },
         {'target': [-1, 1, 0, 0], 'change': [0,0,0,1], 'left': [0,0,0,1], 'right': [0,0,0,1] }]


"""
Documentation
NOTE: no sanity check, must be done manually
"""
def generate_from_rule(name, rule, min = 3, max = 8, num_ex = 20, **kwargs):

    # get kwargs
    objects_np = kwargs['objects_np']
    symbols = kwargs['symbols']
    symbol_to_fl = kwargs['symbol_to_fl']
    fv_to_symbols = kwargs['fv_to_symbols']

    # create csv
    file = open(f'datasets/{name}.csv', 'w', newline='')
    writer = csv.writer(file)

    # for sanity checks in the future
    left_phonemes = []
    target_phonemes = []
    right_phonemes = []

    # generate number of examples as specified
    for word in range(num_ex):

        # for each word, determine the length of the word
        w_len = np.random.randint(min, max)

        # determine if the word will include the rule or not
        gen_rule = True if np.random.randint(0,2) == 1 else False

        if gen_rule:
            # TODO add hash condition here
            # only apply if there is enough phonemes for the rule to apply
            if w_len >= 2:

                # choose rule index
                rule_idx = np.random.randint(0, w_len - 1)

                # generate the rest of the word
                pre_word = gen_random_word(rule_idx, rule, objects_np, symbols, fv_to_symbols)
                post_word = gen_random_word(w_len - (rule_idx + 3), rule, objects_np, symbols, fv_to_symbols)

                # generate the rule TODO add sanity check lists
                u_triple, s_triple = gen_rule_triple(rule, fv_to_symbols, objects_np, symbol_to_fl)

                # create underlying and surface form
                und_form = pre_word + u_triple + post_word
                sur_form = pre_word + s_triple + post_word

                print("und: ", und_form, ", sur: ", sur_form)
                
                # write to file
                writer.writerow([und_form, sur_form])

        else:
            und_form = gen_random_word(w_len, rule, objects_np, symbols, fv_to_symbols)
            writer.writerow([und_form, und_form])

    # close output file
    file.close()

    # this is included in case sanity checks are added in the future
    return left_phonemes, target_phonemes, right_phonemes


"""
Documentation
"""
def generate_rule_interaction(old_data_name, new_data_name, rule, **kwargs):
    
    # get kwargs
    objects_np = kwargs['objects_np']
    symbol_to_fl = kwargs['symbol_to_fl']
    fv_to_symbols = kwargs['fv_to_symbols']

    # create csv
    file = open(f'datasets/{new_data_name}.csv', 'w', newline='')
    writer = csv.writer(file)

    # open file with data in it already
    csv_file = open(f'datasets/{old_data_name}.csv')
    csv_reader = csv.reader(csv_file, delimiter=',')

    # get rule sets
    left_phons = data_utils.get_natural_class(rule['left'], fv_to_symbols, objects_np)
    targ_phons = data_utils.get_natural_class(rule['target'], fv_to_symbols, objects_np)
    right_phons = data_utils.get_natural_class(rule['right'], fv_to_symbols, objects_np)

    # process row by row, changing 
    for u_rep, s_rep in csv_reader:

        # create list of phonemes
        new_word = list(s_rep)

        # check each triple
        for symbol_idx in range(1, len(new_word) - 1):
            rule_one_hot = []

            # otherwise, check each triple for rule context match
            rule_one_hot.append(new_word[symbol_idx-1] in left_phons)
            rule_one_hot.append(new_word[symbol_idx] in targ_phons)
            rule_one_hot.append(new_word[symbol_idx+1] in right_phons)

            # if context match 
            if all(rule_one_hot):
                # apply rule
                new_word[symbol_idx] = data_utils.apply_rule_to_phoneme(new_word[symbol_idx], rule['change'], symbol_to_fl, fv_to_symbols)
            
                print("prev: ", s_rep, " new: ", new_word)
        # write into the new dataset file
        writer.writerow([u_rep, ''.join(new_word)])



"""
DOCS
"""
def gen_random_word(w_len, rule, objects_np, symbols, fv_to_symbols):

    word = []
    left_phons = data_utils.get_natural_class(rule['left'], fv_to_symbols, objects_np)
    targ_phons = data_utils.get_natural_class(rule['target'], fv_to_symbols, objects_np)
    right_phons = data_utils.get_natural_class(rule['right'], fv_to_symbols, objects_np)

    # randomly sample from phoneme inventory to create word
    for _ in range(w_len):

        # sample random symbol
        phoneme_idx = np.random.randint(0, len(objects_np))
        phoneme = data_utils.get_phoneme(objects_np[phoneme_idx], fv_to_symbols)

        # add to word
        word.append(phoneme)

    # check for rule context - remove randomly
    for symbol_idx in range(1, w_len):
        rule_one_hot = []

        # if at the end of the word, stop looking, no context present
        if (symbol_idx + 2) > w_len:
            break

        # otherwise, check each triple for rule context match
        rule_one_hot.append(word[symbol_idx-1] in left_phons)
        rule_one_hot.append(word[symbol_idx] in targ_phons)
        rule_one_hot.append(word[symbol_idx+1] in right_phons)

        # if context match 
        if all(rule_one_hot):

            sample_phon = None

            while(sample_phon == None):

                # sample randomly
                idx_offest = np.random.randint(-1, 2)

                # resample chosen phoneme
                if idx_offest == -1:
                    context_violated = 'left'
                elif idx_offest == 0:
                    context_violated = 'target'
                elif idx_offest == 1:
                    context_violated = 'right'

                sample_phon = sample_non_context_phoneme(rule[context_violated],  objects_np, symbols, fv_to_symbols)

            word[symbol_idx + idx_offest] = sample_phon

    # return the word as a string
    return ''.join(word)
        
"""
DOCS
"""
def gen_rule_triple(rule, fv_to_symbols, objects_np, symbol_to_fl):
    # generate the rule
    l = sample_context_phoneme(rule['left'], fv_to_symbols, objects_np)
    t = sample_context_phoneme(rule['target'], fv_to_symbols, objects_np)
    r = sample_context_phoneme(rule['right'], fv_to_symbols, objects_np)
    c = data_utils.apply_rule_to_phoneme(t, rule['change'], symbol_to_fl, fv_to_symbols)

    return l+t+r, l+c+r
    

"""
Documentation
NOTE: can't sample from no context rules
"""
def sample_non_context_phoneme(context, objects_np, symbols, fv_to_symbols):

    phons = data_utils.get_natural_class(context, fv_to_symbols, objects_np)
    not_phons = [phoneme for phoneme in symbols if phoneme not in phons]

    if (len(not_phons) == 0):
        return None
    
    # sample randomly from list
    symbol_idx = np.random.randint(0, len(not_phons))

    return not_phons[symbol_idx]
    

"""
Documentation
"""
def sample_context_phoneme(context, fv_to_symbols, objects_np):
    phons = data_utils.get_natural_class(context, fv_to_symbols, objects_np)

    # sample randomly from list
    symbol_idx = np.random.randint(0, len(phons))
    return phons[symbol_idx]



"""
Documentation

NOTE: contexts are one hot encodings of partial feature vector
"""
def main(args):

    # get rules
    global rules
    
    # number of rules applied in file
    affix = 1

    # process features
    input_filepath = f"data/{args.tsv_name}.tsv"
    output_filepath = f"data/{args.tsv_name}_data.npy"
    features_list_filepath = f"data/{args.tsv_name}.txt"
    columns_to_remove=('symbol',)
    _, objects_np, symbols, symbol_to_fl, fv_to_symbols = \
        data_utils.preprocess_phoneme_data( input_filepath, output_filepath, 
                                            features_list_filepath, columns_to_remove)
    generate_from_rule(f"{args.data_name}_{affix}", rules[0], args.w_min, args.w_max, args.num_ex, input_filepath=input_filepath, objects_np=objects_np, symbols=symbols, symbol_to_fl=symbol_to_fl, fv_to_symbols=fv_to_symbols)
    

    if (args.mult_rules):
        for rule in rules[1:]:
            print("NEXT")
            generate_rule_interaction(f"{args.data_name}_{affix - 1}", f"{args.data_name}_{affix}", rule, objects_np=objects_np, symbol_to_fl=symbol_to_fl, fv_to_symbols=fv_to_symbols)
            affix += 1

    fw = open(f'datasets/{args.data_name}_metadata.csv', "w", newline='')
    writer = csv.DictWriter(fw, fieldnames=["left", "right", "target", "change"])
    writer.writeheader()
    writer.writerows(rules)
    fw.close()

"""
Documentation
"""
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--tsv_name", type=str, required=True)
    parser.add_argument("--data_name", type=str, required=True)
    parser.add_argument("--w_min", type=int, default=3)
    parser.add_argument("--w_max", type=int, default=8)
    parser.add_argument("--num_ex", type=int, default=20)
    parser.add_argument("--mult_rules", type=bool, default=False)

    args = parser.parse_args()
    print(vars(args))
    main(args)


