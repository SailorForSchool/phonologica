"""
DEBUG FLAGS

This file contains debugging flags to turn on
and off print statements in each section of
the codebase
"""

# make this false to turn off verbose flags
VERBOSE = True

APP = True
# flags for app.py
H_INFER = True
H_INFER_V = True
INFER = True
INFER_V = True

PHONOSYNTH = True
# flags for phonosynth.py
PARSE = False
PARSE_V = False
P_CHANGE = True
P_CHANGE_V = True

SAT = True
# flags for sat.py
S_INFER = True
S_INFER_V = True
S_INFERR = True
S_INFERR_V = True
S_APCH = True
S_APCH_V = False
S_QUERY = True


# for eachfile, if the master flag is false,
# all other flags should also be false
if (not APP):
    H_INFER = False
    H_INFER_V = False
    INFER = False
    INFER_V = False
if (not PHONOSYNTH):
    PARSE = False
    PARSE_V = False
    P_CHANGE = False
    P_CHANGE_V = False
if (not SAT):
    S_INFER = False
    S_INFER_V = False
    S_APCH = False
    S_APCH_V = False
    S_QUERY = False

if (not VERBOSE):
    H_INFER_V = False
    INFER_V = False
    PARSE_V = False
    P_CHANGE_V = False
    S_INFER_V = False
    S_APCH_V = False
