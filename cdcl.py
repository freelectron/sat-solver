from constants import *


import sys
import random

def find_sat_value(literal):
    "finds the value that will satisfy the clause"
    if literal > 0:
        return True
    else:
        return False


def unit_clause(clause, data_pack):
    """
    :param clause:
    :param variables:
    :return: wheteter it is a unit clause, the unit variable, and the value it should be set to
    """
    for literal in clause[CLAUSE]:
        e = evaluate_literal(literal, data_pack)
        if e:
            return False, None, None  # there is allready a truth value
        elif e is UNDEFINED:
            for l in clause[CLAUSE]:
                if literal == l: continue
                if evaluate_literal(l, data_pack) is UNDEFINED:
                    return False, None, None
                elif evaluate_literal(l, data_pack):
                    return False, None, None
            return True, abs(literal), find_sat_value(literal)  # only if all other values are defined as true
    return False, None, None


def evaluate_literal(literal, data_pack):
    """ evaluates a literal"""
    var = abs(literal)
    variables = data_pack[VARIABLES]
    if variables[var][BOOL] == UNDEFINED:
        return UNDEFINED
    elif literal > 0:
        return variables[var][BOOL]
    else:
        return not variables[var][BOOL]


def evaluate_clause(clause, data_pack):
    """
    """
    truths = []
    inconsistent = INCONSISTENT
    for literal in clause[CLAUSE]:
        e = evaluate_literal(literal, data_pack)
        if e:
            return True, False
        elif e == UNDEFINED:
            inconsistent = False
    return False, inconsistent


def resolve_clauses(clause1, clause2):
    temp = clause1 | clause2
    for var in clause2:
        if -var in temp:
            temp.remove(var)
            temp.remove(-var)
    return temp


def find_conflict(clause_key, data_pack):
    clause = data_pack[CLAUSES][clause_key]
    implications = data_pack[IMPLICATIONS]

    checked_literals= set(clause[CLAUSE])
    checked_variables = set(clause[LITERALS])
    partial_clause = set(clause[CLAUSE])
    depth = data_pack[DEPTH]

    stack = set(checked_variables)
    while len(stack)>0:
        var = stack.pop()
        # print("resolving",var)
        #count the number of variabeles at the current depth still present in the clause
        if not var in implications:
            continue

        depth_counter = 0
        for c in partial_clause:
            if abs(c) in implications:
                if implications[abs(c)][1]==depth:
                    depth_counter+=1
                else:
                    pass
                    # print("older",c)
            elif abs(c) == data_pack[SPLITS][depth-1]:
                depth_counter+=1

        if depth_counter<=1:
            break

        second_clause_key = implications[var][0]#0 is clause key, 1 is depth

        second_clause = set([c for c in data_pack[CLAUSES][second_clause_key][CLAUSE] if c not in checked_literals])
        # print("evaluated second", evaluate_clause({CLAUSE: second_clause}, data_pack))
        # print("evaluated", evaluate_clause({CLAUSE: resolve_clauses(partial_clause,second_clause)}, data_pack))
        # if evaluate_clause({CLAUSE: resolve_clauses(partial_clause,second_clause)}, data_pack)[0] == True:
            # print("???")

        partial_clause = resolve_clauses(partial_clause,second_clause)
        # print([var for var in partial_clause])
        # print([f"{abs(var)}:{data_pack[VARIABLES][abs(var)][BOOL]}" for var in partial_clause])

        checked_literals = checked_literals | partial_clause
        for var in [abs(c) for c in second_clause]:
            if not var in checked_variables:
                stack.add(var)
                checked_variables.add(var)

    #
    # for var in set(partial_clause):
    #     if -var in partial_clause:
    #         partial_clause.remove(var)
    #         partial_clause.remove(-var)


    # print([var for var in partial_clause])
    # print([f"{abs(var)}:{data_pack[VARIABLES][abs(var)][BOOL]}" for var in partial_clause])
    # print("evaluated", evaluate_clause({CLAUSE: partial_clause}, data_pack))

    partial_clause = {CLAUSE: partial_clause, BOOL: False, TAUTOLOGY: False,
                      LITERALS: [abs(var) for var in partial_clause]}


    dpc = data_pack[CLAUSES]
    key = len(dpc)
    dpc[key] = partial_clause
    data_pack[UNSAT_CLAUSES][key] = partial_clause

    for var in partial_clause[LITERALS]:
        data_pack[VARIABLES][var][CLAUSE_INDEX].append(key)
        data_pack[VARIABLES][var][UNSAT_CLAUSES_IDX].append(key)

    if data_pack['chronological']:
        return sys.maxsize


    #find the lowest var occuring in the clauses
    lowest_var =data_pack[DEPTH] -1
    for var in partial_clause[LITERALS]:
        if lowest_var==0:
            break
        if var in implications:
            if lowest_var>implications[var][1]:
                lowest_var = implications[var][1]
        else:
            depth = data_pack[SPLITS].index(var)
            if lowest_var >depth:
                lowest_var = depth

    return lowest_var


def check_clause(clause_key, changed_literals, removed_clauses, data_pack):
    backtrack = None
    inconsistent = False
    if clause_key not in data_pack[UNSAT_CLAUSES]:
        return False, backtrack
    clause = data_pack[CLAUSES][clause_key]
    clause_evaluation, inconsistent = evaluate_clause(clause, data_pack)

    if clause_evaluation:
        del data_pack[UNSAT_CLAUSES][clause_key]
        removed_clauses[clause_key] = clause
        return True, backtrack

    if inconsistent is INCONSISTENT:
        backtrack = find_conflict(clause_key, data_pack)
        return INCONSISTENT, backtrack

    is_unit, var, val = unit_clause(clause, data_pack)
    if is_unit:
        data_pack[IMPLICATIONS][var] = (clause_key, data_pack[DEPTH])
        data_pack[VARIABLES][var][BOOL] = val
        changed_literals.append(var)
        del data_pack[UNSAT_CLAUSES][clause_key]
        removed_clauses[clause_key] = clause
        for unsta_var in clause[LITERALS]:
            data_pack[VARIABLES][unsta_var][UNSAT_CLAUSES_IDX].remove(clause_key)

        inconsistent, backtrack = resolve_unit_literals(var, changed_literals, removed_clauses, data_pack)

    return inconsistent, backtrack


def resolve_unit_literals(variable, changed_literals, removed_clauses, data_pack):
    "resolves an unit becoming a literal, cross removes clauses and removes corrosponding indexes"
    clause_keys = data_pack[VARIABLES][variable][CLAUSE_INDEX]
    for k in list(clause_keys):
        inconsistent, backtrack = check_clause(k, changed_literals, removed_clauses, data_pack)
        if inconsistent is INCONSISTENT:
            return inconsistent, backtrack

    return False, None

def undo_clause_deletion(changed_literals, removed_clauses, data_pack):
    for clause_key,clause in removed_clauses.items():
        for var in clause[LITERALS]:
            data_pack[VARIABLES][var][UNSAT_CLAUSES_IDX].append(clause_key)
    data_pack[UNSAT_CLAUSES] = {**data_pack[UNSAT_CLAUSES], **removed_clauses}

    for lit in changed_literals:
        if lit in data_pack[IMPLICATIONS]:
            del data_pack[IMPLICATIONS][lit]
        data_pack[VARIABLES][lit][BOOL] = UNDEFINED


def moms_search(data_pack,k=4):
    max_f_score = 0
    best_var = None
    best_key = None
    # print("moms")
    for key, var in data_pack[VARIABLES].items():
        min_size = sys.maxsize
        occurences = 0
        if not var[BOOL] == UNDEFINED:
            continue

        for clause_key in var[UNSAT_CLAUSES_IDX]:
            clause = data_pack[CLAUSES][clause_key]

            if len(clause[LITERALS])<min_size:
                min_size = len(clause[LITERALS])
            if min_size == len(clause[LITERALS]):
                occurences+=1

        first_term = occurences + len(data_pack[UNSAT_CLAUSES]) - len(var[UNSAT_CLAUSES_IDX])
        f_score = first_term*(2**k) + occurences*(len(data_pack[UNSAT_CLAUSES]) - len(var[UNSAT_CLAUSES_IDX]))
        if f_score>max_f_score:
            best_var = var
            best_key = key
            f_score = max_f_score
    return best_key, best_var

def recursive_cdcl(data_pack, depth=0, moms=False):
    changed_literals = []
    removed_clauses = {}
    
    global global_sat_clauses
    
    for clause_key, clause in list(data_pack[UNSAT_CLAUSES].items()):
        if not clause_key in data_pack[UNSAT_CLAUSES]:
            continue
        inconsistent, backtrack = check_clause(clause_key, changed_literals, removed_clauses, data_pack)
        if inconsistent is INCONSISTENT:
            global_sat_clauses.append(len(removed_clauses))
            undo_clause_deletion(changed_literals, removed_clauses, data_pack)
            return INCONSISTENT, backtrack

    global_sat_clauses.append(len(removed_clauses))
    if len(data_pack[UNSAT_CLAUSES]) == 0:
        return True, None

    # Make the split
    if not moms:
        for key, var in data_pack[VARIABLES].items():
            if var[BOOL] == UNDEFINED:
                    backtrack = None
                    data_pack[SPLITS].append(key)
                    for b in [True,False]:
                        # print("cdcl",depth)
                        var[BOOL] = b
                        data_pack[SAT_SPLITS] = data_pack[SAT_SPLITS] + 1

                        # number of removed clauses = number of satisfied clauses ?
                        data_pack[DEPTH] += 1
                        success, backtrack = recursive_cdcl(data_pack, depth + 1)
                        data_pack[DEPTH] -= 1

                        if success is INCONSISTENT:
                            # try the next run
                            if depth <= backtrack:
                                continue

                            data_pack[SPLITS].remove(key)
                            var[BOOL] = UNDEFINED
                            undo_clause_deletion(changed_literals, removed_clauses, data_pack)
                            if depth == backtrack + 1:
                                # we want to rerun this level
                                return recursive_cdcl(data_pack, depth)
                            return INCONSISTENT, backtrack
                        else:
                            return True, None

                    data_pack[SPLITS].remove(key)
                    var[BOOL] = UNDEFINED
                    undo_clause_deletion(changed_literals, removed_clauses, data_pack)
                    return INCONSISTENT, backtrack
    else:
        key,var = moms_search(data_pack)
        backtrack = None
        data_pack[SPLITS].append(key)
        for b in [True,False]:
            # print("cdcl moms",depth)
            var[BOOL] = b
            data_pack[SAT_SPLITS] = data_pack[SAT_SPLITS]+1

            # number of removed clauses = number of satisfied clauses ?
            data_pack[DEPTH]+=1
            success, backtrack = recursive_cdcl(data_pack, depth + 1)
            data_pack[DEPTH]-=1

            if success is INCONSISTENT:
                #try the next run
                if depth <= backtrack:
                    continue

                undo_clause_deletion(changed_literals, removed_clauses, data_pack)
                data_pack[SPLITS].remove(key)
                var[BOOL] = UNDEFINED
                if depth == backtrack+1:
                    # we want to rerun this level
                    return recursive_cdcl(data_pack, depth)
                return INCONSISTENT, backtrack
            else:
                return True, None

        data_pack[SPLITS].remove(key)
        var[BOOL] = UNDEFINED
        undo_clause_deletion(changed_literals, removed_clauses, data_pack)
        return INCONSISTENT, backtrack

def cdcl(clauses, variables, moms=False,chronological=False):
    """
    #base function
    """
    # init global variables
    # global global_len_clauses
    # global_len_clauses = len(clauses.items())
    # global global_sat_clauses
    # global_sat_clauses = []
    # global_sat_clauses.append(global_len_clauses)
    global global_sat_clauses
    global_sat_clauses = []
    data_pack = {CLAUSES: clauses, VARIABLES: variables, UNSAT_VARIABLES: set(VARIABLES), UNSAT_CLAUSES: dict(clauses),
                 IMPLICATIONS: {}, SPLITS: [], SAT_SPLITS:0,'chronological':chronological, "depth":0}
    success = recursive_cdcl(data_pack, moms=moms)[0]

    # print("cdcl splits:", data_pack[SAT_SPLITS])
    return success, data_pack[SAT_SPLITS], global_sat_clauses

# variables = {111: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              112: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None}}
# clauses = {0: {CLAUSE: set([-111, -112]), BOOL: False, LITERALS: [111, 112]},
#            1: {CLAUSE: set([111, 112]), BOOL: False, LITERALS: [111, 112]},
#            2: {CLAUSE: set([111, -112]), BOOL: False, LITERALS: [111, 112]},
#            3: {CLAUSE: set([-111, 112]), BOOL: False, LITERALS: [111, 112]}}
# print(cdcl(clauses, variables))
#
# variables = {111: {CLAUSE_INDEX: [0, 1], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              112: {CLAUSE_INDEX: [0, 1], BOOL: UNDEFINED, UNIT_CLAUSE: None}}
# clauses = {0:{CLAUSE: set([-111, -112]), BOOL: False,LITERALS:[111,112]}, 1:{CLAUSE: set([111, 112]), BOOL: False,LITERALS:[111,112]}}
#
# print(cdcl(clauses,variables))
# variables = {111: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              112: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              113: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              114: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None}}
# clauses = {0:{CLAUSE: set([-111, -112]), BOOL: False,LITERALS:[111,112]}, 1:{CLAUSE: set([111, 112]), BOOL: False,LITERALS:[111,112]},
#            2:{CLAUSE: set([111, -112]),BOOL: False,LITERALS:[111,112]}, 3:{CLAUSE: set([-111, 112,113]), BOOL: False,LITERALS:[111,112,113]}}
# print(cdcl(clauses,variables))
