from constants import *

CLAUSES = "clauses"
VARIABLES = "variables"
UNSAT_VARIABLES = "unsat_variables"
IMPLICATIONS = "implications"
UNSAT_CLAUSES = "unsat clauses"
SPLITS = "splits"
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

    checked_variables = set(clause[LITERALS])
    partial_clause = set(clause[CLAUSE])


    stack = set(checked_variables)
    while len(stack)>0:
        var = stack.pop()
        if not var in implications:
            continue
        second_clause_key = implications[var]
        second_clause = data_pack[CLAUSES][second_clause_key][CLAUSE]
        partial_clause= partial_clause  | second_clause

        # partial_vars = set([abs(c) for c in partial_clause])

        for var in [abs(c) for c in second_clause]:
            if not var in checked_variables:
                stack.add(var)
                checked_variables.add(var)
    for var in set(partial_clause):
        if -var in partial_clause:
            partial_clause.remove(var)
            partial_clause.remove(-var)


    # print([var for var in partial_clause])
    # print([f"{abs(var)}:{data_pack[VARIABLES][abs(var)][BOOL]}" for var in partial_clause])

    partial_clause = {CLAUSE: partial_clause, BOOL: False, TAUTOLOGY: False,
                      LITERALS: [abs(var) for var in partial_clause]}

    ev, _ = evaluate_clause(partial_clause,data_pack)
    if ev:
        # print("evaluated to true")
        pass


    dpc = data_pack[CLAUSES]
    idx = len(dpc)
    dpc[idx] = partial_clause
    data_pack[UNSAT_CLAUSES][idx] = partial_clause
    for var in partial_clause[LITERALS]:
        data_pack[VARIABLES][var][CLAUSE_INDEX].append(idx)

    for splits in data_pack[SPLITS]:
        for var in partial_clause[LITERALS]:
            if var == splits:
                return 10000  # backtrack
    return None


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
        data_pack[IMPLICATIONS][var] = clause_key
        data_pack[VARIABLES][var][BOOL] = val
        changed_literals.append(var)
        del data_pack[UNSAT_CLAUSES][clause_key]
        removed_clauses[clause_key] = clause
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
    data_pack[UNSAT_CLAUSES] = {**data_pack[UNSAT_CLAUSES], **removed_clauses}
    for lit in changed_literals:
        if lit in data_pack[IMPLICATIONS]:
            del data_pack[IMPLICATIONS][lit]
        data_pack[VARIABLES][lit][BOOL] = UNDEFINED


def recursive_cdcl(data_pack, depth=0, moms=False):
    changed_literals = []
    removed_clauses = {}
    for clause_key, clause in list(data_pack[UNSAT_CLAUSES].items()):
        if not clause_key in data_pack[UNSAT_CLAUSES]:
            continue
        inconsistent, backtrack = check_clause(clause_key, changed_literals, removed_clauses, data_pack)
        if inconsistent is INCONSISTENT:
            undo_clause_deletion(changed_literals, removed_clauses, data_pack)
            return INCONSISTENT, backtrack

    if len(data_pack[UNSAT_CLAUSES]) == 0:
        return True, None

    # Make the split
    if not moms:
        for key, var in data_pack[VARIABLES].items():
	        if var[BOOL] == UNDEFINED:
	            backtrack = None
	            data_pack[SPLITS].append(key)
	            for b in [True,False]:
	                # print(depth)
	                var[BOOL] = b
	                data_pack[SAT_SPLITS] = data_pack[SAT_SPLITS]+1
	                success, backtrack = recursive_cdcl(data_pack, depth + 1)

	                if success is INCONSISTENT:
	                    if depth < backtrack:
	                        continue
	                    if depth == backtrack+1:
	                        recursive_cdcl(data_pack,depth+1)

	                    data_pack[SPLITS].remove(key)
	                    var[BOOL] = UNDEFINED
	                    undo_clause_deletion(changed_literals, removed_clauses, data_pack)

	                    # if depth == backtrack:
	                    #     return recursive_cdcl(data_pack,depth)

	                    return INCONSISTENT,backtrack
	                else:
	                    return True, None

	            data_pack[SPLITS].remove(key)
	            var[BOOL] = UNDEFINED
	            undo_clause_deletion(changed_literals, removed_clauses, data_pack)
	            return INCONSISTENT, backtrack
    else:
        moms_variables = dict(reversed(sorted(data_pack[VARIABLES].items(), key=lambda kv: len(kv[1]['unsat_clauses']))))
        for key in moms_variables.keys():
            var = data_pack[VARIABLES][key]
            if var[BOOL] == UNDEFINED:
                backtrack = None
                data_pack[SPLITS].append(key)
                for b in [True,False]:
	                # print(depth)
	                var[BOOL] = b
	                data_pack[SAT_SPLITS] = data_pack[SAT_SPLITS]+1
	                success, backtrack = recursive_cdcl(data_pack, depth + 1)

	                if success is INCONSISTENT:
	                    if depth < backtrack:
	                        continue
	                    if depth == backtrack+1:
	                        recursive_cdcl(data_pack,depth+1)
	                    
	                    data_pack[SPLITS].remove(key)
	                    var[BOOL] = UNDEFINED
	                    return INCONSISTENT,backtrack
	                else:
	                    return True, None
                data_pack[SPLITS].remove(key)
                var[BOOL] = UNDEFINED
                undo_clause_deletion(changed_literals, removed_clauses, data_pack)
                return INCONSISTENT, backtrack



    

def cdcl(clauses, variables, moms=False):
    """
    #base function
    """
    data_pack = {CLAUSES: clauses, VARIABLES: variables, UNSAT_VARIABLES: set(VARIABLES), UNSAT_CLAUSES: dict(clauses),
                 IMPLICATIONS: {}, SPLITS: [], SAT_SPLITS:0}
    success = recursive_cdcl(data_pack, moms=moms)[0]

    # print("cdcl splits:", data_pack[SAT_SPLITS])
    return success, data_pack[SAT_SPLITS]
#
# variables = {111: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
#              112: {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None}}
# clauses = {0: {CLAUSE: set([-111, -112]), BOOL: False, LITERALS: [111, 112]},
#            1: {CLAUSE: set([111, 112]), BOOL: False, LITERALS: [111, 112]},
#            2: {CLAUSE: set([111, -112]), BOOL: False, LITERALS: [111, 112]},
#            3: {CLAUSE: set([-111, 112]), BOOL: False, LITERALS: [111, 112]}}
# print(cdcl(clauses, variables))

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
