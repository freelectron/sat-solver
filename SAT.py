import re
import sys

"""
All clauses have indexed all variabeles that it contains.
All variabeles have indexed in which clauses they occur.
If a clause is satisfied it will be removed from the dictionaries, and the corrosponding indexes will be removed from the variables.
If a Clause Becomse a Unit clause, and the clause will be satisfied.
Recursively now the clauses where the unit occurs in will evaluated.
"""





####Variables###
PT = 1
CLAUSE_INDEX = 'clause_index'
BOOL = 'bool'
CLAUSE = "clause"
TAUTOLOGY = "tautology"
UNIT_CLAUSE = 'unit_clause'
PURE_LITERAL = 'pure_literal'
UNDEFINED = None
INCONSISTENT = "inconsistent"
LITERALS = "literals"
SPLITTED = "splitted"

def dimacs_to_datastructures(dimacs):
    variables = {}
    clauses = {}
    for idx, row in enumerate(dimacs.split("\n")[1:]):
        if not row: continue
        if 'c' == row[0] :continue
        clause = re.findall(r'-?\d+', row.replace('0', ''))
        list_of_vars = []
        for var in clause:
            var = str(abs(int(var)))
            list_of_vars.append(var)
            if not var in variables:
                variables[var] = {CLAUSE_INDEX: [], BOOL: UNDEFINED, UNIT_CLAUSE: None,SPLITTED:False}
            variables[var][CLAUSE_INDEX].append(idx)

        clauses[idx] = {CLAUSE: clause, BOOL: False, TAUTOLOGY: False, LITERALS: list_of_vars}
    return variables, clauses


def tautology(clause):
    for var in clause[CLAUSE]:
        for check_var in clause[CLAUSE]:
            if int(var) == -int(check_var):
                return True
    return False


def unit_clause(clause, variables):
    """
    :param clause:
    :param variables:
    :return: wheteter it is a unit clause, the unit variable, and the value it should be set to
    """
    for literal in clause[CLAUSE]:
        e = evaluate_literal(literal, variables)
        if e:
            return False, None, None  # there is allready a truth value
        elif e is UNDEFINED:
            for l in clause[CLAUSE]:
                if literal == l: continue
                if evaluate_literal(l, variables) is UNDEFINED:
                    return False, None, None
                elif evaluate_literal(l, variables):
                    return False, None, None
            return True, str(abs(int(literal))), find_sat_value(literal)  # only if all other values are defined as true
    return False, None, None

def pure_literal(variable,clauses,variables):
    """"
    """
    clause_indexes = variables[variable][CLAUSE_INDEX]
    flag = UNDEFINED
    for index in clause_indexes:
        clause = clauses[index]
        for lit in clause[CLAUSE]:
            if str(abs(int(lit))) == variable:
                if flag == UNDEFINED:
                    flag = int(lit)>0
                elif flag == (int(lit)>0):
                    pass
                else:
                    return False
                break

    return True


def find_sat_value(literal):
    "finds the value that will satisfy the clause"
    if int(literal) > 0:
        return True
    else:
        return False


def evaluate_literal(literal, variables):
    "evaluates a literal"
    var = str(abs(int(literal)))
    if variables[var][BOOL] == UNDEFINED:
        return UNDEFINED
    elif int(literal) > 0:
        return variables[var][BOOL]
    else:
        return not variables[var][BOOL]


def evaluate_clause(clause, variables):
    """

    :param clause:
    :param variables:
    :return: if the clause is false/true
    """
    truths = []
    inconsistent = INCONSISTENT
    for literal in clause[CLAUSE]:
        e = evaluate_literal(literal, variables)
        if e:
            return True, False
        elif e == UNDEFINED:
            inconsistent = False
    return False, inconsistent


def check_clauses_validity(clauses):
    for c in clauses:
        if c[BOOL] == False:
            return False
    return True


def resolve_clause(clause_key, clauses, variables, changed_literals):
    """

    Sees if a clause can be resolved, or is a unit clause.
    :param clause_key:
    :param clauses:
    :param variables:
    :param changed_literals:
    :return: Inconsistent, removed clauses
    """
    if clause_key not in clauses:
        return False, {}
    clause = clauses[clause_key]
    clause_evaluation, inconsistent = evaluate_clause(clause, variables)

    if clause_evaluation:
        for l in clause[LITERALS]:
            variables[l][CLAUSE_INDEX].remove(clause_key)
        del clauses[clause_key]
        return inconsistent, {clause_key:clause}
    elif not inconsistent:
        # it might be a unit clause now
        is_unit, lit, val = unit_clause(clause, variables)
        if is_unit:
            variables[lit][BOOL] = val
            changed_literals.append(lit)
            incon, removed_clause = resolve_unit_literals(lit, clauses, variables, changed_literals)
            return incon, removed_clause
    return inconsistent,{}


def resolve_unit_literals(literal, clauses, variables, changed_literals):
    "resolves an unit becoming a literal, cross removes clauses and removes corrosponding indexes"
    clause_keys = variables[literal][CLAUSE_INDEX]
    removed_clauses = {}
    for k in list(clause_keys):
        inconsistent, r_clauses = resolve_clause(k, clauses, variables, changed_literals)
        removed_clauses = {**r_clauses, **removed_clauses}
        if inconsistent:
            return INCONSISTENT, removed_clauses
    return False, removed_clauses


def undo_clause_deletion(removed_clauses,changed_literals, clauses, variables):
    for k, c in removed_clauses.items():
        clauses[k] = c
        for l in c[LITERALS]:
            variables[l][CLAUSE_INDEX].append(k)
    for cl in changed_literals:
        variables[cl][BOOL] = UNDEFINED

def recursive_SAT_solver(clauses, variables,depth=0):
    """
    All changed literals and clauses will be stored
    :param clauses:
    :param variables:
    :param depth:
    :return:
    """
    changed_literals = []
    removed_clauses = {}
    #first try to solve for all variabeles, if all is satisfied we don't need to make splits
    for k,clause in list(clauses.items()):
        if not k in clauses:continue#we are changing the list while running
        inconsistent,r_c= resolve_clause(k, clauses, variables, changed_literals)
        removed_clauses = {**removed_clauses,**r_c}
        if inconsistent:
            undo_clause_deletion(removed_clauses,changed_literals,clauses,variables)
            return INCONSISTENT

    if len(clauses)==0:
        return True

    #We need to make a split
    for k in variables.keys():
        if variables[k][BOOL] == UNDEFINED:
            changed_literals.append(k)
            for b in [False,True]:
                variables[k][BOOL] = b
                # print(depth)
                success = recursive_SAT_solver(clauses,variables,depth+1)
                if success is INCONSISTENT:
                    continue
                else:
                    return True
            # noinspection PyUnreachableCode
            undo_clause_deletion(removed_clauses,changed_literals,clauses,variables)
            return INCONSISTENT

    undo_clause_deletion(removed_clauses, changed_literals, clauses, variables)
    return INCONSISTENT


def SAT_solver(variables, clauses, version=PT):
    # first check for tautologys
    for k, c in list(clauses.items()):
        if tautology(c):
            c[TAUTOLOGY] = True
            c[BOOL] = True
            resolve_clause(k, clauses, variables,[])
    correct = recursive_SAT_solver(clauses, variables)
    #determines if it is inconsistent
    if correct is INCONSISTENT:
        print("awwh inconsistent")
    else:
        print("hurray")

    t = ""
    for k, v in variables.items():
        if v[BOOL]:
            t+=f"{k} 0\n"
    return t




variables = {"111": {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None},
             "112": {CLAUSE_INDEX: [0, 1, 2, 3], BOOL: UNDEFINED, UNIT_CLAUSE: None}}
clauses = {0:{CLAUSE: ["111", "-112"], BOOL: False,LITERALS:['111','112']}, 1:{CLAUSE: ["111", "-112"], BOOL: False,LITERALS:['111','112']},
           2:{CLAUSE: ["111", "-112"], BOOL: False,LITERALS:['111','112']}, 3:{CLAUSE: ["111", "-112"], BOOL: False,LITERALS:['111','112']}}
print(pure_literal('112',clauses, variables))