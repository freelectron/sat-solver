from SAT import *
from collections import defaultdict


def create_sudoku(sudokuname="testsudoku.txt", rules_name="sudoku_rules_4x4"):
    rules = open(rules_name+".txt")
    rules = "\n".join(rules.read().split("\n")[1:])
    sudoku = open(sudokuname).read()
    sudoku_dimacs = parse_sudoku_to_dimacs(sudoku)

    full_dimacs = rules + sudoku_dimacs
    nl = '\n'
    full_dimacs = f"p cnf 999 {full_dimacs.count(nl)}\n" + full_dimacs
    return full_dimacs


def parse_sudoku_to_dimacs(sudoku, output=False):
    clauses = ""
    for idx, char in enumerate(sudoku):
        if ord(char) > 48 and ord(char) <= 57:
            row_idx = int(idx / 9) + 1
            col_idx = idx % 9 + 1
            num = int(char)
            clauses += f"{row_idx}{col_idx}{num} 0\n"
    if output: print_sudoku(clauses)

    return clauses


def print_sudoku(dimacs):
    # to dict
    d = {int(int(s) / 10): int(s) % 10 for s in dimacs.split() if s.isdigit()}
    image = "-" * 31 + "\n"
    for row in range(1, 10):
        # rows with
        for col in range(1, 10):
            if (col - 1) % 3 == 0: image += '|'
            if row * 10 + col in d:
                    image += f" {d[row * 10 + col]} "
            else:
                    image += '   '
            image += '|\n'
            if row % 3 == 0: image += "-" * 31 + "\n"

        print(image)


def test_func(data_name="1060_4x4", rules_name="sudoku_rules_4x4"):
    rules = open(rules_name + ".txt")
    rules = "\n".join(rules.read().split("\n")[1:])
    sudoku = open(data_name + ".txt")
    import pandas as pd

    DP_splits_list = list()
    DP_list_sat_clauses_list = list()
    DP_moms_splits_list = list()
    DP_moms_list_sat_clauses_list = list()
    cdcl_splits_list = list()
    cdcl_list_sat_clauses_list = list()
    cdcl_moms_splits_list = list()
    cdcl_moms_list_sat_clauses_list = list()
    cdcl_chron_splits_list = list()
    cdcl_chron_list_sat_clauses_list = list()

    cdcl_chron_moms_splits_list = list()
    cdcl_chron_moms_list_sat_clauses_list = list()

    sudoku_clauses_list = list()

    c = 0
    for line in sudoku.read().split("\n"):
        if not line: continue
        c += 1
        print(c)
        sudoku_dimacs = parse_sudoku_to_dimacs(line, False)
        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)

        DP_correct, DP_final, DP_splits, DP_list_sat_clauses = \
            SAT_solver(variables, clauses, 0, moms=False)

        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        DP_moms_correct, DP_moms_final, DP_moms_splits, DP_moms_list_sat_clauses = \
            SAT_solver(variables, clauses, 0, moms=True)

        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        cdcl_correct, cdcl_final, cdcl_splits, cdcl_list_sat_clauses = \
            SAT_solver(variables, clauses, 1, moms=False)

        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        cdcl_moms_correct, cdcl_moms_final, cdcl_moms_splits, cdcl_moms_list_sat_clauses = \
            SAT_solver(variables, clauses, 1, moms=True)

        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        cdcl_chron_correct, cdcl_chron_final, cdcl_chron_splits, cdcl_chron_list_sat_clauses = \
            SAT_solver(variables, clauses, 1, moms=False, chronological=True)

        variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        cdcl_chron_moms_correct, cdcl_chron_moms_final, cdcl_chron_moms_splits, cdcl_chron_moms_list_sat_clauses = \
            SAT_solver(variables, clauses, 1, moms=True, chronological=True)

        # print_sudoku(cdcl_final)
        # print_sudoku(cdcl_chron_final)
        # print_sudoku(cdcl_chron_moms_final)

        DP_splits_list.append(DP_splits)
        DP_moms_splits_list.append(DP_moms_splits)
        cdcl_splits_list.append(cdcl_splits)
        cdcl_moms_splits_list.append(cdcl_moms_splits)
        cdcl_chron_splits_list.append(cdcl_chron_splits)
        cdcl_chron_moms_splits_list.append(cdcl_chron_moms_splits)

        DP_list_sat_clauses_list.append(DP_list_sat_clauses)
        DP_moms_list_sat_clauses_list.append(DP_moms_list_sat_clauses)
        cdcl_list_sat_clauses_list.append(cdcl_list_sat_clauses)
        cdcl_moms_list_sat_clauses_list.append(cdcl_moms_list_sat_clauses)
        cdcl_chron_list_sat_clauses_list.append(cdcl_chron_list_sat_clauses)
        cdcl_chron_moms_list_sat_clauses_list.append(cdcl_chron_moms_list_sat_clauses)

        sudoku_clauses_list.append(len(sudoku_dimacs.split('\n')) - 1)

    data = {'DP_splits': DP_splits_list,
            'DP_moms_splits': DP_moms_splits_list,
            'cdcl_splits': cdcl_splits_list,
            'cdcl_moms_splits': cdcl_moms_splits_list,
            'cdcl_chron_splits': cdcl_chron_splits_list,
            'cdcl_chron_moms_splits': cdcl_chron_moms_splits_list,
            'sudoku_given_clauses': sudoku_clauses_list,

            'DP_list_sat_clauses': DP_list_sat_clauses_list,
            'DP_moms_list_sat_clauses': DP_moms_list_sat_clauses_list,
            'cdcl_list_sat_clauses': cdcl_list_sat_clauses_list,
            'cdcl_moms_list_sat_clauses': cdcl_moms_list_sat_clauses_list,
            'cdcl_chron_list_sat_clauses': cdcl_chron_list_sat_clauses_list,
            'cdcl_chron_moms_list_sat_clauses': cdcl_chron_moms_list_sat_clauses_list,
            }

    df = pd.DataFrame(data=data)
    df.to_csv('df' + "_" + data_name + '.csv')


test_func()
