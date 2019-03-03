from dp_wrapper import *
from collections import defaultdict
# import pandas as pd
import os
from time import time
import logging

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


def test_func(sys_args=None, ):
    t0 = time()

    file = open(sys_args[2])
    rules_sudoku_dimacs = file.read()
    file.close()

    heuristic = sys_args[1]

    variables, clauses = dimacs_to_datastructures(rules_sudoku_dimacs)

    if heuristic == '-S1':
        print("simple DP algorithm is running.")
        correct, final, splits, list_sat_clauses, _ = \
            SAT_solver(variables, clauses, 0, moms=False)
    elif heuristic == '-S2':
        print("DP with MOMs algorithm is running.")
        correct, final, splits, list_sat_clauses, _ = \
            SAT_solver(variables, clauses, 0, moms=True)
    elif heuristic == '-S3':
        print("CDCL algorithm is running.")
        correct, final, splits, list_sat_clauses, _= \
            SAT_solver(variables, clauses, 1, moms=False)
    elif heuristic == '-S4':
        print("CDCL with MOMS algorithm is running.")
        correct, final, splits, list_sat_clauses, _ = \
            SAT_solver(variables, clauses, 1, moms=True)
    elif heuristic == '-S5':
        print("CDCL Chronological algorithm is running.")
        correct, final, splits, list_sat_clauses, _ = \
            SAT_solver(variables, clauses, 1, moms=False, chronological=True)
    elif heuristic == '-S6':
        print("CDCL Chronological with MOMs algorithm is running.")
        correct, final, splits, list_sat_clauses, _ = \
            SAT_solver(variables, clauses, 1, moms=True, chronological=True)
    else:
        print('Please specify a heuristic, either S1 , S2 ... S6')
        final = ":''("
        return
    with open(sys_args[2].split("/")[-1]+".out", "w+") as f:
        f.write(final)

    print('it took %2d seconds' % (time() - t0))

if __name__ == '__main__':
    logging.info("Script started...")
    test_func(sys.argv)
    logging.info("... script ended.")
