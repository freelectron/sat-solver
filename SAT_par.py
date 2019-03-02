import os
import multiprocessing as mp
from time import time

from dp_wrapper import *
from collections import defaultdict
import pandas as pd


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
    d = {int(int(s) / 10): int(s) % 10 for s  in dimacs.split() if s.isdigit()}
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


def test_func(data_name="top870.sdk", rules_name="9x9"):
    rules_path = os.path.join('rules', "sudoku_rules_" + rules_name + ".txt")
    rules = open(rules_path)
    rules = "\n".join(rules.read().split("\n")[1:])
    sudoku = open(data_name + ".txt")

    t0 = time()

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

        # define an output que
        output_que = mp.Queue()

        # SAT_solver(variables, clauses, version=PT, moms=False,chronological=False, output_que=None)
        arg_list = [(variables, clauses, 0, False, False, output_que, 0),
                    (variables, clauses, 0, True, False, output_que, 1),
                    (variables, clauses, 1, False, False, output_que, 2),
                    (variables, clauses, 1, True, False, output_que, 3),
                    (variables, clauses, 1, False, True, output_que, 4),
                    (variables, clauses, 1, True, True, output_que, 5)]

        # Setup a list of processes that we want to run
        processes = [mp.Process(target=SAT_solver, args=arg_tup) for arg_tup in arg_list]

        # Run processes
        for p in processes:
            p.start()

        # Exit the completed processes
        for p in processes:
            p.join()

        # Get process results from the output queue
        results = [output_que.get() for p in processes]

        #results are retrurned in the order of faster completion
        for result in results:
            if result[-1] == 0:
                DP_correct, DP_final, DP_splits, DP_list_sat_clauses, _ = result
            elif result[-1] == 1:
                DP_moms_correct, DP_moms_final, DP_moms_splits, DP_moms_list_sat_clauses, _ = result
            elif result[-1] == 2:
                cdcl_correct, cdcl_final, cdcl_splits, cdcl_list_sat_clauses, _ = result
            elif result[-1] == 3:
                cdcl_moms_correct, cdcl_moms_final, cdcl_moms_splits, cdcl_moms_list_sat_clauses, _ = result
            elif result[-1] == 4:
                cdcl_chron_correct, cdcl_chron_final, cdcl_chron_splits, cdcl_chron_list_sat_clauses, _ = result
            else:
                cdcl_chron_moms_correct, cdcl_chron_moms_final, cdcl_chron_moms_splits, \
                cdcl_chron_moms_list_sat_clauses, _ = result

        # if c>10:
        #     break

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
            'cdcl_moms_list_sat_clauses': cdcl_moms_list_sat_clauses_list ,
            'cdcl_chron_list_sat_clauses': cdcl_chron_list_sat_clauses_list,
            'cdcl_chron_moms_list_sat_clauses': cdcl_chron_moms_list_sat_clauses_list
            }

    print('it took %2d seconds' % (time() - t0))

    df = pd.DataFrame(data=data)
    df.to_csv('df' + "_" + data_name + '_par.csv')



if __name__ == '__main__':
    test_func()
