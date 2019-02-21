from SAT import *
from collections import defaultdict

def create_sudoku(sudokuname="testsudoku.txt"):
    rules = open("sudoku-rules.txt")
    rules = "\n".join(rules.read().split("\n")[1:])
    sudoku = open(sudokuname).read()
    sudoku_dimacs = parse_sudoku_to_dimacs(sudoku)

    full_dimacs = rules + sudoku_dimacs
    nl = '\n'
    full_dimacs = f"p cnf 999 {full_dimacs.count(nl)}\n" +full_dimacs
    return full_dimacs


def parse_sudoku_to_dimacs(sudoku,output=False):
    clauses = ""
    for idx,char in enumerate(sudoku):
        if ord(char)>48 and ord(char)<=57:
            row_idx = int(idx/9)+1
            col_idx = idx%9+1
            num = int(char)
            clauses+= f"{row_idx}{col_idx}{num} 0\n"
    if output:print_sudoku(clauses)

    return clauses


def print_sudoku(dimacs):
    #to dict
    d = {int(int(s)/10):int(s)%10 for s in dimacs.split() if s.isdigit()}
    image = "-"*31+"\n"
    for row in range(1,10):
        #rows with
        for col in range(1,10):
            if (col-1) % 3 == 0: image += '|'
            if row*10+col in d:
                image+=f" {d[row*10+col]} "
            else:
                image+='   '
        image+='|\n'
        if row%3==0:image+= "-" * 31 + "\n"

    print(image)


def test_func():
    rules = open("sudoku-rules.txt")
    rules = "\n".join(rules.read().split("\n")[1:])
    sudoku = open("testsudoku.txt")
    for line in sudoku.read().split("\n"):
        if not line:continue
        sudoku_dimacs = parse_sudoku_to_dimacs(line,True)

        # variables, clauses = dimacs_to_datastructures(rules + sudoku_dimacs)
        # final = SAT_solver(variables, clauses,0)
        # print_sudoku(final)

        variables, clauses = dimacs_to_datastructures(rules+sudoku_dimacs)
        final = SAT_solver(variables, clauses,1)
        print_sudoku(final)





test_func()
# dimacs = create_sudoku()
# variables, clauses = dimacs_to_datastructures(dimacs)
#
# final = SAT_solver(variables,clauses)
# print_sudoku(final)
# import timeit
# print(timeit.timeit(lambda: SAT_solver(variables,clauses), number=10))