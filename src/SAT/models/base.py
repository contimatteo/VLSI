from itertools import combinations
from operator import indexOf
from z3 import *
import numpy as np
import math


def at_least_one(bool_vars):
    return Or(bool_vars)

def at_most_one(bool_vars):
    return [Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(bool_vars):
    return at_most_one(bool_vars) + [at_least_one(bool_vars)]


def baseSAT(data_dict: dict) -> dict:
    #data_dict = {"data":str, "width": int, "n_circuits": int, "dims":[(w,h)]}

    solutions_dict = {"all_solutions": [], "solution": {}, "stats": [], "model": "base", "data": data_dict["data"], "solver": "z3 SAT1"}
    # each solution in all_solutions is a dict
    solution = {"width": data_dict["width"], "n_circuits": data_dict["n_circuits"], "widths": [], "heights": [], "x": [], "y": [], "min_makespan": int, "max_makespan": int, "makespan": int}
    solutions_dict["all_solutions"].append(solution)

    n_circuits = data_dict["n_circuits"]
    width = data_dict["width"]
    CIRCUITS = range(n_circuits)

    ###  array of horizontal dimension of the circuits
    widths = [ data_dict["dims"][c][0] for c in CIRCUITS]
    ###  array of vertical dimension of the circuits
    heigths = [ data_dict["dims"][c][1] for c in CIRCUITS]

    ### define makespan boundaries
    sum_area = sum([heigths[c]*widths[c] for c in CIRCUITS])
    min_makespan = round(sum_area / width)
    max_makespan = sum(heigths)

    solver = Solver()

    ### list of list of bools for x coordinates
    x = [[Bool(f"c'{i}") for i in range(width)] for c in CIRCUITS]
    ### list of list of bools for x coordinates
    y = [[Bool(f"c'{i}") for i in range(max_makespan - min(heigths))] for c in range(n_circuits)]
    
    #int values for x and y coordinates
    list_of_x_coord = [indexOf(x[c], True) for c in CIRCUITS]
    list_of_y_coord = [indexOf(y[c], True) for c in CIRCUITS]

    circuit_at_max_h = indexOf(list_of_y_coord, max(list_of_y_coord))
    makespan = list_of_y_coord[circuit_at_max_h] + heigths[circuit_at_max_h]

    ### grid (linearized)
    domain = math.ceil(math.log2(width*max_makespan))
    grid = [ [Bool(f"c{i}") for i in range(domain)] for c in range(sum_area)]


    
    ### all circuits must have each dimension greater than zero
    assert(min(heigths > 0 and min(widths) > 0))
    

    solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    return solutions_dict
