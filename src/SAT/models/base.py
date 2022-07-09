from itertools import combinations
from operator import indexOf
from z3 import *
import numpy as np
import math
from components import heuristics


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

    ###  array of horizontal dimensions of the circuits
    widths = [ data_dict["dims"][c][0] for c in CIRCUITS]
    ###  array of vertical dimensions of the circuits
    heigths = [ data_dict["dims"][c][1] for c in CIRCUITS]

    ### define makespan boundaries
    sum_area = sum([heigths[c]*widths[c] for c in CIRCUITS])
    #min_makespan = round(sum_area / width)
    min_makespan = max(math.ceil(sum_area / width), max(heigths))
    #max_makespan = sum(heights)
    # max_makespan = max(
    #     min_makespan,  # max(heights), 
    #     sum(heigths) // (width // max(widths)))
    max_makespan = heuristics.compute_max_makespan(heigths, widths, width)
            
    solver = Solver()

    ### grid (linearized)
    domain = math.ceil(math.log2(width*max_makespan))
    grid = [ [Bool(f"point{p}_{coord}") for coord in range(domain)] for p in range(sum_area)]
    # i assign point p of the sum_area (point p of a circuit) to the coord on the board

    #int values for x coordinate of circuit c
    def x_int(c: int) -> int:
        point_of_sum_area = sum([heigths(i)*widths(i) for i in range(c)]) #TODO correct?
        bool_coord = grid(point_of_sum_area)
        point_of_grid = 0
        for digits in bool_coord:
            point_of_grid = (point_of_grid << 1) | digits
        return point_of_grid % width

    #int values for y coordinates of circuit c
    def y_int(c: int) -> int:
        point_of_sum_area = sum([heigths(i)*widths(i) for i in range(c)])
        bool_coord = grid(point_of_sum_area)
        point_of_grid = 0
        for digits in bool_coord:
            point_of_grid = (point_of_grid << 1) | digits
        return point_of_grid // width

    makespan = max([y_int[c] + heigths[c] for c in CIRCUITS])
    
    ### all circuits must have each dimension greater than zero
    assert(min(heigths > 0 and min(widths) > 0))
    assert(len(heigths) == len(widths) == n_circuits)

    #diffn: noOverlap
    #alldifferent(grid[]) se grid fosse di int
    #ma grid è un piano di bit -> alldifferent(strighe di bit)
    # per ogni coppia di stringhe almeno un bit deve essere diverso
    # And(#per ogni coppia di stringhe
    #     for s1 in range(grid.len):
    #         for s2 in range(grid.len):
    #             if s1<s2:
    #                 Or(
    #                 #almeno una coppia di bit è diversa
    #                     for bit in range(grid[s1].len):
    #                         #s1[bit] != s2[bit]
    #                         #Or( And(s1[bit], Not(s2[bit]), And(Not(s1[bit]), s2[bit]) )
    #                         Xor(s1[bit], s2[bit])
    #                 )
    # )
    #almeno una coppia di bit è diversa
    #Or([Xor(s1[bit], s2[bit]) for bit in range(grid[s1].len)])
    
    And([
        Or([Xor(s1[bit], s2[bit]) for bit in range(grid[s1].len)])
        for s1 in range(grid.len)
        for s2 in range(grid.len)
        if s1<s2
    ])

    

    solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    return solutions_dict


