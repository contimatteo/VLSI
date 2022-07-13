import z3
import numpy as np


def baseSAT(data_dict: dict) -> dict:
    # "data" "width" "n_circuits" "dims"

    solutions_dict = {"all_solutions": [], "solution": {}, "stats": [], "model": "base", "data": data_dict["data"], "solver": "z3 SAT1"}
    # each solution in all_solutions is a dict
    solution = {"width": data_dict["width"], "n_circuits": data_dict["n_circuits"], "widths": [], "heights": [], "x": [], "y": [], "min_makespan": int, "max_makespan": int, "makespan": int}
    solutions_dict["all_solutions"].append(solution)
    



    #

    solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    return solutions_dict
