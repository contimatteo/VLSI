from typing import List

import math
import time
import z3

from z3 import Bool, And, BoolRef, Solver

from SAT.models.components.helper import compute_max_makespan
from SAT.models.components.foundation import diffn, lte_int
from SAT.models.components.symmetry import sym_bigger_circuit_origin

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


def __solver() -> T_Z3Solver:
    solver = Solver()

    solver.set('sat.random_seed', 666)

    # if custom_search:
    #     s.set("sat.local_search", True)
    #     s.set("sat.local_search_threads", 1)
    #     s.set("sat.threads", 3)
    #     s.set("sat.lookahead_simplify", True)
    #     s.set("sat.lookahead.use_learned", True)

    return solver


def __variables_support(data: dict) -> dict:
    width = data["width"]
    n_circuits = data["n_circuits"]
    CIRCUITS = range(n_circuits)

    _dims = data["dims"]
    ###  array of horizontal dimensions of the circuits
    widths = [_dims[c][0] for c in CIRCUITS]
    ###  array of vertical dimensions of the circuits
    heigths = [_dims[c][1] for c in CIRCUITS]

    return width, n_circuits, CIRCUITS, widths, heigths


def variables(data: dict) -> dict:
    width, n_circuits, CIRCUITS, widths, heigths = __variables_support(data)

    #

    ### define makespan boundaries
    _c_area_sum = sum([heigths[c] * widths[c] for c in CIRCUITS])
    min_makespan = max(math.ceil(_c_area_sum / width), max(heigths))
    max_makespan = compute_max_makespan(heigths, widths, width)

    ### + max(widths) is necessary for summing the width later
    _x_domain_max = width - min(widths) + max(widths)
    _x_domain_size = math.ceil(math.log2(_x_domain_max)) if _x_domain_max > 0 else 1

    ### + max(heigths) is necessary for summing the height later
    _y_domain_max = max_makespan - min(heigths) + max(heigths)
    _y_domain_size = math.ceil(math.log2(_y_domain_max)) if _y_domain_max > 0 else 1

    x = [[Bool(f"x_of_c{c}_{i}") for i in range(_x_domain_size)] for c in CIRCUITS]
    y = [[Bool(f"y_of_c{c}_{i}") for i in range(_y_domain_size)] for c in CIRCUITS]

    #

    ### all circuits must have each dimension greater than zero
    assert min(heigths) > 0 and min(widths) > 0
    assert len(heigths) == len(widths) == n_circuits

    VARS_TO_RETURN = [
        "width", "n_circuits", "CIRCUITS", "widths", "heigths", "x", "y", "min_makespan",
        "max_makespan"
    ]

    _local_vars = locals()

    return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}


###


def constraints(var: dict) -> List[T_Z3Clause]:
    return [
        diffn(var["x"], var["y"], var["widths"], var["heigths"]),
        ### forall(c in CIRCUITS)(x[c] + widths[c] <= width)
        And([lte_int(var["x"][c], var["width"] - var["widths"][c]) for c in var["CIRCUITS"]])
    ]


def symmetries_breaking(var: dict) -> List[T_Z3Clause]:
    return [sym_bigger_circuit_origin(var["x"], var["y"], var["widths"], var["heigths"])]


###


def solve(data: dict) -> dict:
    t0 = time.time()

    solver = __solver()

    # solutions_dict = { ### each solution in all_solutions is a dict
    #     "all_solutions": [],
    #     "solution": {},
    #     "stats": [],
    #     "model": "base",
    #     "data": data["data"],
    #     "solver": "z3 SAT"
    # }

    #

    vars_dict = variables(data)

    width = vars_dict["width"]
    assert width is not None

    n_circuits, CIRCUITS = vars_dict["n_circuits"], vars_dict["CIRCUITS"]
    assert n_circuits is not None and CIRCUITS is not None

    widths, heigths = vars_dict["widths"], vars_dict["heigths"]
    assert len(widths) > 0 and len(heigths) > 0

    x, y = vars_dict["x"], vars_dict["y"]
    assert len(x) > 0 and len(y) > 0

    min_makespan, max_makespan = vars_dict["min_makespan"], vars_dict["max_makespan"]
    assert min_makespan is not None and max_makespan is not None

    #

    for clause in constraints(vars_dict):
        solver.add(clause)

    for clause in symmetries_breaking(vars_dict):
        solver.add(clause)

    #

    target_makespan = min_makespan  ### use target_makespan to iterate during optimization

    check = z3.unsat

    while check == z3.unsat and min_makespan <= target_makespan <= max_makespan and time.time(
    ) - t0 < 300:
        t1 = time.time()
        solver.push()
        ### forall(c in CIRCUITS)(y[c] + heights[c] <= target_makespan)
        solver.add(And([lte_int(y[c], target_makespan - heigths[c]) for c in CIRCUITS]))

        check = solver.check()

        # solution = {}
        # makespan = 0
        if check == z3.sat:
            print("SAT")
            print("makespan =", target_makespan)
            # model = solver.model()
            # y_int = [
            #     bool2int([model.evaluate(y[c][i]) for i in range(domain_size_y)]) for c in CIRCUITS
            # ]
            # makespan = max([y_int[c] + heigths[c] for c in CIRCUITS])
            # print("sat")
            # solution = {
            #     "width":
            #     data_dict["width"],
            #     "n_circuits":
            #     data_dict["n_circuits"],
            #     "widths":
            #     widths,
            #     "heights":
            #     heigths,
            #     "x": [
            #         bool2int([model.evaluate(x[c][i]) for i in range(domain_size_x)])
            #         for c in CIRCUITS
            #     ],
            #     "y":
            #     y_int,
            #     "min_makespan":
            #     min_makespan,
            #     "max_makespan":
            #     max_makespan,
            #     "makespan":
            #     makespan
            # }
            # solutions_dict["all_solutions"].append(solution)
            # print(
            #     f"target_makespan = {target_makespan}  min_makespan = {min_makespan}  makespan = {makespan}"
            # )
            # solutions_dict["stats"] = solver.statistics()
            solver.pop()
        else:
            print("unsat")
            target_makespan += 1
        print(round(time.time() - t1))
        ### it is possible to decrease max_makespan at pace > 1 and when unsat try the skipped values
        ### or implement binary search...

    print(f"TOTAL TIME = {round(time.time() - t0, 2)}")

    # solutions_dict["all_solutions"] = solutions_dict["all_solutions"][::-1]
    # if solutions_dict["all_solutions"]:
    #     solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    # return solutions_dict

    return {"leonardo": "ciaoooone"}
