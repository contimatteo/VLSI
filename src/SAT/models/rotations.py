import math
from socket import timeout
import time
#import timeout_decorator
from operator import indexOf
from z3 import And, Solver, Bool, sat, unsat, Implies, Not, Xor, Or

from SAT.models.components.helper import compute_max_makespan
from SAT.models.components.foundation import bool2int, diffn, lte, all_F, axial_symmetry, pad, sub_b, int2boolList
#hello
### NOTE: https://digitalcommons.iwu.edu/cgi/viewcontent.cgi?article=1022&context=cs_honproj
### contains a more efficient encoding for lex


def solve(data_dict: dict) -> dict:
    ### data_dict = {"data":str, "width": int, "n_circuits": int, "dims":[(w,h)]}

    t0 = time.time()

    n_circuits = data_dict["n_circuits"]
    width = data_dict["width"]
    CIRCUITS = range(n_circuits)

    ###  array of horizontal dimensions of the circuits
    widths = [data_dict["dims"][c][0] for c in CIRCUITS]
    ###  array of vertical dimensions of the circuits
    heights = [data_dict["dims"][c][1] for c in CIRCUITS]

    ### define makespan boundaries
    sum_area = sum([heights[c] * widths[c] for c in CIRCUITS])
    min_makespan = max(math.ceil(sum_area / width), max(heights))
    # max_makespan = sum(heights)
    # max_makespan = heuristics.compute_max_makespan(heights, widths, width);
    max_makespan = compute_max_makespan(heights, widths, width)

    solver = Solver()

    max_domain_x = width - min(widths + heights) + max(widths + heights)
    ### + max(widths) is necessary for summing the width later
    if max_domain_x > 0:
        domain_size_x = math.ceil(math.log2(max_domain_x))
    else:
        domain_size_x = 1

    domain_size_y = max_makespan - min(heights + widths) + max(heights + widths)
    ### + max(heights) is necessary for summing the height later
    if domain_size_y > 0:
        domain_size_y = math.ceil(math.log2(domain_size_y))
    else:
        domain_size_y = 1
    x = [[Bool(f"x_of_c{c}_{i}") for i in range(domain_size_x)] for c in CIRCUITS]
    y = [[Bool(f"y_of_c{c}_{i}") for i in range(domain_size_y)] for c in CIRCUITS]

    max_dim = max(widths + heights)
    domain_size_dims = math.ceil(math.log2(max_dim))
    widths_bool = [[Bool(f"w_of_c{c}_{i}") for i in range(domain_size_dims)] for c in CIRCUITS]
    heights_bool = [[Bool(f"h_of_c{c}_{i}") for i in range(domain_size_dims)] for c in CIRCUITS]

    rotation = False

    ### NO rotation constraints
    ### if there are no rotation then the bool_list of widths and heights must be == to the int lists
    solver.add(
        And(
            [
                And(
                    [
                        Implies(
                            Not(rotation),
                            Not(
                                Xor(
                                    widths_bool[c][i],
                                    pad(int2boolList(widths[c]), domain_size_dims)[i]
                                )
                            )
                        ) for i in range(domain_size_dims)
                    ] for c in CIRCUITS
                )
            ]
        )
    )
    solver.add(
        And(
            [
                And(
                    [
                        Implies(
                            Not(rotation),
                            Not(
                                Xor(
                                    heights_bool[c][i],
                                    pad(int2boolList(heights[c]), domain_size_dims)[i]
                                )
                            )
                        ) for i in range(domain_size_dims)
                    ] for c in CIRCUITS
                )
            ]
        )
    )

    ### rotation constraints
    solver.add(
        And(
            [
                And(
                    [
                        Implies(
                            rotation,
                            Or(
                                Not(Xor(widths_bool[c][i], int2boolList(widths[c][i]))),
                                Not(Xor(widths_bool[c][i], int2boolList(heights[c][i])))
                            )
                        ) for i in range(domain_size_dims)
                    ] for c in CIRCUITS
                )
            ]
        )
    )
    solver.add(
        And(
            [
                And(
                    [
                        Implies(
                            rotation,
                            Or(
                                Not(Xor(heights_bool[c][i], int2boolList(widths[c][i]))),
                                Not(Xor(heights_bool[c][i], int2boolList(heights[c][i])))
                            )
                        ) for i in range(domain_size_dims)
                    ] for c in CIRCUITS
                )
            ]
        )
    )

    ### diffn
    solver.add(diffn(x, y, widths_bool, heights_bool))

    ### makespan is not known yet

    ### all circuits must have each dimension greater than zero
    assert min(heights) > 0 and min(widths) > 0
    assert len(heights) == len(widths) == n_circuits

    ### forall(c in CIRCUITS)(x[c] + widths[c] <= width)
    solver.add(And([lte(x[c], sub_b(width, widths_bool[c])) for c in CIRCUITS]))

    solutions_dict = { ### each solution in all_solutions is a dict

        "all_solutions": [],
        "solution": {},
        "stats": [],
        "model": "base",
        "data": data_dict["data"],
        "solver": "z3 SAT"
    }

    ### simmetry braking constraint: biggest circuit in 0,0
    # area_list = [widths[c] * heights[c][1] for c in CIRCUITS]
    # max_area = indexOf(area_list, max(area_list))
    # solver.add(all_F(y[max_area]))
    # solver.add(all_F(x[max_area]))

    # solver.add(axial_symmetry(x, widths_bool, start=0, end=width))

    target_makespan = min_makespan  ### use target_makespan to iterate during optimization

    check = unsat
    while check == unsat and min_makespan <= target_makespan <= max_makespan and time.time(
    ) - t0 < 300:
        t1 = time.time()
        # set_option(timeout=1000)
        solver.push()
        ### forall(c in CIRCUITS)(y[c] + heights[c] <= target_makespan)
        solver.add(And([lte(y[c], sub_b(target_makespan, heights_bool[c])) for c in CIRCUITS]))

        # solver.add(axial_symmetry(y, heights, start=0, end=target_makespan))

        solution = {}
        check = solver.check()
        makespan = 0
        if check == sat:
            model = solver.model()
            y_int = [
                bool2int([model.evaluate(y[c][i]) for i in range(domain_size_y)]) for c in CIRCUITS
            ]
            heights_int = [
                bool2int([model.evaluate(heights_bool[c][i]) for i in range(domain_size_dims)])
                for c in CIRCUITS
            ]

            makespan = max([y_int[c] + heights_int[c] for c in CIRCUITS])
            print("sat")
            solution = {
                "width":
                data_dict["width"],
                "n_circuits":
                data_dict["n_circuits"],
                "widths":
                widths_bool,
                "heights":
                heights_int,
                "x": [
                    bool2int([model.evaluate(x[c][i]) for i in range(domain_size_x)])
                    for c in CIRCUITS
                ],
                "y":
                y_int,
                "min_makespan":
                min_makespan,
                "max_makespan":
                max_makespan,
                "makespan":
                makespan
            }
            solutions_dict["all_solutions"].append(solution)
            print(
                f"target_makespan = {target_makespan}  min_makespan = {min_makespan}  makespan = {makespan}"
            )
            solutions_dict["stats"] = solver.statistics()
            solver.pop()
        else:
            print("unsat")
            target_makespan += 1
        print(round(time.time() - t1))
        ### it is possible to decrease max_makespan at pace > 1 and when unsat try the skipped values
        ### or implement binary search...
    ### while

    print(f"TOTAL TIME = {round(time.time() - t0, 2)}")

    solutions_dict["all_solutions"] = solutions_dict["all_solutions"][::-1]
    if solutions_dict["all_solutions"]:
        solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    return solutions_dict
