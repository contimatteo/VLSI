import math
from itertools import combinations
from z3 import And, Or, Not, Xor, Solver, Bool, sat, Implies
from SAT.models.components import heuristics


def at_least_one(bool_vars: 'list[Bool]'):
    return Or(bool_vars)


def at_most_one(bool_vars: 'list[Bool]'):
    return [Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]


def exactly_one(bool_vars: 'list[Bool]'):
    return at_most_one(bool_vars) + [at_least_one(bool_vars)]


def bool2int(l: 'list[Bool]'):
    for i in range(len(l)):
        print(type(l[i]), end="")
        print("  ", end="")
        print(l[i])

    result = 0
    l_b = []
    for i in range(len(l)):
        if str(l[i]) == "True":
            l_b.append(True)
        else:
            #assert(str(l[i] == "True" or str(l[i]) == "False"))
            l_b.append(False)

    for digits in l_b:
        result = (result << 1) | bool(digits)  #TODO: wtf?
    return result


def int2boolList(n: int):
    result = []
    base2 = format(n, "b")
    for bit in base2:
        if bit == "1":
            result.append(True)
        else:
            result.append(False)
    return result


def ge(l1: 'list[Bool]', l2: 'list[Bool]'):
    #AND encoding: complexity n^2 -> not very good
    n = len(l1)
    first = Or(l1[0], Not(l2[0]))  #l1[0] >= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  # AND(l1[j] == l2[j]) for j in range(i+1)
                Or((l1[i + 1], Not(l2[i + 1])))  #l1[i+1] >= l2[i+1]
            ) for i in range(n - 1)
        ]
    )

    return And(first, rest)


#NOTE: https://digitalcommons.iwu.edu/cgi/viewcontent.cgi?article=1022&context=cs_honproj
#contains a more efficient encoding for lex


def le(l1: 'list[Bool]', l2: 'list[Bool]'):
    #lex_lesseq(list1, list2)
    #AND encoding: complexity n^2 -> not very good
    n = len(l1)
    first = Or(Not(l1[0]), l2[0])  #l1[0] <= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  # AND(l1[j] == l2[j]) for j in range(i+1)
                Or((Not(l1[i + 1]), l2[i + 1]))  #l1[i+1] <= l2[i+1]
            ) for i in range(n - 1)
        ]
    )

    return And(first, rest)


def lt(l1: 'list[Bool]', l2: 'list[Bool]'):
    #return And(le(l1, l2), Not(eq(l1, l2))) #inefficient
    #AND encoding: complexity n^2 -> not very good
    n = len(l1)
    first = Or(Not(l1[0]), l2[0])  #l1[0] <= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  # AND(l1[j] == l2[j]) for j in range(i+1)
                And((Not(l1[i + 1]), l2[i + 1]))  #l1[i+1] < l2[i+1]
            ) for i in range(n - 1)
        ]
    )

    return And(first, rest)


def gt(l1: 'list[Bool]', l2: 'list[Bool]'):
    #return And(ge(l1, l2), Not(eq(l1, l2))) #inefficient
    #AND encoding: complexity n^2 -> not very good
    n = len(l1)
    first = Or(l1[0], Not(l2[0]))  #l1[0] >= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  # AND(l1[j] == l2[j]) for j in range(i+1)
                And((l1[i + 1], Not(l2[i + 1])))  #l1[i+1] > l2[i+1]
            ) for i in range(n - 1)
        ]
    )

    return And(first, rest)


def ne(l1: 'list[Bool]', l2: 'list[Bool]'):  # does not change from decimal to one hot encoding
    assert (len(l1) == len(l2))
    return Or([Xor(l1[bit], l2[bit]) for bit in range(len(l2))])


def eq(l1: 'list[Bool]', l2: 'list[Bool]'):  # does not change from decimal to one hot encoding
    assert (len(l1) == len(l2))
    return And([Not(Xor(l1[i], l2[i])) for i in range(len(l1))])


def lt_int(l: 'list[Bool]', n: int):
    #provide constraint list so that bool2int(l) < n
    base2 = format(n, "b")
    if len(l) < len(base2):
        return []

    for i in range(len(l) - len(base2)):
        base2 = "0" + base2
    assert (len(base2) == len(l))

    list_of_1 = [i for i in range(len(base2)) if base2[i] == "1"]
    list_of_1.append(len(l))

    #all the bools of l before the first 1 in n must be 0
    constraint_list = [Not(l[i]) for i in range(list_of_1[0])]

    #(each bit in l at the indexes contained in list_of_1 and all the previous) -> all the bit after that in l are 0 before the next index of list_of_1

    for i in range(len(list_of_1)):
        index_of_1 = list_of_1[i]
        next_index_of_1 = list_of_1[min(len(list_of_1) - 1, i + 1)]

        constraint_list = constraint_list + \
        [ Implies(
            And([l[list_of_1[k]] for k in range(i+1)]),
            Not(l[j]))
            for j in range(min(index_of_1 + 1, len(l)), next_index_of_1)
        ]

    if constraint_list:
        result = And(constraint_list)
    else:
        result = []

    return result


def le_int(l: 'list[Bool]', n: int):
    pass  #TODO


def sub(l1: 'list[Bool]', l2: 'list[Bool]'):
    #a - b
    pass  #TODO


def sub_int(l: 'list[Bool]', n: int):
    pass  # TODO


def mul_int(l: 'list[Bool]', n: int):
    #a * b
    pass  #TODO


def eq_int(l: 'list[Bool]', n: int):
    #a == b
    base2 = format(n, "b")

    for i in range(len(l) - len(base2)):
        base2 = "0" + base2

    assert (len(base2) == len(l))
    constraint_list = []

    for i in range(len(base2)):
        if base2[i] == '0':
            constraint_list.append(Not(l[i]))
        else:
            constraint_list.append(l[i])

    return And(constraint_list)


def equation(
    point_of_grid: Bool, x_c: Bool, w: int, y_c: Bool, h: int, width: int
):  # does not change from decimal to one hot encoding
    # point_of_grid = (x_c + w) + (y_c + h) * width
    # point_of_grid - x_c - width*y_c = h*width + w
    eq_int(sub(sub_int(point_of_grid, x_c), mul_int(y_c, width)), h * width + w)


def baseSAT(data_dict: dict) -> dict:
    #data_dict = {"data":str, "width": int, "n_circuits": int, "dims":[(w,h)]}

    n_circuits = data_dict["n_circuits"]
    width = data_dict["width"]
    CIRCUITS = range(n_circuits)

    ###  array of horizontal dimensions of the circuits
    widths = [data_dict["dims"][c][0] for c in CIRCUITS]
    ###  array of vertical dimensions of the circuits
    heigths = [data_dict["dims"][c][1] for c in CIRCUITS]

    ### define makespan boundaries
    sum_area = sum([heigths[c] * widths[c] for c in CIRCUITS])
    min_makespan = max(math.ceil(sum_area / width), max(heigths))
    #max_makespan = sum(heights)
    # max_makespan = heuristics.compute_max_makespan(heigths, widths, width);
    max_makespan = heuristics.compute_max_makespan_tree(heigths, widths, width)

    solver = Solver()

    domain_size_x = math.ceil(math.log2(width - min(widths)))
    domain_size_y = math.ceil(math.log2(max_makespan - min(heigths)))
    x = [[Bool(f"x_of_c{c}_{i}") for i in range(domain_size_x)] for c in CIRCUITS]
    y = [[Bool(f"y_of_c{c}_{i}") for i in range(domain_size_y)] for c in CIRCUITS]

    ### grid (linearized)
    domain_size_grid = math.ceil(math.log2((width - min(widths)) * (max_makespan - min(heigths))))
    grid = [
        [Bool(f"point{p}_{coord}") for coord in range(domain_size_grid)] for p in range(sum_area)
    ]
    # Each point p of the sum_area (point p of a circuit) is assigned to the coord on the board

    #int values for x coordinate of circuit c
    # def x_c(c: int) -> int:
    #     point_of_sum_area = sum([heigths(i)*widths(i) for i in range(c)])
    #     bool_coord = grid(point_of_sum_area)
    #     point_of_grid = bool2int(bool_coord)
    #     return point_of_grid % width

    # #int values for y coordinates of circuit c
    # def y_c(c: int) -> int:
    #     point_of_sum_area = sum([heigths(i)*widths(i) for i in range(c)])
    #     bool_coord = grid(point_of_sum_area)
    #     point_of_grid = bool2int(bool_coord)
    #     return point_of_grid // width

    #constraint to bind grid values to x,y
    for c in CIRCUITS:
        for h in range(heigths[c]):
            for w in range(widths[c]):
                point_of_sum_area = sum([heigths(i) * widths(i)
                                         for i in range(c)]) + widths[c] * h + w
                solver.add(equation(grid[point_of_sum_area], x[c], w, y[c], h, width))
                #grid[point_of_sum_area] = (x[c]+w) + (y[c]+h)*width

    #makespan is not known yet

    ### all circuits must have each dimension greater than zero
    assert (min(heigths) > 0 and min(widths) > 0)
    assert (len(heigths) == len(widths) == n_circuits)

    #diffn: noOverlap => alldifferent(grid[])
    solver.add(
        And(
            [
                ne(grid[s1], grid[s2]) for s1 in range(len(grid)) for s2 in range(len(grid))
                if s1 < s2
            ]
        )
    )

    #forall(c in CIRCUITS)(x[c] + widths[c] <= width)
    solver.add(And([lt_int(x[c], width - widths[c]) for c in CIRCUITS]))

    check = sat
    while check == sat and max_makespan >= min_makespan:

        solver.push()
        #forall(c in CIRCUITS)(y[c] + heights[c] <= max_makespan)
        solver.add(And([lt_int(y[c], max_makespan - heigths[c]) for c in CIRCUITS]))

        solutions_dict = {
            "all_solutions": [],
            "solution": {},
            "stats": [],
            "model": "base",
            "data": data_dict["data"],
            "solver": "z3 SAT"
        }
        # each solution in all_solutions is a dict

        solution = {}
        check = solver.check()
        if check == sat:
            model = solver.model()
            y_int = [
                bool2int([model.evaluate(y[c][i]) for i in range(domain_size_y)]) for c in CIRCUITS
            ]

            makespan = max([y_int[c] + heigths[c] for c in CIRCUITS])
            print(f"max_makespan:{max_makespan}  sat:{makespan}")
            solution = {
                "width":
                data_dict["width"],
                "n_circuits":
                data_dict["n_circuits"],
                "widths":
                widths,
                "heights":
                heigths,
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
            print(solution)
            solver.pop()
        else:
            print("unsat")
        max_makespan = makespan - 1
        #it is possible to decrease max_makespan at pace > 1 and when unsat try the skipped values
    #while check == sat

    solutions_dict["stats"] = solver.statistics()
    solutions_dict["solution"] = solutions_dict["all_solutions"][0]
    return solutions_dict