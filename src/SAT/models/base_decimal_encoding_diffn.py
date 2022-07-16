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


def all_zeros(l: 'list[Bool]'):
    return And([Not(l[i]) for i in range(len(l))])


def bool2int(l: 'list[Bool]'):
    result = 0
    l_b = []
    for _, l_i in enumerate(l):
        if str(l_i) == "True":
            l_b.append(True)
        else:
            l_b.append(False)

    for digits in l_b:
        result = (result << 1) | bool(int(digits))
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
    #l1 >= l2

    #l1 = 10101010101
    #l2 =      010101
    if len(l1) > len(l2):
        diff = len(l1) - len(l2)
        l1_same_len = l1[diff:]
        l1_exceeding = l1[:diff]
        #if there are Trues in the diff then for sure l1>l2
        return Implies(Not(at_least_one(l1_exceeding)), ge_same_len(l1_same_len, l2))

    if len(l1) == len(l2):
        return ge_same_len(l1, l2)

    #l1 =      010101
    #l2 = 10101010101
    diff = len(l2) - len(l1)
    l2_same_len = l2[diff:]
    l2_exceeding = l2[:diff]
    first = all_zeros(l2_exceeding)  #there must not be any Trues in the exceeding part
    rest = ge_same_len(l1, l2_same_len)
    return And(first, rest)


def ge_same_len(l1: 'list[Bool]', l2: 'list[Bool]'):
    assert (len(l1) == len(l2))
    #AND encoding: complexity n^2 -> not very good, will be done better
    n = len(l1)
    first = Or(l1[0], Not(l2[0]))  #l1[0] >= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  # if l1[j] == l2[j] for every j up to i
                Or((l1[i + 1], Not(l2[i + 1])))  # then l1[i+1] >= l2[i+1]
            ) for i in range(n - 1)
        ]
    )
    return And(first, rest)


def gt(l1: 'list[Bool]', l2: 'list[Bool]'):
    #l1 > l2

    #l1 = 10101010101
    #l2 =      010101
    if len(l1) > len(l2):
        diff = len(l1) - len(l2)
        l1_same_len = l1[diff:]
        l1_exceeding = l1[:diff]
        #if there are Trues in the diff then for sure l1>l2
        return Implies(Not(at_least_one(l1_exceeding)), gt_same_len(l1_same_len, l2))

    if len(l1) == len(l2):
        return gt_same_len(l1, l2)

    #l1 =      010101
    #l2 = 10101010101
    diff = len(l2) - len(l1)
    l2_same_len = l2[diff:]
    l2_exceeding = l2[:diff]
    first = all_zeros(l2_exceeding)
    rest = gt_same_len(l1, l2_same_len)
    return And(first, rest)


def gt_same_len(l1: 'list[Bool]', l2: 'list[Bool]'):
    assert (len(l1) == len(l2))
    #AND encoding: complexity n^2 -> not very good, will be done better
    n = len(l1)
    first = Or(l1[0], Not(l2[0]))  #l1[0] >= l2[0]
    rest = And(
        [
            Implies(
                And(
                    [
                        Not(Xor(l1[j], l2[j]))  # if l1[j] == l2[j] for every j up to i
                        for j in range(i + 1)
                    ]
                ),
                And(l1[i + 1], Not(l2[i + 1]))  # then l1[i+1] > l2[i+1]
            ) for i in range(n - 1)
        ]
    )
    return And(first, rest)


#NOTE: https://digitalcommons.iwu.edu/cgi/viewcontent.cgi?article=1022&context=cs_honproj
#contains a more efficient encoding for lex

# def le(l1: 'list[Bool]', l2: 'list[Bool]'):
#     #lex_lesseq(list1, list2)
#     #AND encoding: complexity n^2 -> not very good
#     n = len(l1)
#     first = Or(Not(l1[0]), l2[0])  #l1[0] <= l2[0]
#     rest = And(
#         [
#             Implies(
#                 And([Not(Xor(l1[j], l2[j]))
#                      for j in range(i + 1)]),  # AND(l1[j] == l2[j]) for j in range(i+1)
#                 Or((Not(l1[i + 1]), l2[i + 1]))  #l1[i+1] <= l2[i+1]
#             ) for i in range(n - 1)
#         ]
#     )

#     return And(first, rest)#


def le(l1: 'list[Bool]', l2: 'list[Bool]'):
    return ge(l1=l2, l2=l1)


def lt(l1: 'list[Bool]', l2: 'list[Bool]'):
    return gt(l1=l2, l2=l1)


def ne(l1: 'list[Bool]', l2: 'list[Bool]'):  # does not change from decimal to one hot encoding
    assert (len(l1) == len(l2))
    return Or([Xor(l1[bit], l2[bit]) for bit in range(len(l2))])


def eq(l1: 'list[Bool]', l2: 'list[Bool]'):  # does not change from decimal to one hot encoding
    assert (len(l1) == len(l2))
    return And([Not(Xor(l1[i], l2[i])) for i in range(len(l1))])


def lt_int(l: 'list[Bool]', n: int):
    #provide constraint list so that bool2int(l) < n

    base2 = format(n, "b")

    if len(base2) > len(l):
        return []

    if len(base2) < len(l):
        base2 = ("0" * (len(l) - len(base2))) + base2

    assert (len(base2) == len(l))

    list_of_1 = [i for i in range(len(base2)) if base2[i] == "1"]
    list_of_1.append(len(l))

    #all the bools of l before the first 1 in n must be 0
    constraint_list = [Not(l[i]) for i in range(list_of_1[0])]

    #(each bit in l at the indexes contained in list_of_1 and all the previous) ->
    # all the bit after that in l are 0 before the next index of list_of_1
    #for i in range(len(list_of_1)):
    for i, list_of_1_i in enumerate(list_of_1):
        index_of_1 = list_of_1_i
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


# def lt_eq_int(l: 'list[Bool]', n: int):
#     return Or(lt_int(l, n), eq_int(l, n))
#     #rifare a partire da lt_int


def lt_eq(l1: 'list[Bool]', l2: 'list[Bool]'):
    return Or(lt(l1, l2), eq(l1, l2))  #TODO rifare a partire da lt


def eq_int(l: 'list[Bool]', n: int):
    #a == b
    base2 = format(n, "b")

    for i in range(len(l) - len(base2)):
        base2 = "0" + base2

    assert (len(base2) == len(l))
    constraint_list = []

    #for i in range(len(base2)):
    for i, base2_i in enumerate(base2):
        if base2_i == '0':
            constraint_list.append(Not(l[i]))
        else:
            constraint_list.append(l[i])

    return And(constraint_list)


def sum_int(l: 'list[Bool]', n: int):
    base2 = base2 = format(n, "b")

    base2 = '0' * (len(l) - len(base2)) + base2
    result = []

    carry_in = False
    carry_out = False

    for i in range(len(base2) - 1, -1, -1):
        a = l[i]
        b = bool(int(base2[i]))
        result.append(Xor(Xor(a, b), carry_in))

        carry_out = Or(And(Xor(a, b), carry_in), And(a, b))
        carry_in = carry_out

    result = result[::-1]
    return result


def diffn(x: 'list[Bool]', y: 'list[Bool]', widths: 'list[int]', heigths: 'list[int]'):
    # predicate fzn_diffn(array[int] of var int: x,
    #                 array[int] of var int: y,
    #                 array[int] of var int: dx,
    #                 array[int] of var int: dy) =
    #     forall(i,j in index_set(x) where i < j)(
    #         x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/
    #         x[j] + dx[j] <= x[i] \/ y[j] + dy[j] <= y[i]
    #     );

    l = []
    for i, j in combinations(range(len(x)), 2):
        #if i < j: useless
        l.append(
            Or(
                lt_eq(sum_int(x[i], widths[i]), x[j]), lt_eq(sum_int(y[i], heigths[i]), y[j]),
                lt_eq(sum_int(x[j], widths[j]), x[i]), lt_eq(sum_int(y[j], heigths[j]), y[i])
            )
        )
    return And(l)


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

    max_domain_x = width - min(widths) + max(widths)
    # + max(widths) is necessary for summing the width later
    if max_domain_x > 0:
        domain_size_x = math.ceil(math.log2(max_domain_x))
    else:
        domain_size_x = 1

    domain_size_y = max_makespan - min(heigths) + max(heigths)
    # + max(heigths) is necessary for summing the height later
    if domain_size_y > 0:
        domain_size_y = math.ceil(math.log2(domain_size_y))
    else:
        domain_size_y = 1
    x = [[Bool(f"x_of_c{c}_{i}") for i in range(domain_size_x)] for c in CIRCUITS]
    y = [[Bool(f"y_of_c{c}_{i}") for i in range(domain_size_y)] for c in CIRCUITS]

    ### diffn
    solver.add(diffn(x, y, widths, heigths))

    #makespan is not known yet

    ### all circuits must have each dimension greater than zero
    assert (min(heigths) > 0 and min(widths) > 0)
    assert (len(heigths) == len(widths) == n_circuits)

    #forall(c in CIRCUITS)(x[c] + widths[c] <= width)
    solver.add(And([lt_int(x[c], width - widths[c]) for c in CIRCUITS]))

    solutions_dict = {
        "all_solutions": [],
        "solution": {},
        "stats": [],
        "model": "base",
        "data": data_dict["data"],
        "solver": "z3 SAT"
    }
    # each solution in all_solutions is a dict

    print(f"max_makespan = {max_makespan}")
    print(f"min_maekspan = {min_makespan}")

    check = sat
    while check == sat and max_makespan >= min_makespan:

        solver.push()
        #forall(c in CIRCUITS)(y[c] + heights[c] <= max_makespan)
        solver.add(And([lt_int(y[c], max_makespan - heigths[c]) for c in CIRCUITS]))

        solution = {}
        check = solver.check()
        makespan = 0
        if check == sat:
            model = solver.model()
            y_int = [
                bool2int([model.evaluate(y[c][i]) for i in range(domain_size_y)]) for c in CIRCUITS
            ]

            makespan = max([y_int[c] + heigths[c] for c in CIRCUITS])
            print(f"max_makespan = :{max_makespan}  sat at makespan = :{makespan}")
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
            solutions_dict["stats"] = solver.statistics()
            solver.pop()
        else:
            print("unsat")
        max_makespan = makespan - 1
        #it is possible to decrease max_makespan at pace > 1 and when unsat try the skipped values
        #or implement binary search...
    #while check == sat

    if solutions_dict["all_solutions"]:
        solutions_dict["solution"] = solutions_dict["all_solutions"][
            len(solutions_dict["all_solutions"]) - 1]
    return solutions_dict
