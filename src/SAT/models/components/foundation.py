from typing import List, Union

import uuid

from itertools import combinations
import uuid

from z3 import Bool, BoolRef
from z3 import Or, And, Not, Xor, Implies

###

T_NumberAsBoolList = List[Bool]
T_Number = Union[T_NumberAsBoolList, int]
T_NumbersAsBoolLists = List[T_Number]
# T_BoolOrList = Union[T_NumberAsBoolList, Bool]
T_Z3Clause = BoolRef

###


def __is_bool(val: Union[bool, BoolRef]) -> bool:
    return isinstance(val, bool) or isinstance(val, BoolRef)


def pad(l: T_NumberAsBoolList, length: int) -> T_NumberAsBoolList:
    assert length > 0 and length >= len(l), '\nl:\t{}\nlength:\t{}'.format(l, length)

    return [False for _ in range(length - len(l))] + l


def bool2int(l: T_NumberAsBoolList) -> int:
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


def int2boolList(n: int) -> List[bool]:
    result = []
    base2 = format(n, "b")
    for bit in base2:
        if bit == "1":
            result.append(True)
        else:
            result.append(False)
    return result


###


def all_F(l: T_NumberAsBoolList) -> T_Z3Clause:
    return And([Not(b) for b in l])


def at_least_one_T(bools: List[Bool]) -> T_Z3Clause:
    return Or(bools)


def at_most_one_T(bools: List[Bool]) -> T_Z3Clause:
    return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])


def exactly_one_T(bools: List[Bool]) -> T_Z3Clause:
    return And(at_most_one_T(bools) + [at_least_one_T(bools)])


def ne(l1, l2) -> T_Z3Clause:
    l1, l2 = get_bool_lists(l1, l2)

    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = at_least_one_T(l2[:start_idx[1]])
    return Or([c1, c2] + [Xor(l1i, l2i) for l1i, l2i in zip(l1, l2)])


"""
def eq(bol1: T_BoolOrList, bol2: T_BoolOrList) -> T_Z3Clause:

    def __eq(b1: Bool, b2: Bool) -> T_Z3Clause:
        return Not(Xor(b1, b2))

    assert isinstance(bol1, list) or __is_bool(bol1)
    assert isinstance(bol2, list) or __is_bool(bol2)

    if __is_bool(bol1) and __is_bool(bol2):
        return __eq(bol1, bol2)

    if isinstance(bol1, list) and isinstance(bol2, list):
        if len(bol1) == len(bol2):
            return And([__eq(b1, b2) for b1, b2 in zip(bol1, bol2)])

        if len(bol1) > len(bol2):
            return And(
                [__eq(b1, b2) for b1, b2 in zip(bol1[len(bol2):], bol2)] + all_F(bol1[:len(bol2)])
            )

        ### len(bol1) < len(bol2)
        return And(
            [__eq(b1, b2) for b2, b1 in zip(bol2[len(bol1):], bol1)] + all_F(bol2[:len(bol1)])
        )

    raise Exception("[eq] invalid parameters types.")
    """


def get_bool_lists(*ll):
    ll = list(ll)
    for i in range(len(ll)):
        if isinstance(ll[i], int):
            ll[i] = int2boolList(ll[i])
        #elif isinstance(ll[i], list) and isinstance(ll[i][0], int):
        #    ll[i] = [int2boolList(x) for x in ll[i]]
        elif not isinstance(ll[i], list):
            assert __is_bool(ll[i])
            ll[i] = [ll[i]]
    return ll


def eq(l1: T_Number, l2: T_Number) -> T_Z3Clause:
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)

    return And([Not(Xor(l1[i], l2[i])) for i in range(max_len)])


"""
def gte(l1,l2):
    return Or(gt(l1,l2), eq(l1,l2))
"""
"""
def __gte_same_len_n2(l1: T_NumberAsBoolList, l2: T_NumberAsBoolList) -> BoolRef:
    assert (len(l1) == len(l2))
    ### AND encoding: complexity n^2 -> not very good, will be done better
    n = len(l1)
    first = Or(l1[0], Not(l2[0]))  ### l1[0] >= l2[0]
    rest = And(
        [
            Implies(
                And([Not(Xor(l1[j], l2[j]))
                     for j in range(i + 1)]),  ### if l1[j] == l2[j] for every j up to i
                Or((l1[i + 1], Not(l2[i + 1])))  ### then l1[i+1] >= l2[i+1]
            ) for i in range(n - 1)
        ]
    )
    return And(first, rest)
"""


def __gte_same_len(l1: T_NumberAsBoolList, l2: T_NumberAsBoolList) -> T_Z3Clause:
    ### AND-CSE Encoding: Common SubExpression Elimination
    if len(l1) == 1:
        return Or(l1[0], Not(l2[0]))

    x = [Bool(f"xge_{str(uuid.uuid4())}") for i in range(len(l1) - 1)]

    first = Or(l1[0], Not(l2[0]))
    second = (x[0] == Not(Xor(l1[0], l2[0])))
    third = []
    for i in range(len(l1) - 2):
        third.append(x[i + 1] == (And(x[i], Not(Xor(l1[i + 1], l2[i + 1])))))
    fourth = []
    for i in range(len(l1) - 1):
        fourth.append(Implies(x[i], Or(l1[i + 1], Not(l2[i + 1]))))

    return And(first, second, And(third), And(fourth))


def gte(l1: T_Number, l2: T_Number) -> T_Z3Clause:

    l1, l2 = get_bool_lists(l1, l2)

    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gte_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))


def __gt_same_len(l1: T_NumberAsBoolList, l2: T_NumberAsBoolList) -> T_Z3Clause:
    ### AND-CSE Encoding: Common SubExpression Elimination
    if len(l1) == 1:
        return And(l1[0], Not(l2[0]))

    x = [Bool(f"x_{i}") for i in range(len(l1) - 1)]

    first = And(l1[0], Not(l2[0]))
    second = (x[0] == Not(Xor(l1[0], l2[0])))
    third = []
    for i in range(len(l1) - 2):
        third.append(x[i + 1] == (And(x[i], Not(Xor(l1[i + 1], l2[i + 1])))))
    fourth = []
    for i in range(len(l1) - 1):
        fourth.append(And(x[i], And(l1[i + 1], Not(l2[i + 1]))))

    return Or(first, And(second, And(third), Or(fourth)))


"""
def __gt_same_len(l1: T_NumberAsBoolList, l2: T_NumberAsBoolList) -> T_Z3Clause:
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
"""


def gt(l1: T_Number, l2: T_Number) -> T_Z3Clause:

    l1, l2 = get_bool_lists(l1, l2)

    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gt_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))


"""
def gt(l1: T_NumberAsBoolList, l2: T_NumberAsBoolList) -> BoolRef:
    #l1 > l2

    #l1 = 10101010101
    #l2 =      010101
    if len(l1) > len(l2):
        diff = len(l1) - len(l2)
        l1_same_len = l1[diff:]
        l1_exceeding = l1[:diff]
        #if there are Trues in the diff then for sure l1>l2
        result = Implies(Not(at_least_one_T(l1_exceeding)), __gt_same_len(l1_same_len, l2))

    elif len(l1) == len(l2):
        result = __gt_same_len(l1, l2)
    else:
        #l1 =      010101
        #l2 = 10101010101
        diff = len(l2) - len(l1)
        l2_same_len = l2[diff:]
        l2_exceeding = l2[:diff]
        first = all_F(l2_exceeding)
        rest = __gt_same_len(l1, l2_same_len)
        result = And(first, rest)
    return result
"""


def lte(l1: T_Number, l2: T_Number) -> T_Z3Clause:
    return gte(l1=l2, l2=l1)


def lt(l1: T_Number, l2: T_Number) -> T_Z3Clause:
    return gt(l1=l2, l2=l1)


"""
def lte_int(l: T_NumberAsBoolList, n: int) -> BoolRef:
    ### provide constraint list so that bool2int(l) < n

    base2 = format(n, "b")

    if len(base2) > len(l):
        return True

    if len(base2) < len(l):
        base2 = ("0" * (len(l) - len(base2))) + base2

    assert (len(base2) == len(l))

    list_of_1 = [i for i in range(len(base2)) if base2[i] == "1"]
    list_of_1.append(len(l))

    ### all the bools of l before the first 1 in n must be 0
    constraint_list = []
    constraint_list.append(all_F(l[:list_of_1[0]]))

    ### (each bit in l at the indexes contained in list_of_1 and all the previous) ->
    ### all the bit after that in l are 0 before the next index of list_of_1
    ### for i in range(len(list_of_1)):
    for i, index_of_1 in enumerate(list_of_1):
        next_index_of_1 = list_of_1[min(len(list_of_1) - 1, i + 1)]

        constraint_list = constraint_list + [
            Implies(And([l[list_of_1[k]] for k in range(i + 1)]), Not(l[j]))
            for j in range(min(index_of_1 + 1, len(l)), next_index_of_1)
        ]

    return And(constraint_list)
"""
"""
def lte_int(l: T_NumberAsBoolList, n: int) -> BoolRef:
    return Or(lte_int(l, n), eq(l, n))
    #rifare a partire da lt_int
"""


###  check argument type
def sum_b(l1: T_Number, l2: T_Number) -> T_Z3Clause:
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)
    result = []

    carry_in = False
    carry_out = False

    for i in range(max_len - 1, -1, -1):
        a = l1[i]
        b = l2[i]
        result.append(Xor(Xor(a, b), carry_in))

        carry_out = Or(And(Xor(a, b), carry_in), And(a, b))
        carry_in = carry_out

    result = result[::-1]

    return result


def sub_b(l1: T_Number, l2: T_Number) -> T_Z3Clause:
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)
    result = []

    borr_in = False
    borr_out = False

    for i in range(len(l1) - 1, -1, -1):
        a = l1[i]
        b = l2[i]
        result.append(Xor(Xor(a, b), borr_in))

        borr_out = Or(And(Not(Xor(a, b)), borr_in), And(Not(a), b))
        borr_in = borr_out

    result = result[::-1]
    return result


def diffn(
    x: 'list[list[Bool]]', y: 'list[list[Bool]]', widths: T_Number, heigths: T_Number
) -> T_Z3Clause:
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
        ### if i < j: useless
        l.append(
            Or(
                lte(sum_b(x[i], widths[i]), x[j]), lte(sum_b(y[i], heigths[i]), y[j]),
                lte(sum_b(x[j], widths[j]), x[i]), lte(sum_b(y[j], heigths[j]), y[i])
            )
        )
    return And(l)


def _disjunctive(x: T_NumbersAsBoolLists, dx: T_NumbersAsBoolLists):
    CIRCUITS = range(len(x))
    result = []
    for c1, c2 in combinations(CIRCUITS, 2):
        result.append(Or(lte(sum_b(x[c1], dx[c1]), x[c2]), lte(sum_b(x[c2], dx[c2]), x[c1])))
    return And(result)


def _fzn_cumulative(
    x: T_NumbersAsBoolLists, dx: T_NumbersAsBoolLists, r: T_NumbersAsBoolLists, boundary: int
):
    result = []
    # x, dx, r = get_bool_lists(x, dx, r)

    CIRCUITS = range(len(x))
    for xi in range(boundary):
        ###  initialize sum at 0
        sum_at_xi = [False]  # == int2boolList(0)
        for c in CIRCUITS:
            _x, _dx, _r = get_bool_lists(x[c], dx[c], r[c])
            ###  if condition then res_at_xi=_r else 0
            res_at_xi = []
            ###  check if circuit==c is at x==xi
            condition = And(lte(_x, xi), lt(xi, sum_b(_x, _dx)))

            ###  null the resource of circuit==c if condition not satisfied
            for i in range(len(_r)):
                res_at_xi.append(And(_r[i], condition))

            ###  update the sum
            sum_at_xi = sum_b(sum_at_xi, res_at_xi)

        ###  the sum of resources for all circuits at x==xi must not pass the boundary
        result.append(lte(sum_at_xi, boundary))

    return And(result)


def cumulative(
    x: T_NumbersAsBoolLists, dx: T_NumbersAsBoolLists, r: T_NumbersAsBoolLists, boundary: int,
    min_r: int, idx_min_r: int
) -> T_Z3Clause:

    assert len(x) == len(dx) == len(
        r
    ), 'cumulative: the 3 array arguments must have identical length'
    CIRCUITS = range(len(x))

    ###  check if disjunctive can be used
    disj_cond = []
    for c in CIRCUITS:
        disj_cond.append(Or(gt(sum_b(r[c], min_r), boundary), c == idx_min_r))
    result = [
        ###  disjunctive case
        Implies(And(disj_cond), _disjunctive(x, dx)),
        ###  fzn_cumulative case
        Implies(Not(And(disj_cond)), _fzn_cumulative(x, dx, r, boundary))
    ]
    return And(result)


###


def symmetrical(x: T_NumbersAsBoolLists, dx: T_Number, start: int, end: int) -> T_Z3Clause:
    assert start >= 0 and end > start

    ###  x' = end - (x[i]-start+dx[i])
    x_symm = [sub_b(end, sum_b(sub_b(x[i], start), dx[i])) for i in range(len(x))]
    return x_symm


def axial_symmetry(x: T_NumbersAsBoolLists, dx: T_Number, start: int, end: int) -> T_Z3Clause:
    x_symm = symmetrical(x, dx, start, end)
    max_len = max(max([len(xi) for xi in x]), max([len(xi) for xi in x_symm]))
    x_flat = []
    x_symm_flat = []
    ###  maybe padding is useless
    for i in range(len(x)):
        x_flat += pad(x[i], max_len)
        x_symm_flat += pad(x_symm[i], max_len)
    return lte(x_flat, x_symm_flat)
