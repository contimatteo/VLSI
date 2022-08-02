from typing import List, Union

from itertools import combinations
import uuid

###

###

M = int(1e10)


def diffn(x, y, widths, heigths, diffn_vars):
    # predicate fzn_diffn(array[int] of var int: x,
    #                 array[int] of var int: y,
    #                 array[int] of var int: dx,
    #                 array[int] of var int: dy) =
    #     forall(i,j in index_set(x) where i < j)(
    #         x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/
    #         x[j] + dx[j] <= x[i] \/ y[j] + dy[j] <= y[i]
    #     );

    CIRCUITS = range(len(x))
    result = []
    i = 0
    for c1, c2 in combinations(CIRCUITS, 2):
        result += [
            ###  if diffn_vars[i] == 1 -> c1 on the right of c2
            ###  -> if diffn_vars[i] == 1 make true the case x[c2] - x[c1] >= widths[c1]
            x[c2] - x[c1] >= widths[c1] - M * diffn_vars[i],
            ###  -> if diffn_vars[i] == 1 leave undefined the case x[c2] + widths[c2] <= x[c1]
            x[c1] - x[c2] >= widths[c2] - M * (1 - diffn_vars[i]),
            ###  if diffn_vars[i+1] == 1 -> c1 on top of c2
            ###  -> if diffn_vars[i] == 1 make true the case y[c1] + heights[c1] <= y[c2]
            y[c1] - y[c2] >= heigths[c2] - M * diffn_vars[i+1],
            ###  -> if diffn_vars[i+1] == 1 leave undefined the case y[c2] + heights[c2] <= y[c1]
            y[c1] - y[c2] >= heigths[c2] - M * (1 - diffn_vars[i+1])
        ]
        i += 2
    
    print('diffn result:', result)

    return result

"""
def _disjunctive(x: IntVector, dx: T_List):
    CIRCUITS = range(len(x))
    result = []
    for c1, c2 in combinations(CIRCUITS, 2):
        result.append(Or(x[c1] + dx[c1] <= x[c2], x[c2] + dx[c2] <= x[c1]))
    return And(result)


def _fzn_cumulative(x: T_List, dx: T_List, r: T_List, boundary: T_Number):
    result = []
    # x, dx, r = get_bool_lists(x, dx, r)

    CIRCUITS = range(len(x))
    for c_ref in CIRCUITS:
        xi = x[c_ref]
        ###  initialize sum at 0
        sum_at_xi = 0
        for c in CIRCUITS:
            _x, _dx, _r = (x[c], dx[c], r[c])
            ###  if condition then res_at_xi=_r else 0
            res_at_xi = 0
            ###  check if circuit==c is at x==xi
            condition = And(_x <= xi, xi < _x + _dx)

            ###  null the resource of circuit==c if condition not satisfied
            res_at_xi = If(condition, _r, 0)

            ###  update the sum
            sum_at_xi = sum_at_xi + res_at_xi

        ###  the sum of resources for all circuits at x==xi must not pass the boundary
        result.append(sum_at_xi <= boundary)

    return And(result)


def cumulative(x: T_List, dx: T_List, r: T_List, boundary: T_Number, min_r: int, idx_min_r: int) -> T_Z3Clause:

    assert len(x) == len(dx) == len(r), 'cumulative: the 3 array arguments must have identical length'
    CIRCUITS = range(len(x))

    ###  check if disjunctive can be used
    disj_cond = []
    for c in CIRCUITS:
        disj_cond.append(Or(r[c] + min_r > boundary, c == idx_min_r))
    disj_cond = And(disj_cond)
    result = [
        ###  disjunctive case
        Implies(disj_cond, _disjunctive(x, dx)),
        ###  fzn_cumulative case
        Implies(Not(disj_cond), _fzn_cumulative(x, dx, r, boundary))
    ]
    return And(result)


###


def symmetrical(x: T_List, dx: T_Number, start: int, end: int) -> T_Z3Clause:
    assert start >= 0 
    if isinstance(end, int): assert end > start

    ###  x' = end - (x[i]-start+dx[i])
    x_symm = [end - ((x[i] - start) + dx[i]) for i in range(len(x))]
    return x_symm

def _lex_lesseq(x: T_List, y: T_List):
    CIRCUITS = range(len(x))
    if not x:
        return False

    return And(x[0]<=y[0], Or(x[0]<y[0], _lex_lesseq(x[1:], y[1:])))

def axial_symmetry(x: T_List, dx: T_Number, start: int, end: int) -> T_Z3Clause:
    x_symm = symmetrical(x, dx, start, end)
    ###  constraint lexicographical ordering    
    return _lex_lesseq(x, x_symm)
"""