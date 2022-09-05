from typing import List, Union

from itertools import combinations
import uuid

###

###

# M = int(1e10)


def diffn(x, y, widths, heigths, diffn_vars, M):
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
            ###  if diffn_vars[i+1] == 1 c1 on the right of c2
            ###  if diffn_vars[i+1] == 0 make true the case x[c1] - x[c2] >= widths[c2]
            x[c1] - x[c2] >= widths[c2] - M * (1 - diffn_vars[i+1]),
            ###  if diffn_vars[i] == 1 c1 on the left of c2
            ###  if diffn_vars[i] == 0 make true the case x[c2] - x[c1] >= widths[c1]
            x[c2] - x[c1] >= widths[c1] - M * (1 - diffn_vars[i]),
            ###  if diffn_vars[i+2] == 1 c1 on top of c2
            ###  if diffn_vars[i+2] == 0 make true the case y[c1] - y[c2] >= heigths[c2]
            y[c1] - y[c2] >= heigths[c2] - M * (1 - diffn_vars[i+2]),
            ###  if diffn_vars[i+3] == 1 c1 under c2
            ###  if diffn_vars[i+3] == 0 make true the case y[c1] - y[c2] >= heigths[c2]
            y[c2] - y[c1] >= heigths[c1] - M * (1 - diffn_vars[i+3]),
            ###  at least one of the conditions above must be applied
            diffn_vars[i] + diffn_vars[i+1] + diffn_vars[i+2] + diffn_vars[i+3] >= 1,
            ###  if c1 on the right it cannot be on the left, the same for top and bottom
            diffn_vars[i] + diffn_vars[i+1] + diffn_vars[i+2] + diffn_vars[i+3] <= 2,
        ]
        i += 4

    return result