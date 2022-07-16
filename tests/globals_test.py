from typing import Any

import z3

from z3 import Solver

from SAT.models.components import foundation as FN

###


def __solve(expr: Any) -> bool:
    solver = Solver()
    solver.add(expr)
    result = solver.check()

    if result == z3.sat:
        return True
    if result == z3.unsat:
        return False

    raise Exception("[__solve] unrecognized result type.")


###


def test_eq():

    clause = lambda values: FN.eq(*values)

    T_exprs = [
        (True, True),
        (False, False),
        ([True], [True]),
        ([False], [False]),
        ([True, True], [True, True]),
        ([False, False], [False, False]),
    ]

    F_exprs = [
        (True, False),
        (False, True),
        ([True], [False]),
        ([False], [True]),
        ([True, False], [False, True]),
        ([False, True], [True, False]),
    ]

    for expr in T_exprs:
        assert __solve(clause(expr)) is True, str(expr)

    for expr in F_exprs:
        assert __solve(clause(expr)) is False, str(expr)
