from typing import Any, Tuple, Union, List

import z3

from z3 import Solver, Bool, BoolRef

from SAT.models.components import foundation as FN

###


def __solve(expr: Any) -> Tuple[bool, Solver]:
    solver = Solver()
    solver.add(expr)
    result = solver.check()

    if result == z3.sat:
        return True, solver
    if result == z3.unsat:
        return False, None

    raise Exception("[__solve] unrecognized result type.")


def __evaluate(solver: Solver, expr) -> Tuple[Any, Any]:

    def __solver_var_evaluation(variable: Union[BoolRef, List[BoolRef]]):
        if isinstance(variable, BoolRef):
            return solver.model().evaluate(variable)
        if isinstance(variable, list):
            return [solver.model().evaluate(v) for v in variable]

    var1, var2 = expr[0], expr[1]
    var1_evaluated, var2_evaluated = None, None

    if isinstance(var1, bool) or (isinstance(var1, list) and isinstance(var1[0], bool)):
        var1_evaluated = var1
    else:
        var1_evaluated = __solver_var_evaluation(var1)

    if isinstance(var2, bool) or (isinstance(var2, list) and isinstance(var2[0], bool)):
        var2_evaluated = var2
    else:
        var2_evaluated = __solver_var_evaluation(var2)

    return var1_evaluated, var2_evaluated


###

# def test_eq():

#     clause = lambda values: FN.eq(*values)

#     T_exprs = [
#         (True, True),
#         (False, False),
#         ([True], [True]),
#         ([False], [False]),
#         ([True, True], [True, True]),
#         ([False, False], [False, False]),
#     ]

#     F_exprs = [
#         (True, False),
#         (False, True),
#         ([True], [False]),
#         ([False], [True]),
#         ([True, False], [False, True]),
#         ([False, True], [True, False]),
#     ]

#     for expr in T_exprs:
#         assert __solve(clause(expr)) is True, str(expr)

#     for expr in F_exprs:
#         assert __solve(clause(expr)) is False, str(expr)


def test_ne():
    __apply_clause = lambda values: FN.ne(*values)

    T_exprs = [
        (True, Bool("x11")),
        (False, Bool("x21")),
        ([True], [Bool("x31")]),
        ([False], [Bool("x41")]),
        ([True, True], [Bool("x51"), Bool("x52")]),
        ([False, False], [Bool("x61"), Bool("x62")]),
        ([True, False], [Bool("x71"), Bool("x72")]),
        ([False, True], [Bool("x81"), Bool("x82")]),
    ]

    for expr in T_exprs:
        clause = __apply_clause(expr)

        satisfied, solver = __solve(clause)
        assert satisfied is True, str(expr)

        if satisfied:
            val1, val2 = __evaluate(solver, expr)
            print(val1, val2)
