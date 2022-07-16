from typing import List, Union
from itertools import combinations

from z3 import Bool, BoolRef
from z3 import Or, And, Not, Xor

###

BoolOrList = Union[List[Bool], Bool]
Z3Clause = BoolRef

###


def __is_bool(val: Union[bool, BoolRef]) -> bool:
    return isinstance(val, bool) or isinstance(val, BoolRef)


###


def all_F(l: 'list[Bool]'):
    return And([Not(b) for b in l])


def at_least_one_T(bools: List[Bool]) -> Z3Clause:
    return Or(bools)


def at_most_one_T(bools: List[Bool]) -> Z3Clause:
    return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])


def exactly_one_T(bools: List[Bool]) -> Z3Clause:
    return And(at_most_one_T(bools) + [at_least_one_T(bools)])


def ne(bol1: BoolOrList, bol2: BoolOrList) -> Z3Clause:
    return Not(eq(bol1, bol2))


def eq(bol1: BoolOrList, bol2: BoolOrList) -> Z3Clause:

    def __eq(b1: Bool, b2: Bool) -> Z3Clause:
        return Not(Xor(b1, b2))

    assert isinstance(bol1, list) or __is_bool(bol1)
    assert isinstance(bol1, list) or __is_bool(bol2)

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
