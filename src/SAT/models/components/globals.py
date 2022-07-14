from typing import List, Union
from itertools import combinations

from z3 import Bool, Probe, BoolRef
from z3 import Or, And, Not, Xor

###

BoolOrList = Union[List[Bool], Bool]
Z3Operator = Union[Probe, BoolRef]  # Union[Union[Any, Probe], BoolRef]
Z3Operators = List[Z3Operator]

###


def at_least_one_T(bools: List[Bool]) -> Z3Operator:
    return Or(bools)


def at_most_one_T(bools: List[Bool]) -> Z3Operators:

    def __T_values(b1: Bool, b2: Bool) -> Z3Operator:
        return And(b1, b2)

    return [Not(__T_values(b1, b2)) for b1, b2 in combinations(bools, 2)]


def exactly_one_T(bools: List[Bool]) -> Z3Operators:
    return at_most_one_T(bools) + [at_least_one_T(bools)]


def ne(bol1: BoolOrList, bol2: BoolOrList) -> Union[Z3Operator, Z3Operators]:

    def __ne(b1: Bool, b2: Bool) -> Z3Operator:
        return Xor(b1, b2)

    assert isinstance(bol1, list) or isinstance(bol2, Z3Operator)
    assert isinstance(bol1, list) or isinstance(bol2, Z3Operator)

    if isinstance(bol1, Z3Operator) and isinstance(bol2, Z3Operator):
        return __ne(bol1, bol2)

    if isinstance(bol1, list) and isinstance(bol2, list):
        assert len(bol1) == len(bol2)
        return Or([__ne(b1, b2) for b1, b2 in zip(bol1, bol2)])

    raise Exception("[ne] invalid parameters types.")


def eq(bol1: BoolOrList, bol2: BoolOrList) -> Union[Z3Operator, Z3Operators]:

    def __eq(b1: Bool, b2: Bool) -> Z3Operator:
        return Not(Xor(b1, b2))

    assert isinstance(bol1, list) or isinstance(bol2, Z3Operator)
    assert isinstance(bol1, list) or isinstance(bol2, Z3Operator)

    if isinstance(bol1, Z3Operator) and isinstance(bol2, Z3Operator):
        return __eq(bol1, bol2)

    if isinstance(bol1, list) and isinstance(bol2, list):
        assert len(bol1) == len(bol2)
        return And([__eq(b1, b2) for b1, b2 in zip(bol1, bol2)])

    raise Exception("[eq] invalid parameters types.")
