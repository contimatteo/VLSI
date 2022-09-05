from operator import indexOf

from z3 import BoolRef, And

###

Z3Clause = BoolRef

###


### simmetry braking constraint: biggest circuit in 0,0
def sym_bigger_circuit_origin(x, y, widths, heights) -> Z3Clause:
    assert len(x) == len(y) == len(widths) == len(heights)

    CIRCUITS = range(len(x))

    _c_areas = [widths[c] * heights[c] for c in CIRCUITS]
    _idx_of_bigger_circuit = indexOf(_c_areas, max(_c_areas))

    return And(y[_idx_of_bigger_circuit] == 0, x[_idx_of_bigger_circuit] == 0)
