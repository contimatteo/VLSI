from typing import List

import math

from z3 import Bool, And, Or, Not, BoolRef, Solver

from SAT.models.base import Z3Model as Z3BaseModel
from SAT.models.components.helper import compute_max_makespan
from SAT.models.components.foundation import diffn, lte, sub_b, axial_symmetry, pad, eq, int2boolList
# from SAT.models.components.symmetry import axial_symmetry

###  FIXME: AssertionError "assert solutions_dict is not None and isinstance(solutions_dict, dict)"

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model(Z3BaseModel):
    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths_int, heights_int = self.__variables_support(raw_data)

        ### define makespan boundaries
        _c_area_sum = sum([heights_int[c] * widths_int[c] for c in CIRCUITS])
        min_makespan = max(math.ceil(_c_area_sum / width), max(heights_int))
        max_makespan = compute_max_makespan(heights_int, widths_int, width)

        ### + max(widths) is necessary for summing the width later
        _x_domain_max = width - min(widths_int + heights_int) + max(widths_int + heights_int)
        _x_domain_size = math.ceil(math.log2(_x_domain_max)) if _x_domain_max > 0 else 1

        ### + max(heights) is necessary for summing the height later
        _y_domain_max = max_makespan - min(heights_int + widths_int) + max(heights_int + widths_int)
        _y_domain_size = math.ceil(math.log2(_y_domain_max)) if _y_domain_max > 0 else 1

        x = [[Bool(f"x_of_c{c}_{i}") for i in range(_x_domain_size)] for c in CIRCUITS]
        y = [[Bool(f"y_of_c{c}_{i}") for i in range(_y_domain_size)] for c in CIRCUITS]

        ### all circuits must have each dimension greater than zero
        assert min(heights_int) > 0 and min(widths_int) > 0
        assert len(heights_int) == len(widths_int) == n_circuits

        ###  width and heigth variables for rotation
        _max_dim = max(widths_int + heights_int)
        _dims_domain_size = math.ceil(math.log2(_max_dim))
        widths  = [[Bool(f"w_of_c{c}_{i}") for i in range(_dims_domain_size)] for c in CIRCUITS]
        heights = [[Bool(f"h_of_c{c}_{i}") for i in range(_dims_domain_size)] for c in CIRCUITS]

        is_rotated = [Bool(f"r_c{c}") for c in CIRCUITS]

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths_int", "heights_int", "x", "y", "min_makespan",
            "max_makespan", "widths", "heights", "is_rotated", "_dims_domain_size"
        ]

        _local_vars = locals()

        return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}

    def _constraints(self) -> List[T_Z3Clause]:
        var = self.variables

        widths = var["widths_int"]
        heights = var["heights_int"]
        widths_b = var["widths"]
        heights_b = var["heights"]
        r = var["is_rotated"]
        CIRCUITS = var["CIRCUITS"]
        max_len = var["_dims_domain_size"]

        eq_list = []
        for c in CIRCUITS:
            w = pad(int2boolList(widths[c]), max_len)
            h = pad(int2boolList(heights[c]), max_len)
            w_rot = []
            h_rot = []
            for i in range(max_len):
                w_rot.append(
                    Or(And(r[c], h[i]), And(Not(r[c]), w[i]))
                )
                h_rot.append(
                    Or(And(Not(r[c]), h[i]), And(r[c], w[i]))
                )
            eq_list.append(eq(widths_b[c],  w_rot))
            eq_list.append(eq(heights_b[c], h_rot))

        return super()._constraints() + eq_list
            

