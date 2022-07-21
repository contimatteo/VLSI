from typing import List

import math

from z3 import Bool, And, BoolRef, Solver

from SAT.models.__default import Z3Model as Z3DefaultModel
from SAT.models.components.helper import compute_max_makespan
from SAT.models.components.foundation import diffn, lte, sub_b, axial_symmetry
# from SAT.models.components.symmetry import axial_symmetry

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model(Z3DefaultModel):

    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths, heights = self.__variables_support(raw_data)

        ### define makespan boundaries
        _c_area_sum = sum([heights[c] * widths[c] for c in CIRCUITS])
        min_makespan = max(math.ceil(_c_area_sum / width), max(heights))
        max_makespan = compute_max_makespan(heights, widths, width)

        ### + max(widths) is necessary for summing the width later
        _x_domain_max = width - min(widths) + max(widths)
        _x_domain_size = math.ceil(math.log2(_x_domain_max)) if _x_domain_max > 0 else 1

        ### + max(heights) is necessary for summing the height later
        _y_domain_max = max_makespan - min(heights) + max(heights)
        _y_domain_size = math.ceil(math.log2(_y_domain_max)) if _y_domain_max > 0 else 1

        x = [[Bool(f"x_of_c{c}_{i}") for i in range(_x_domain_size)] for c in CIRCUITS]
        y = [[Bool(f"y_of_c{c}_{i}") for i in range(_y_domain_size)] for c in CIRCUITS]

        #

        ### all circuits must have each dimension greater than zero
        assert min(heights) > 0 and min(widths) > 0
        assert len(heights) == len(widths) == n_circuits

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths", "heights", "x", "y", "min_makespan",
            "max_makespan"
        ]

        _local_vars = locals()

        return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}

    #

    def _constraints(self) -> List[T_Z3Clause]:
        var = self.variables

        x = var["x"]
        y = var["y"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        CIRCUITS = var["CIRCUITS"]

        return [
            diffn(x, y, widths, heights),
            ### forall(c in CIRCUITS)(x[c] + widths[c] <= width)
            # And([lte(x[c], width - widths[c]) for c in CIRCUITS]),
            And([lte(x[c], sub_b(width, widths[c])) for c in CIRCUITS])
        ]

    def _symmetries_breaking(self) -> List[T_Z3Clause]:
        var = self.variables

        x = var["x"]
        width = var["width"]
        widths = var["widths"]

        return [
            # sym_bigger_circuit_origin(x, y, widths, heights),
            # axial_symmetry(x, widths, start=0, end=width),
        ]

    #

    def _dynamic_constraints(self, makespan: int) -> List[T_Z3Clause]:
        var = self.variables

        y = var["y"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        CIRCUITS = var["CIRCUITS"]

        return [
            ### forall(c in CIRCUITS)(y[c] + heights[c] <= target_makespan)
            # And([lte(var["y"][c], makespan - var["heights"][c]) for c in var["CIRCUITS"]]),
            And([lte(y[c], sub_b(makespan, heights[c])) for c in CIRCUITS])
        ]

    def _dynamic_symmetries_breaking(self, makespan: int) -> List[T_Z3Clause]:
        var = self.variables

        y = var["y"]
        heights = var["heights"]

        return [
            # axial_symmetry(y, heights, start=0, end=makespan),
        ]
