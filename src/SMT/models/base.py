import time
from typing import List

import math

from z3 import Bool, And, BoolRef, Solver, IntVector, Int

from SMT.models.__default import Z3Model as Z3DefaultModel
from SMT.models.components.helper import compute_max_makespan
from SMT.models.components.foundation import diffn, axial_symmetry, cumulative
# from SMT.models.components.symmetry import axial_symmetry

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model(Z3DefaultModel):

    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths, heights = self.__variables_support(raw_data)

        ###  define makespan boundaries
        _c_area_sum = sum([heights[c] * widths[c] for c in CIRCUITS])
        ###  measure time needed for default solution
        t0 = time.time()
        default_solution = compute_max_makespan(heights, widths, width)
        time_default = int((time.time() - t0) * 1000)
        print('time spent for default solution:', time_default)
        ###  redefine solver timeout
        self.solver_timeout -= time_default

        min_makespan = max(math.ceil(_c_area_sum / width), max(heights))
        max_makespan = default_solution["makespan"]
        default_solution['min_makespan'] = min_makespan
        target_makespan = Int('makespan')

        x = IntVector('x', n_circuits)
        y = IntVector('y', n_circuits)

        ### all circuits must have each dimension greater than zero
        assert min(heights) > 0 and min(widths) > 0
        assert len(heights) == len(widths) == n_circuits

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths", "heights", "x", "y", "min_makespan",
            "max_makespan", "target_makespan", "default_solution"
        ]

        _local_vars = locals()

        return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}

    #

    def _get_min_w(self):
        min_w = min(self.variables['widths'])
        idx = self.variables['widths'].index(min_w)
        return min_w, idx

    def _get_min_h(self):
        min_h = min(self.variables['heights'])
        idx = self.variables['heights'].index(min_h)
        return min_h, idx

    def _constraints(self, use_cumulative: bool) -> List[T_Z3Clause]:
        var = self.variables

        x = var["x"]
        y = var["y"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        makespan = var["target_makespan"]
        min_makespan = var["min_makespan"]
        max_makespan = var["max_makespan"]
        CIRCUITS = var["CIRCUITS"]

        min_w, idx = self._get_min_w()
        min_h, idx = self._get_min_h()

        r = [
            diffn(x, y, widths, heights),
            ### forall(c in CIRCUITS)(x[c] + widths[c] <= width)
            # And([lte(x[c] + widths[c], width) for c in CIRCUITS]),
            And(makespan <= max_makespan, makespan >= min_makespan),
            And([And(x[c] >= 0, y[c] >= 0) for c in CIRCUITS]),
            And([x[c] + widths[c] <= width for c in CIRCUITS]),
            And([y[c] + heights[c] <= makespan for c in CIRCUITS])
        ]

        if use_cumulative:
            r += [cumulative(y, heights, widths, width, min_w, idx)]
            r += [cumulative(x, widths, heights, makespan, min_h, idx)]

        return r

    def _symmetries_breaking(self) -> List[T_Z3Clause]:
        var = self.variables

        x = var["x"]
        y = var["y"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        makespan = var["target_makespan"]

        return [
            # sym_bigger_circuit_origin(x, y, widths, heights),
            axial_symmetry(x, widths, start=0, end=width),
            axial_symmetry(y, heights, start=0, end=makespan)
        ]
