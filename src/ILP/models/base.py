import time
from typing import List

import math

from ILP.models.__default import Z3Model as Z3DefaultModel
from ILP.models.components.helper import compute_max_makespan
from ILP.models.components.foundation import diffn  #, axial_symmetry, cumulative
# from ILP.models.components.symmetry import axial_symmetry

###

###


class Z3Model(Z3DefaultModel):

    @property
    def model_name(self) -> str:
        return "base"

    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths, heights = self.__variables_support(raw_data)

        CIRCUITS = range(n_circuits)

        ###  define makespan boundaries
        _c_area_sum = sum([heights[c] * widths[c] for c in CIRCUITS])
        ###  measure time needed for default solution
        t0 = time.time()
        default_solution = compute_max_makespan(heights, widths, width)
        time_default = int((time.time() - t0) * 1000)

        ###  redefine solver timeout
        self.solver_timeout -= time_default

        min_makespan = max(math.ceil(_c_area_sum / width), max(heights))
        max_makespan = default_solution["makespan"]
        default_solution['min_makespan'] = min_makespan
        target_makespan = self.solver.integer_var(lb=min_makespan, ub=max_makespan, name='makespan')

        ###  if no rotation -> both width and widths[c] are int values -> setting lb and ub avoid adding some constraints
        x = [
            self.solver.integer_var(name='x_' + str(c), lb=0, ub=width - widths[c])
            for c in CIRCUITS
        ]
        # x = self.solver.integer_var_list(n_circuits, lb=0, ub=width-min(widths), name='x')

        ###  makespan is docplex.mp.LinearExpr -> cannot be used to determine ub -> must be added explicitly as constraint
        y = self.solver.integer_var_list(n_circuits, lb=0, ub=max_makespan - min(heights), name='y')

        ###  all circuits must have each dimension greater than zero
        assert min(heights) > 0 and min(widths) > 0
        assert len(heights) == len(widths) == n_circuits

        ###  or variables for diffn
        n = n_circuits * (
            n_circuits - 1
        ) * 2  # == (n_circuits*(n_circuits-1) // 2) * 4 == n_combinations * 4
        diffn_vars = self.solver.binary_var_list(n, name='diffn_vars')

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths", "heights", "x", "y", "min_makespan",
            "max_makespan", "target_makespan", "default_solution", "diffn_vars"
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

    def _constraints(self, use_cumulative: bool):
        var = self.variables

        x = var["x"]
        y = var["y"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        makespan = var["target_makespan"]
        min_makespan = var["min_makespan"]
        max_makespan = var["max_makespan"]
        diffn_vars = var["diffn_vars"]
        CIRCUITS = var["CIRCUITS"]

        min_w, idx = self._get_min_w()
        min_h, idx = self._get_min_h()

        r = []
        r += diffn(x, y, widths, heights, diffn_vars)

        for c in CIRCUITS:
            r += [
                #         x[c] + widths[c] <= width,
                y[c] + heights[c] <= makespan
            ]

        # if use_cumulative:
        #     r += [cumulative(y, heights, widths, width, min_w, idx)]
        #     r += [cumulative(x, widths, heights, makespan, min_h, idx)]

        return r

    # def _symmetries_breaking(self) -> List[LinearConstraint]:
    #     var = self.variables

    #     x = var["x"]
    #     y = var["y"]
    #     width = var["width"]
    #     widths = var["widths"]
    #     heights = var["heights"]
    #     makespan = var["target_makespan"]

    #     return [
    #         # sym_bigger_circuit_origin(x, y, widths, heights),
    #         axial_symmetry(x, widths, start=0, end=width),
    #         axial_symmetry(y, heights, start=0, end=makespan)
    #     ]
