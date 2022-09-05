from typing import List

import math
import time

from z3 import Bool, And, Or, Not, BoolRef, Solver, Int, IntVector, BoolVector, If

from SMT.models.base import Z3Model as Z3BaseModel
from SMT.models.components.helper import compute_max_makespan
from SMT.models.components.foundation import diffn, axial_symmetry
# from SAT.models.components.symmetry import axial_symmetry

###  FIXME: AssertionError "assert solutions_dict is not None and isinstance(solutions_dict, dict)"

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model(Z3BaseModel):

    @property
    def model_name(self) -> str:
        return "rotation"

    #

    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths_int, heights_int = self.__variables_support(raw_data)

        ### define makespan boundaries
        _c_area_sum = sum([heights_int[c] * widths_int[c] for c in CIRCUITS])
        ###  measure time needed for default solution
        t0 = time.time()
        default_solution = compute_max_makespan(heights_int, widths_int, width)
        time_default = int((time.time() - t0) * 1000)

        ###  redefine solver timeout
        self.solver_timeout -= time_default

        min_makespan = max(math.ceil(_c_area_sum / width), max(heights_int))
        max_makespan = default_solution["makespan"]
        default_solution['min_makespan'] = min_makespan
        target_makespan = Int('makespan')

        x = IntVector('x', n_circuits)
        y = IntVector('y', n_circuits)

        ### all circuits must have each dimension greater than zero
        assert min(heights_int) > 0 and min(widths_int) > 0
        assert len(heights_int) == len(widths_int) == n_circuits

        ###  width and heigth variables for rotation

        widths = IntVector('w', n_circuits)
        heights = IntVector('h', n_circuits)

        is_rotated = BoolVector('is_rotated', n_circuits)

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths_int", "heights_int", "x", "y",
            "min_makespan", "max_makespan", "target_makespan", "widths", "heights", "is_rotated",
            "default_solution"
        ]

        _local_vars = locals()

        return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}

    def _get_min_dim(self):
        dims = self.variables['widths_int'] + self.variables['heights_int']
        min_dim = min(dims)
        idx = dims.index(min_dim) % len(self.variables['widths_int'])
        return min_dim, idx

    def _get_min_w(self):
        return self._get_min_dim()

    def _get_min_h(self):
        return self._get_min_dim()

    def _constraints(self, use_cumulative: bool) -> List[T_Z3Clause]:
        var = self.variables

        widths = var["widths_int"]
        heights = var["heights_int"]
        widths_b = var["widths"]
        heights_b = var["heights"]
        is_rotated = var["is_rotated"]
        CIRCUITS = var["CIRCUITS"]

        link_w = [widths_b[c] == If(is_rotated[c], heights[c], widths[c]) for c in CIRCUITS]
        link_h = [heights_b[c] == If(is_rotated[c], widths[c], heights[c]) for c in CIRCUITS]

        return super()._constraints(use_cumulative) + link_w + link_h

    def _evaluate_solution(self, model, min_makespan, max_makespan):
        solution = {
            "width":
            self.variables['width'],
            "n_circuits":
            self.variables["n_circuits"],
            "widths": [
                model.evaluate(self.variables['widths'][c]).as_long()
                for c in self.variables['CIRCUITS']
            ],
            "heights": [
                model.evaluate(self.variables['heights'][c]).as_long()
                for c in self.variables['CIRCUITS']
            ],
            "x":
            [model.evaluate(self.variables['x'][c]).as_long() for c in self.variables['CIRCUITS']],
            "y":
            [model.evaluate(self.variables['y'][c]).as_long() for c in self.variables['CIRCUITS']],
            "min_makespan":
            min_makespan,
            "max_makespan":
            max_makespan,
            "makespan":
            model.evaluate(self.variables['target_makespan']).as_long()
        }

        return solution

