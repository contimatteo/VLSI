import math
import time

from ILP.models.base import CplexModel as CplexBaseModel
from ILP.models.components.helper import compute_max_makespan

###


class CplexModel(CplexBaseModel):

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
        target_makespan = self.solver.integer_var(lb=min_makespan, ub=max_makespan, name='makespan')

        x = self.solver.integer_var_list(n_circuits, lb=0, ub=width - min(widths_int), name='x')
        y = self.solver.integer_var_list(
            n_circuits, lb=0, ub=max_makespan - min(heights_int), name='y'
        )

        ### all circuits must have each dimension greater than zero
        assert min(heights_int) > 0 and min(widths_int) > 0
        assert len(heights_int) == len(widths_int) == n_circuits

        ###  width and heigth variables for rotation

        widths = [
            self.solver.integer_var(
                name='w_' + str(c),
                lb=min(heights_int[c], widths_int[c]),
                ub=max(heights_int[c], widths_int[c])
            ) for c in CIRCUITS
        ]
        heights = [
            self.solver.integer_var(
                name='h_' + str(c),
                lb=min(heights_int[c], widths_int[c]),
                ub=max(heights_int[c], widths_int[c])
            ) for c in CIRCUITS
        ]

        is_rotated = self.solver.binary_var_list(n_circuits, name='is_rotated')

        ###  or variables for diffn
        n = n_circuits * (
            n_circuits - 1
        ) * 2  # == (n_circuits*(n_circuits-1) // 2) * 4 == n_combinations * 4
        diffn_vars = self.solver.binary_var_list(n, name='diffn_vars')

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths_int", "heights_int", "x", "y",
            "min_makespan", "max_makespan", "target_makespan", "widths", "heights", "is_rotated",
            "default_solution", "diffn_vars"
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

    def _constraints(self):
        var = self.variables

        width = var["width"]
        x = var["x"]
        widths = var["widths_int"]
        heights = var["heights_int"]
        widths_b = var["widths"]
        heights_b = var["heights"]
        is_rotated = var["is_rotated"]
        CIRCUITS = var["CIRCUITS"]

        link_w = [
            widths_b[c] == heights[c] * is_rotated[c] + widths[c] * (1 - is_rotated[c])
            for c in CIRCUITS
        ]
        link_h = [
            heights_b[c] == widths[c] * is_rotated[c] + heights[c] * (1 - is_rotated[c])
            for c in CIRCUITS
        ]

        x_constr = [x[c] + widths_b[c] <= width for c in CIRCUITS]

        return super()._constraints() + link_w + link_h + x_constr

    def _evaluate_solution(self, min_makespan, max_makespan):
        CIRCUITS = self.variables['CIRCUITS']
        solution = {
            "width": self.variables['width'],
            "n_circuits": self.variables["n_circuits"],
            "widths": [self.variables['widths'][c].solution_value for c in CIRCUITS],
            "heights": [self.variables['heights'][c].solution_value for c in CIRCUITS],
            "x": [self.variables['x'][c].solution_value for c in CIRCUITS],
            "y": [self.variables['y'][c].solution_value for c in CIRCUITS],
            "min_makespan": min_makespan,
            "max_makespan": max_makespan,
            "makespan": self.variables['target_makespan'].solution_value
        }
        print(solution)
        return solution

