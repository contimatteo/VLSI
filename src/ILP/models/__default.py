from typing import List, Tuple
from copy import deepcopy

import time
from docplex.mp.model import Model

# from ILP.models.components.foundation import bool2int

###

###


class Z3Model():

    def __init__(self, timeout: int = 300, seed: int = 666) -> None:
        self.solver = None
        self.variables = None

        self.solver_random_seed = seed
        self.solver_timeout = min(timeout, 300)

    #

    def __configure_solver(self) -> None:
        self.solver = Model(name='VLSI model')

        # self.solver.set("smt.local_search", True)
        # self.solver.set("smt.local_search_threads", 1)
        # self.solver.set("smt.threads", 3)
        # self.solver.set("smt.lookahead_simplify", True)
        # self.solver.set("smt.lookahead.use_learned", True)

        # self.solver.set_time_limit(self.solver_timeout)

    def __variables_support(self, raw_data: dict) -> Tuple[int, int, List[int], List[int]]:
        width = raw_data["width"]
        n_circuits = raw_data["n_circuits"]
        CIRCUITS = list(range(n_circuits))

        _dims = raw_data["dims"]
        ###  array of horizontal dimensions of the circuits
        widths = [_dims[c][0] for c in CIRCUITS]
        ###  array of vertical dimensions of the circuits
        heights = [_dims[c][1] for c in CIRCUITS]

        return width, n_circuits, CIRCUITS, widths, heights

    def __validate_variables(self):
        var = self.variables

        width = var["width"]
        assert width is not None

        n_circuits, CIRCUITS = var["n_circuits"], var["CIRCUITS"]
        assert n_circuits is not None and CIRCUITS is not None

        widths, heights = var["widths"], var["heights"]
        assert len(widths) > 0 and len(heights) > 0

        x, y = var["x"], var["y"]
        assert len(x) > 0 and len(y) > 0

        min_makespan, max_makespan = var["min_makespan"], var["max_makespan"]
        assert min_makespan is not None and max_makespan is not None

    #

    def _variables(self, raw_data: dict) -> dict:
        raise NotImplementedError

    def _constraints(self):
        raise NotImplementedError

    def _symmetries_breaking(self):
        raise NotImplementedError

    def _dynamic_constraints(self, makespan: int):
        raise NotImplementedError

    def _dynamic_symmetries_breaking(self, makespan: int):
        raise NotImplementedError

    def _evaluate_solution(self, min_makespan: int, max_makespan: int):
        CIRCUITS = self.variables['CIRCUITS']
        solution = {
            "width": self.variables['width'],
            "n_circuits": self.variables["n_circuits"],
            "widths": self.variables['widths'],
            "heights": self.variables['heights'],
            "x": [self.variables['x'][c].solution_value for c in CIRCUITS],
            "y": [self.variables['y'][c].solution_value for c in CIRCUITS],
            "min_makespan": min_makespan,
            "max_makespan": max_makespan,
            "makespan": self.variables['target_makespan'].solution_value
        }
        return solution

    ###

    def initialize(self, raw_data: dict) -> None:
        assert raw_data is not None
        self.__configure_solver()
        self.variables = self._variables(deepcopy(raw_data))
        self.__validate_variables()

    def solve(self, file_name: str, symmetry: bool, use_cumulative: bool) -> dict:
        solutions_dict = { ### each solution in all_solutions is a dict
            "all_solutions": [],
            "solution": {},
            "stats": [],
            "model": "base",
            "data_file": file_name,
            "data": self.variables,
            "solver": "z3 SAT",
            "TOTAL_TIME": 0
        }

        min_makespan = self.variables["min_makespan"]
        max_makespan = self.variables["max_makespan"]
        target_makespan = self.variables["target_makespan"]
        default_solution = self.variables["default_solution"]

        #

        for clause in self._constraints(use_cumulative):
            self.solver.add_constraint(clause)

        if symmetry:
            for clause in self._symmetries_breaking():
                self.solver.add_constraint(clause)

        #
        self.solver.minimize(target_makespan)

        t0 = time.time()
        check = self.solver.solve()

        time_spent = time.time() - t0
        if time_spent >= self.solver_timeout:
            print('time exceeded, optimal solution not found')
            solution = default_solution
        else:
            print('solver found at least one solution')
            solution = self._evaluate_solution(min_makespan, max_makespan)
            print(f"TOTAL TIME = {round(time_spent, 2)}")

        solutions_dict["TOTAL_TIME"] = time_spent
        solutions_dict["all_solutions"].append(solution)
        solutions_dict["solution"] = solution
        return solutions_dict
