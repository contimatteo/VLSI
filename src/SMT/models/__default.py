from typing import List, Tuple
from copy import deepcopy

import time
import z3

from z3 import BoolRef, Solver, Optimize

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model():

    def __init__(self, timeout: int = 300, seed: int = 666) -> None:
        self.solver = None
        self.variables = None

        self.solver_random_seed = seed
        self.solver_timeout = min(timeout, 300) * 1000

    #

    def __configure_solver(self) -> None:
        self.solver = Optimize()

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

    @property
    def model_name(self) -> str:
        raise NotImplementedError

    def _variables(self, raw_data: dict) -> dict:
        raise NotImplementedError

    def _constraints(self) -> List[T_Z3Clause]:
        raise NotImplementedError

    def _symmetries_breaking(self) -> List[T_Z3Clause]:
        raise NotImplementedError

    def _dynamic_constraints(self, makespan: int) -> List[T_Z3Clause]:
        raise NotImplementedError

    def _dynamic_symmetries_breaking(self, makespan: int) -> List[T_Z3Clause]:
        raise NotImplementedError

    def _evaluate_solution(self, model, min_makespan: int, max_makespan: int):
        solution = {
            "width": self.variables['width'],
            "n_circuits": self.variables["n_circuits"],
            "widths": self.variables['widths'],
            "heights": self.variables['heights'],
            "x":
            [model.evaluate(self.variables['x'][c]).as_long() for c in self.variables['CIRCUITS']],
            "y":
            [model.evaluate(self.variables['y'][c]).as_long() for c in self.variables['CIRCUITS']],
            "min_makespan": min_makespan,
            "max_makespan": max_makespan,
            "makespan": model.evaluate(self.variables['target_makespan']).as_long()
        }
        return solution

    ###

    def initialize(self, raw_data: dict) -> None:
        assert raw_data is not None
        self.variables = self._variables(deepcopy(raw_data))

        self.__validate_variables()
        self.__configure_solver()

    def solve(self, file_name: str, symmetry: bool, use_cumulative: bool) -> dict:
        solutions_dict = {
            "solver": "SMT",
            "model": self.model_name,
            "data_file": file_name,
            "search": "linear",
            "symmetry": symmetry,
            "cumulative": use_cumulative,
            "TOTAL_TIME": 0,
            "stats": [],
            "solution": {},
            "all_solutions": [],
        }

        min_makespan = self.variables["min_makespan"]
        max_makespan = self.variables["max_makespan"]
        target_makespan = self.variables["target_makespan"]

        #

        for clause in self._constraints(use_cumulative):
            self.solver.add(clause)

        if symmetry:
            for clause in self._symmetries_breaking():
                self.solver.add(clause)

        ### solve

        self.solver.set('timeout', self.solver_timeout)
        self.solver.minimize(target_makespan)

        time_before_exec_start = time.time()

        check = self.solver.check()
        time_spent = time.time() - time_before_exec_start

        solution = None

        if check == z3.sat:
            solution = self._evaluate_solution(
                self.solver.model(),
                min_makespan,
                max_makespan,
            )

        #

        assert solution is not None

        solutions_dict["TOTAL_TIME"] = time_spent
        solutions_dict["all_solutions"] = [solution]
        solutions_dict["solution"] = solution

        return solutions_dict
