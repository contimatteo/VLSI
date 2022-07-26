from email.contentmanager import raw_data_manager
from typing import List, Tuple
from copy import deepcopy

import cplex


class cplexModel():

    def __init__(self, timeout: int = 300, seed: int = 666) -> None:
        self.solver = None
        self.variables = None

        self.solver_random_seed = seed
        self.solver_timeout = min(timeout, 300)

    def __configure_solver(self) -> None:
        self.solver = cplex.Cplex()
        # We want to minimize our objective function
        self.solver.objective.set_sense(self.solver.objective.sense.minimize)

    def __define_variables(self) -> None:
        raise NotImplementedError

    def __variables_support(self, raw_data: dict) -> Tuple[int, int, List[int], List[int]]:
        width = float(raw_data["width"])
        n_circuits = raw_data["n_circuits"]
        CIRCUITS = range(n_circuits)

        _dims = raw_data["dims"]
        ###  array of horizontal dimensions of the circuits
        widths = [float(_dims[c][0]) for c in CIRCUITS]
        ###  array of vertical dimensions of the circuits
        heights = [float(_dims[c][1]) for c in CIRCUITS]

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

    def _variables(self, raw_data: dict) -> dict:
        raise NotImplementedError

    def __coefficient_objective(self, raw_data) -> None:
        raise NotImplementedError

    def _addConstraints(self) -> None:
        raise NotImplementedError

    def initialize(self, raw_data: dict) -> None:
        assert raw_data is not None
        self.variables = self._variables(deepcopy(raw_data))

        self.__validate_variables()
        self.__configure_solver()
        self.__coefficient_objective(raw_data=raw_data)

    def solve(self, file_name: str, symmetry: bool) -> dict:
        solutions_dict = { ### each solution in all_solutions is a dict
            "all_solutions": [],
            "solution": {},
            "stats": [],
            "model": "base",
            "file": file_name,
            "data": self.variables,
            "solver": "cplex ILP",
            "totalTime": 0
        }

        self._addConstraints()

        self.solver.solve()
        print(self.solver.linear_constraints.get_rows())
        print()
        print(self.solver.solution.get_values())