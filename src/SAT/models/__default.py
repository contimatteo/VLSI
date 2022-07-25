from typing import List, Tuple
from copy import deepcopy

import time
import z3

from z3 import BoolRef, Solver

from SAT.models.components.foundation import bool2int

###

T_Z3Clause = BoolRef
T_Z3Solver = Solver

###


class Z3Model():

    def __init__(self, timeout: int = 300, seed: int = 666) -> None:
        self.solver = None
        self.variables = None

        self.solver_random_seed = seed
        self.solver_timeout = min(timeout, 300)

    #

    def __configure_solver(self) -> None:
        self.solver = Solver()

        # self.solver.set("sat.local_search", True)
        # self.solver.set("sat.local_search_threads", 1)
        # self.solver.set("sat.threads", 3)
        # self.solver.set("sat.lookahead_simplify", True)
        # self.solver.set("sat.lookahead.use_learned", True)
        self.solver.set('sat.random_seed', self.solver_random_seed)

    def __variables_support(self, raw_data: dict) -> Tuple[int, int, List[int], List[int]]:
        width = raw_data["width"]
        n_circuits = raw_data["n_circuits"]
        CIRCUITS = range(n_circuits)

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

        min_makespan, max_makespan = var["min_makespan"]-10, var["max_makespan"]
        assert min_makespan is not None and max_makespan is not None

    #

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

    def _evaluate_solution(self, model, min_makespan: int, max_makespan: int, target_makespan: int):
        solution = {
            "width": self.variables['width'],
            "n_circuits": self.variables["n_circuits"],
            "widths": self.variables['widths'],
            "heights": self.variables['heights'],
            "x": [
                bool2int([model.evaluate(self.variables['x'][c][i]) for i in range(self.variables['_x_domain_size'])])
                for c in self.variables['CIRCUITS']
            ],
            "y": [
                bool2int([model.evaluate(self.variables['y'][c][i]) for i in range(self.variables['_y_domain_size'])])
                for c in self.variables['CIRCUITS']
            ],
            "min_makespan": min_makespan,
            "max_makespan": max_makespan,
            "makespan": target_makespan
        } 
        
        return solution

    def _get_target_makespan(self, min_m: int, max_m: int, target_m: int, sat: bool, search: str):
        if search=='linear':
            ###  if unsat increase target makespan
            min_makespan = min_m if sat else min_m + 1
            max_makespan = max_m
            target_makespan = min_makespan
            done = sat
        elif search=='binary':
            ###  ISSUE: optimal solution evaluated twice
            ###  target makespan == mean value between min and max makespan
            ###  if sat -> decrease max makespan, if unsat -> increase min makespan
            min_makespan = min_m    if sat else target_m +1
            max_makespan = target_m if sat else max_m
            target_makespan = (max_makespan+min_makespan) // 2
            ###  if min makespan is sat, done=True
            done = True if sat and target_m==min_m else False
        else:
            raise NotImplementedError('Not implemented {} search strategy'.format(search))

        ###  if done, do not update parameters
        if done: 
            return done, min_m, max_m, target_m
        else:
            return done, min_makespan, max_makespan, target_makespan

    ###

    def initialize(self, raw_data: dict) -> None:
        assert raw_data is not None
        self.variables = self._variables(deepcopy(raw_data))

        self.__validate_variables()
        self.__configure_solver()

    def solve(self, file_name: str, search: str, symmetry: bool) -> dict:
        solutions_dict = { ### each solution in all_solutions is a dict
            "all_solutions": [],
            "solution": {},
            "stats": [],
            "model": "base",
            "file": file_name,
            "data": self.variables,
            "solver": "z3 SAT",
            "totalTime": 0
        }
        # vars_dict = self._variables(raw_data)
        # width = vars_dict["width"]
        # assert width is not None
        # n_circuits, CIRCUITS = vars_dict["n_circuits"], vars_dict["CIRCUITS"]
        # assert n_circuits is not None and CIRCUITS is not None
        # widths, heigths = vars_dict["widths"], vars_dict["heigths"]
        # assert len(widths) > 0 and len(heigths) > 0
        # x, y = vars_dict["x"], vars_dict["y"]
        # assert len(x) > 0 and len(y) > 0
        # min_makespan, max_makespan = vars_dict["min_makespan"], vars_dict["max_makespan"]
        # assert min_makespan is not None and max_makespan is not None

        min_makespan = self.variables["min_makespan"]
        max_makespan = self.variables["max_makespan"]

        #

        for clause in self._constraints():
            self.solver.add(clause)

        if symmetry:
            for clause in self._symmetries_breaking():
                self.solver.add(clause)

        #

        target_makespan = min_makespan  ### use target_makespan to iterate during optimization

        check = z3.unsat
        t0 = time.time()
        time_spent = 0
        done = False
        ###  to solve case: optimal_makespan == max_makespan for binary search
        # if search == 'binary': max_makespan += 1

        while (not done) and (time_spent < 300):
            t1 = time.time()

            print('target makespan:', target_makespan)
            print('done:', done)

            self.solver.push()
            self.solver.set('timeout', int(self.solver_timeout-time_spent) * 1000)

            for clause in self._dynamic_constraints(target_makespan):
                self.solver.add(clause)

            if symmetry:
                for clause in self._dynamic_symmetries_breaking(target_makespan):
                    self.solver.add(clause)

            check = self.solver.check()

            # solution = {}
            # makespan = 0
            if check == z3.sat:
                print("SAT")
                print("makespan =", target_makespan)
                model = self.solver.model()

                solution = self._evaluate_solution(model, min_makespan, max_makespan, target_makespan)
                solutions_dict["all_solutions"].append(solution)
                # print(
                #     f"target_makespan = {target_makespan}  min_makespan = {min_makespan}  makespan = {makespan}"
                # )
                solutions_dict["stats"] = self.solver.statistics()
                done, min_makespan, max_makespan, target_makespan = self._get_target_makespan(
                    min_m = min_makespan, 
                    max_m = max_makespan, 
                    target_m = target_makespan, 
                    sat = True, 
                    search = search
                )
            else:
                print("unsat")
                done, min_makespan, max_makespan, target_makespan = self._get_target_makespan(
                    min_m = min_makespan, 
                    max_m = max_makespan, 
                    target_m = target_makespan, 
                    sat = False, 
                    search = search
                )
            self.solver.pop()
            print(round(time.time() - t1))
            time_spent = time.time() - t0
            ### it is possible to decrease max_makespan at pace > 1 and when unsat try the skipped values
            ### or implement binary search...

        print(f"TOTAL TIME = {round(time.time() - t0, 2)}")
        print("")

        solutions_dict["TOTAL_TIME"] = time_spent
        solutions_dict["all_solutions"] = solutions_dict["all_solutions"][::-1]
        if solutions_dict["all_solutions"]:
            solutions_dict["solution"] = solutions_dict["all_solutions"][0]
        return solutions_dict
