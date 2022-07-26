import math

import cplex

from ILP.models.__default import cplexModel as cplexDefaultModel
from ILP.models.components.helper import compute_max_makespan
from ILP.models.components.foundation import diffn_helper, diffn_or_helper

class cplexModel(cplexDefaultModel):

    def _variables(self, raw_data: dict) -> dict:
        width, n_circuits, CIRCUITS, widths, heights = self.__variables_support(raw_data)

        ### define makespan boundaries
        _c_area_sum = sum([heights[c] * widths[c] for c in CIRCUITS])
        min_makespan = max(math.ceil(_c_area_sum / width), max(heights))
        max_makespan = compute_max_makespan(heights, widths, width)

        ### + max(widths) is necessary for summing the width later
        _x_domain_max = width - min(widths) + max(widths)
        ### + max(heights) is necessary for summing the height later
        _y_domain_max = max_makespan - min(heights) + max(heights)

        x = [f"x_{c}" for c in CIRCUITS]
        print("x variables = ", x)
        y = [f"y_{c}" for c in CIRCUITS]
        print("y variables = ", y)
        d = []
        for c1 in CIRCUITS:
            for c2 in range(c1+1, n_circuits):
                d += [f"d_{c1}_{c2}_{i}" for i in range(4)]
        print("d variables = ", d)
        names = x + y + d

        ### all circuits must have each dimension greater than zero
        assert min(heights) > 0 and min(widths) > 0
        assert len(heights) == len(widths) == n_circuits

        VARS_TO_RETURN = [
            "width", "n_circuits", "CIRCUITS", "widths", "heights", 
            "x", "y", "d", "names",
            "min_makespan", "max_makespan", "_x_domain_max",  "_y_domain_max"
        ]

        _local_vars = locals()

        return {var_name: _local_vars[var_name] for var_name in VARS_TO_RETURN}

    def __coefficient_objective(self, raw_data) -> None:
        var = self._variables(raw_data)

        CIRCUITS = var['CIRCUITS']
        x = var["x"]
        y = var["y"]
        d = var["d"]
        width = var["width"]
        max_makespan = var["max_makespan"]
        widths = var["widths"]
        heights = var["heights"]
        n_circuits = var["n_circuits"]
        CIRCUITS = var["CIRCUITS"]

        ### OBJECTIVE COEFFICIENTS
        ### coefficients 0 foreach value of x and y and coefficient 1 to makespan
        # NB: all coefficients must be float 
        objective = [0.0 for _ in CIRCUITS] + [1.0 for _ in CIRCUITS] + [0.0 for _ in range(len(d))]

        print()
        print()
        print('objective = ', objective)


        ### VARIABLES LOWER BOUNDS
        ### 0 foreach value of x and y and min_makespan for makespan
        lb = [0.0 for _ in CIRCUITS] + [0.0 for _ in CIRCUITS] + [0.0 for _ in range(len(d))]
        print()
        print('lb = ', lb)
        ### VARIABLES UPPER BOUNDS
        ### 0 foreach value of x and y and min_makespan for makespan
        ub = [float(width) for _ in CIRCUITS] + [float(max_makespan) for _ in CIRCUITS] + [1.0 for _ in range(len(d))]
        print()
        print('ub = ', ub)

        ### add the objective function
        self.solver.variables.add(obj=objective,
                                  lb=lb,
                                  ub=ub,
                                  names=var['names'])
    
    def _addConstraints(self) -> None:
        var = self.variables

        x = var["x"]
        y = var["y"]
        d = var["d"]
        width = var["width"]
        widths = var["widths"]
        heights = var["heights"]
        n_circuits = var["n_circuits"]
        CIRCUITS = var["CIRCUITS"]
        variables = [i for i in range(n_circuits*2+len(d))]
        print()
        print('num of variables =', len(variables))

        print()
        print('### CONSTRAINTS ###')


        ### WIDTHS CONSTRAINTS
        ### x[c] <= width - widths[c]
        ### in total n_circuits constraints
        constraints = []
        rhs = []
        constraint_names = []
        constraint_sensens = ["L" for c in CIRCUITS]
        for c in CIRCUITS:
            ### variables: x + y + d
            constraint_names.append(f"widths_cnst_{c}" )
            constraints.append([variables, 
                               [1.0 if i == c else 0.0 for i in CIRCUITS] + [0.0 for _ in CIRCUITS] + \
                               [0.0 for _ in range(len(d))]])
            rhs.append(width - widths[c])
            print()
            print(f'({constraint_names[-1]})', constraints[-1][1], '<=', rhs[-1])

        self.solver.linear_constraints.add(lin_expr = constraints,
                                           senses = constraint_sensens,
                                           rhs = rhs,
                                           names = constraint_names)

        ### DIFFN
        ### ref[https://sofdem.github.io/gccat/gccat/Cdiffn.html]
        ### Then the 𝚍𝚒𝚏𝚏𝚗 constraint holds if the volume of the union is
        ### equal to the sum of the volumes of the different boxes.
        ### [x[c1] - x[c2] + d_c1_c2_a <= 1 - widths[c1],
        ###  y[c1] - y[c2] + d_c1_c2_b <= 1 - heights[c1],
        ###  x[c2] - x[c1] + d_c1_c2_c <= 1 - widths[c2],
        ###  y[c2] - y[c1] + d_c1_c2_d <= 1 - heights[c2],
        ###  d_c1_c2_a + d_c1_c2_b + d_c1_c2_c + d_c1_c2_d >= 1]
        ### in total n_circuits * (n_circuits - 1) * 5 constraints
        constraints = []
        rhs = []
        constraint_names = []
        constraint_sensens = []

        for c1 in CIRCUITS:
            for c2 in range(c1+1, n_circuits):

                cnst_a, rhs_a = diffn_helper(c1, c2, 0, widths[c1], CIRCUITS, n_circuits, axis=0)
                constraints.append([variables, cnst_a])
                rhs.append(rhs_a)
                constraint_names.append(f"diffn_{c1}_{c2}_{1}")
                constraint_sensens.append('L')
                print()
                print(f'({constraint_names[-1]})', constraints[-1][1], '<=', rhs[-1])

                cnst_b, rhs_b = diffn_helper(c1, c2, 1, heights[c1], CIRCUITS, n_circuits, axis=1)
                constraints.append([variables, cnst_b])
                rhs.append(rhs_b)
                constraint_names.append(f"diffn_{c1}_{c2}_{2}")
                constraint_sensens.append('L')
                print()
                print(f'({constraint_names[-1]})', constraints[-1][1], '<=', rhs[-1])

                cnst_c, rhs_c = diffn_helper(c2, c1, 2, widths[c2], CIRCUITS, n_circuits, axis=0)
                constraints.append([variables, cnst_c])
                rhs.append(rhs_c)
                constraint_names.append(f"diffn_{c1}_{c2}_{3}")
                constraint_sensens.append('L')
                print()
                print(f'({constraint_names[-1]})', constraints[-1][1], '<=', rhs[-1])

                cnst_d, rhs_d = diffn_helper(c2, c1, 3, heights[c2], CIRCUITS, n_circuits, axis=1)
                constraints.append([variables, cnst_d])
                rhs.append(rhs_d)
                constraint_names.append(f"diffn_{c1}_{c2}_{4}")
                constraint_sensens.append('L')
                print()
                print(f'({constraint_names[-1]})', constraints[-1][1], '<=', rhs[-1])

                cnst_e, rhs_e = diffn_or_helper(c1, c2, CIRCUITS, n_circuits)
                rhs.append(rhs_e)
                constraints.append([variables, cnst_e])
                constraint_names.append(f"diffn_{c1}_{c2}_{5}")
                constraint_sensens.append('G')
                print()
                print(f'({constraint_names[-1]})', constraints[-1][1], '>=', rhs[-1])

        print(len(constraints), len(rhs), len(constraint_sensens), len(constraint_names))

        self.solver.linear_constraints.add(lin_expr = constraints,
                                           senses = constraint_sensens,
                                           rhs = rhs,
                                           names = constraint_names)

        ###
