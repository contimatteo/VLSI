import os
import minizinc
import numpy as np

from CP.utils import parse_args
from CP.utils import convert_txt_file_to_dzn, convert_raw_result_to_solutions_dict
from CP.utils import plot_solutions_v1, plot_solutions_v2
from CP.utils import CP_model_file_url, CP_data_file_url

###

np.random.seed(1)

DATA_FILE_NAME = "ab-test-6"
MODEL_FILE_NAME = "v6"
SOLVER_FILE_NAME = "gecode"  # chuffed

N_MAX_SOLUTIONS = 9

###

# def load_model(file_name: str) -> minizinc.Model:
#     return minizinc.Model(str(CP_model_file_url(file_name)))

# def load_data(file_name: str, model: minizinc.Model) -> dict:
#     in_dict = convert_txt_file_to_dzn(DATA_FILE_NAME)

#     model.add_file(str(CP_data_file_url(file_name, "dzn")))

#     return in_dict

# def load_solver(file_name: str):
#     assert isinstance(file_name, str)
#     return minizinc.Solver.lookup(file_name)

# def instantiate(solver: minizinc.Solver, model: minizinc.Model) -> minizinc.Instance:
#     return minizinc.Instance(solver, model)

# def solve(instance: minizinc.Instance, all_solutions=False) -> minizinc.Result:
#     return instance.solve(all_solutions=all_solutions)

# def main(all_solutions=False):
#     model = load_model(MODEL_FILE_NAME)
#     solver = load_solver(SOLVER_FILE_NAME)
#     in_dict = load_data(DATA_FILE_NAME, model)
#     ### parse_solution instance
#     instance = instantiate(solver, model)
#     ### solve
#     results = solve(instance, all_solutions)
#     for _ in range(len(results)):
#         print(results)
#         plot_solutions_v1(results["pos"], in_dict, results["objective"])

###


def __plot(raw_results):
    solutions_dict = convert_raw_result_to_solutions_dict(raw_results, N_MAX_SOLUTIONS)

    plot_solutions_v2(solutions_dict)


def main(args):
    convert_txt_file_to_dzn(args.data)

    solver = args.solver
    model = CP_model_file_url(args.model).resolve()
    data = CP_data_file_url(args.data, 'dzn').resolve()

    #

    opts = f"--time-limit {args.time}"  # --solver-time-limit

    if args.solutions > 1:
        opts += " --all-solutions"

    if args.stats is True:
        opts += " --statistics --output-time"

    if args.verbose == 1:
        opts += " --output-detailed-timing"

    #

    os_cmd = f"minizinc --solver {solver} --model {model} --data {data} {opts.strip()}"

    if args.debug is True:
        print()
        print(os_cmd)
        print()

    raw_results = os.popen(os_cmd).read()

    #

    if args.output == "raw" or args.output == "raw+plot":
        print()
        print(raw_results)
        print()

    if args.output == "plot" or args.output == "raw+plot":
        __plot(raw_results)


###

if __name__ == '__main__':
    main(parse_args())
