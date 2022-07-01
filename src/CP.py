import os
import numpy as np
import json

from CP.utils import parse_args
from CP.utils import convert_txt_file_to_dzn, convert_raw_result_to_solutions_dict
from CP.utils import plot_solutions_v2
from CP.utils import CP_model_file_url, CP_data_file_url, CP_out_file_url

###

np.random.seed(1)

DATA_FILE_NAME = "ab-test-6"
MODEL_FILE_NAME = "v6"
SOLVER_FILE_NAME = "gecode"  # chuffed

N_MAX_SOLUTIONS = 9

###


def __minizinc_exec_cmd(os_cmd: str) -> str:
    return os.popen(os_cmd).read()


def __convert_raw_results_to_dict(raw_results: dict, args) -> dict:
    solutions_dict = convert_raw_result_to_solutions_dict(raw_results, N_MAX_SOLUTIONS)

    solutions_dict["solver"] = args.solver
    solutions_dict["model"] = args.model
    solutions_dict["data"] = args.data

    return solutions_dict


def __store_solutions_dict(solutions_dict: dict) -> None:
    sub_dir = str(solutions_dict["solver"]).lower() + "/" + solutions_dict["model"]
    file_name = solutions_dict["data"]
    file_url = str(CP_out_file_url(file_name, sub_dir).resolve())

    with open(file_url, 'w', encoding="utf-8") as file:
        json.dump(solutions_dict, file, indent=2)


def __plot(solutions_dict):
    plot_solutions_v2(solutions_dict)


###


def main(args):
    solver = args.solver

    _model_name = f"{args.model}.{str(args.solver).lower()}"
    model = CP_model_file_url(_model_name).resolve()

    convert_txt_file_to_dzn(args.data)
    data = CP_data_file_url(args.data, 'dzn').resolve()

    #

    opts = f"--time-limit {args.time * 1000}"  # --solver-time-limit

    if args.solutions > 1:
        opts += " --all-solutions"
    if args.stats is True:
        opts += " --statistics --output-time"
    if args.verbose == 1:
        opts += " --output-detailed-timing"

    #

    os_cmd = f"minizinc {opts.strip()} --solver \"{solver}\" {model} {data}"

    if args.debug is True:
        print("\n", os_cmd, "\n")

    ### exec minizinc model
    raw_results = __minizinc_exec_cmd(os_cmd)

    ### parse raw results
    solutions_dict = __convert_raw_results_to_dict(raw_results, args)

    ### save parsed solutions to disk
    __store_solutions_dict(solutions_dict)

    #

    if args.output is not None:
        if args.output == "raw" or args.output == "raw+plot":
            print("\n", raw_results, "\n")

        if args.output == "plot" or args.output == "raw+plot":
            __plot(solutions_dict)


###

if __name__ == '__main__':
    main(parse_args())
