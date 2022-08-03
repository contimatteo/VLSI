import os
import copy
import json
import numpy as np

from dotenv import load_dotenv

from CP.utils import parse_args
from CP.utils import convert_txt_file_to_dzn, convert_raw_result_to_solutions_dict
# from CP.utils import plot_solutions_v2
# from CP.utils import CP_model_file_url, CP_data_file_url, CP_out_file_url

from utils import CPStorage, plot_solutions

###

np.random.seed(1)
load_dotenv()

DATA_FILE_NAME = "ab-test-6"
MODEL_FILE_NAME = "v6"
SOLVER_FILE_NAME = "gecode"  # chuffed

N_MAX_SOLUTIONS = 9

###


def __minizinc_exec_cmd(os_cmd: str) -> str:
    return os.popen(os_cmd).read()


def __convert_raw_results_to_dict(raw_results: dict, args) -> dict:
    solutions_dict = convert_raw_result_to_solutions_dict(
        raw_results, min(args.sol, N_MAX_SOLUTIONS)
    )

    solutions_dict["solver"] = args.solver
    solutions_dict["model"] = args.model
    solutions_dict["data"] = args.data

    return solutions_dict


def __store_solutions_dict(solutions_dict: dict) -> None:

    def __file_url():
        file_sub_dir = str(solutions_dict["solver"]).lower() + "/" + solutions_dict["model"]
        return str(CPStorage.out_file_url(solutions_dict["data"], file_sub_dir).resolve())

    def __clean_dict(obj):
        obj_copy = copy.deepcopy(obj)
        del obj_copy["all_solutions"]
        return obj_copy

    def __format_dict(obj):
        int_list_to_str = lambda l: ','.join(str(v) for v in l)
        obj_copy = copy.deepcopy(obj)
        obj_copy["solution"]['x'] = int_list_to_str(obj_copy["solution"]['x'])
        obj_copy["solution"]['y'] = int_list_to_str(obj_copy["solution"]['y'])
        obj_copy["solution"]['widths'] = int_list_to_str(obj_copy["solution"]['widths'])
        obj_copy["solution"]['heights'] = int_list_to_str(obj_copy["solution"]['heights'])
        return obj_copy

    json_data = copy.deepcopy(solutions_dict)
    json_data = __clean_dict(json_data)
    json_data = __format_dict(json_data)

    with open(__file_url(), 'w', encoding="utf-8") as file:
        json.dump(json_data, file, indent=2)

    return json_data


def __plot(solutions_dict):
    plot_solutions(solutions_dict)


###


def main(args):
    solver = args.solver

    # _model_name = f"{args.model}.{str(args.solver).lower()}"
    _model_name = f"{args.model}"
    model = CPStorage.model_file_url(_model_name).resolve()

    convert_txt_file_to_dzn(args.data, args.model)
    data = CPStorage.data_file_url(args.data, 'dzn').resolve()

    #

    # opts = f"--time-limit {args.time * 1000}"  # --solver-time-limit
    opts = f"--time-limit {args.time * 1000} --random-seed 666"

    if args.sol > 1:
        opts += " --all-solutions"
    if args.stats is True:
        opts += " --output-detailed-timing"
        opts += " --output-time"
        opts += " --statistics "
        opts += " --solver-statistics"
        opts += " --verbose-solving"

    #

    os_cmd = f"minizinc {opts.strip()} --solver \"{solver}\" {model} {data}"

    if args.debug is True:
        print("\n", os_cmd, "\n")

    ### exec minizinc model
    raw_results = __minizinc_exec_cmd(os_cmd)

    if args.verbose == 2:
        print("\n", raw_results, "\n")

    ### parse raw results
    solutions_dict = __convert_raw_results_to_dict(raw_results, args)

    ### save parsed solutions to disk
    out_file_content = __store_solutions_dict(solutions_dict)

    #

    if args.verbose == 1:
        print("\n", json.dumps(out_file_content, indent=2), "\n")

    if args.plot is True:
        __plot(solutions_dict)


###

if __name__ == '__main__':
    main(parse_args())
