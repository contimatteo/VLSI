from importlib import import_module
import copy
import json

from SMT.utils import parse_args

from utils import SMTStorage, plot_solutions

###

MODELS_MODULE_NAMESPACE = "SMT.models"

###


def __store_solutions_dict(solutions_dict: dict) -> None:
    model = solutions_dict["model"]
    search = solutions_dict["search"]
    symmetry = solutions_dict["symmetry"]
    data_file = solutions_dict["data_file"]
    cumulative = solutions_dict["cumulative"]

    def __file_url():
        file_sub_dir = model + "/" + search.lower()
        file_sub_dir += ".symmetry" if symmetry is True else ""
        file_sub_dir += ".cumulative" if cumulative is True else ""
        return str(SMTStorage.out_file_url(data_file, file_sub_dir).resolve())

    def __clean_dict(obj):
        obj_copy = copy.deepcopy(obj)
        del obj_copy["all_solutions"]
        return obj_copy

    json_data = copy.deepcopy(solutions_dict)
    json_data = __clean_dict(json_data)

    with open(__file_url(), 'w', encoding="utf-8") as file:
        json.dump(json_data, file, indent=2)

    return json_data


###


def main(args):
    ### open file
    SMT_file_url = SMTStorage.data_file_url(args.data, "txt")
    with open(SMT_file_url, encoding="utf-8") as f:
        txt_lines = f.readlines()
        f.close()

    data_dict = {
        "data": args.data,
        'width': int(txt_lines[0][:-1]),
        'n_circuits': int(txt_lines[1][:-1]),
        'dims': []
    }
    for line_idx in range(2, len(txt_lines)):
        x, y = txt_lines[line_idx][:-1].split(sep=' ')
        data_dict['dims'].append((int(x), int(y)))

    ### solve

    solutions_dict = {}

    CURRENT_MODEL_MODULE = import_module(f"{MODELS_MODULE_NAMESPACE}.{args.model}")
    ModelClass = getattr(CURRENT_MODEL_MODULE, "Z3Model")

    model = ModelClass(timeout=args.time)
    model.initialize(data_dict)
    solutions_dict = model.solve(args.data, args.symmetry, args.cumulative)

    assert solutions_dict is not None and isinstance(solutions_dict, dict)

    ### plot

    if args.plot:
        plot_solutions(solutions_dict)

    __store_solutions_dict(solutions_dict)


###

if __name__ == '__main__':
    main(parse_args())
