from importlib import import_module
import copy
import json

from SMT.utils import parse_args

from utils import SMTStorage, plot_solutions

###

MODELS_MODULE_NAMESPACE = "SMT.models"

###


def __store_solutions_dict(solutions_dict: dict, search_strategy: str) -> None:

    def __file_url(F_json = True):
        if F_json:
            file_sub_dir = solutions_dict["model"] + "/" + search_strategy.lower()
            return str(SMTStorage.json_file_url(solutions_dict["data_file"], file_sub_dir).resolve())
        else:
            file_sub_dir = solutions_dict["model"] + "/" + search_strategy.lower()
            return str(SMTStorage.out_file_url(solutions_dict["data_file"], file_sub_dir).resolve())

    def __clean_dict(obj):
        obj_copy = copy.deepcopy(obj)
        del obj_copy["all_solutions"]
        return obj_copy

    def __format_dict(obj):
        obj_copy = copy.deepcopy(obj)
        obj_copy["stats"] = {
            key: obj_copy["stats"].get_key_value(key)
            for key in obj_copy["stats"].keys()
        }
        return obj_copy

    json_data = copy.deepcopy(solutions_dict)
    json_data = __clean_dict(json_data)
    # json_data = __format_dict(json_data)

    with open(__file_url(), 'w', encoding="utf-8") as file:
        json.dump(json_data, file, indent=2)

    jsol = json_data['solution']
    lines = str(jsol['width']) + ' ' + str(jsol['makespan']) + '\n'
    lines += str(jsol['n_circuits']) + '\n'
    for i in range(jsol['n_circuits']):
        lines += str(jsol['widths'][i]) + ' ' + str(jsol['heights'][i]) + ' ' +\
                str(jsol['x'][i]) + ' ' + str(jsol['y'][i]) + '\n'
    with open(__file_url(F_json=False), 'w') as file:
        file.write(lines)
        file.close()

    return json_data


###


def main(args):
    # mi dice quale tra i file .py in models usare (ogni file contine un modello diverso)

    # open file
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

    solutions_dict = {}

    CURRENT_MODEL_MODULE = import_module(f"{MODELS_MODULE_NAMESPACE}.{args.model}")

    if args.model == "base" or args.model == "rotation":
        ModelClass = getattr(CURRENT_MODEL_MODULE, "Z3Model")
        model = ModelClass(timeout=args.time)
        model.initialize(data_dict)
        solutions_dict = model.solve(args.data, args.symmetry, args.cumulative)
    else:
        fn_model_solve = getattr(CURRENT_MODEL_MODULE, "solve")
        solutions_dict = fn_model_solve(data_dict)

    assert solutions_dict is not None and isinstance(solutions_dict, dict)

    # plot
    if args.plot:
        plot_solutions(solutions_dict)

    # save_results(args, 'SMT', solutions_dict)
    __store_solutions_dict(solutions_dict, args.search)


###

if __name__ == '__main__':
    main(parse_args())
