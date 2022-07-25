from importlib import import_module

from SMT.utils.args import parse_args
from SMT.utils.storage import SMT_data_file_url
from SMT.utils.plots import plot_solutions_v2

import json
import os

###

MODELS_MODULE_NAMESPACE = "SMT.models"

###


def main(args):
    # mi dice quale tra i file .py in models usare (ogni file contine un modello diverso)

    # open file
    SMT_file_url = SMT_data_file_url(args.data, "txt")
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
        plot_solutions_v2(solutions_dict)

    filename = os.path.join('SMT', 'out', args.model)
    if args.symmetry:
        filename = os.path.join(filename, 'symmetry')
    if not os.path.exists(filename):
        os.makedirs(filename)
    filename = os.path.join(filename, solutions_dict['file'] + '.json')
    output_string = json.dumps(
        {
            'file': solutions_dict['file'],
            'TOTAL_TIME': solutions_dict['TOTAL_TIME']
        }
    )
    #if not os.path.exists(filename):
    #    os.makedirs(filename)
    with open(filename, 'w', encoding="utf-8") as file:
        file.write(output_string)


###

if __name__ == '__main__':
    main(parse_args())