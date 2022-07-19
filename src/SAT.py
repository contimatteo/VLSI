from SAT.models.base import solve
# from SAT.models.base_legacy import solve

from SAT.utils.args import parse_args
from SAT.utils.storage import SAT_data_file_url
from SAT.utils.plots import plot_solutions_v2


def main(args):
    # mi dice quale tra i file .py in models usare (ogni file contine un modello diverso)

    # open file
    sat_file_url = SAT_data_file_url(args.data, "txt")
    with open(sat_file_url, encoding="utf-8") as f:
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

    # lancia il python con dentro z3py
    _model_name = f"{args.model}"
    if _model_name == "base":
        solutions_dict = solve(data_dict)
    elif _model_name == "rotation":
        pass
    elif _model_name == "rotation.search":
        pass
    elif _model_name == "rotation.search.symmetry":
        pass
    elif _model_name == "symmetry":
        pass
    else:  # if _model_name == "search.symmetry"
        pass

    # plot
    if args.plot:
        plot_solutions_v2(solutions_dict)


###

if __name__ == '__main__':
    main(parse_args())
