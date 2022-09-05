import numpy as np

###


def solutions_dict_to_txt_file(sol_dict: dict) -> str:
    jsol = sol_dict['solution']

    lines = str(jsol['width']) + ' ' + str(int(np.ceil(jsol['makespan']))) + '\n'
    lines += str(jsol['n_circuits']) + '\n'

    for i in range(jsol['n_circuits']):
        lines += str(jsol['widths'][i]) + ' ' + str(jsol['heights'][i]) + ' ' +\
                str(int(np.ceil(jsol['x'][i]))) + ' ' + str(int(np.ceil(jsol['y'][i]))) + '\n'

    return lines
