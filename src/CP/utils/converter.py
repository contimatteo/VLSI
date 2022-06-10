import numpy as np

from .storage import CP_data_file_url

###


def convert_txt_file_to_dzn(txt_file_name: str):
    assert isinstance(txt_file_name, str)

    txt_file_url = CP_data_file_url(txt_file_name, "txt")
    dzn_file_url = CP_data_file_url(txt_file_name, "dzn")

    assert txt_file_url.exists() and txt_file_url.is_file()

    #

    with open(txt_file_url, encoding="utf-8") as f:
        txt_lines = f.readlines()
        f.close()

    dzn_lines = ['' for _ in range(len(txt_lines))]
    data_dict = {}

    #

    # print and save width
    width = txt_lines[0][:-1]
    dzn_lines[0] = 'width = ' + width + ';\n'
    data_dict['width'] = int(width)

    # print and save n_plates
    n_plates = txt_lines[1][:-1]
    dzn_lines[1] = 'n_circuits = ' + n_plates + ';\n'
    data_dict['n_circuits'] = int(n_plates)

    # print and save dims
    data_dict['dims'] = []
    dzn_lines[2] = 'dims = ['
    for line_idx in range(2, len(txt_lines)):
        x, y = txt_lines[line_idx][:-1].split(sep=' ')
        dzn_lines[line_idx] += '|' + x + ', ' + y + ',\n'
        data_dict['dims'].append((int(x), int(y)))

    # remove last comma
    dzn_lines[-1] = dzn_lines[-1][:-1]

    # close the array
    dzn_lines[-1] += '|]'

    #

    with open(dzn_file_url, 'w', encoding="utf-8") as f:
        f.writelines(dzn_lines)
        f.close()

    #

    assert txt_file_url.exists() and txt_file_url.is_file()

    return data_dict


###


def __convert_raw_var_to_number(raw_var: str):
    raw_var = raw_var.strip()
    assert isinstance(raw_var, str) and len(raw_var) > 0

    # number
    try:
        raw_var = float(raw_var)
        return int(raw_var) if raw_var.is_integer() else raw_var
    except ValueError:
        pass

    raise Exception("raw variable format not supported.")


def __convert_raw_var_to_list(raw_var: str):
    raw_var = raw_var.strip()
    assert isinstance(raw_var, str) and len(raw_var) > 0

    # list
    if raw_var[0] == "[":
        raw_var = raw_var.replace("[", "").replace("]", "").replace(" ", "")
        raw_var = raw_var.split(",")
        return [__convert_raw_var_to_number(val) for val in raw_var]

    raise Exception("raw variable format not supported.")


def __convert_raw_var_to_special_type(raw_var_name: str, raw_var_value: str):
    raw_var = raw_var_value.strip()
    assert isinstance(raw_var, str) and len(raw_var) > 0

    # 2x2 matrix
    if raw_var_name == "pos" or raw_var_name == "dims":
        raw_var = __convert_raw_var_to_list(raw_var)
        return np.array(raw_var, dtype=np.int64).reshape((-1, 2)).tolist()

    raise Exception("raw variable format not supported.")


def convert_raw_result_to_solutions_dict(raw_results: str, n_max_solutions: int) -> dict:
    results = []
    best_result_index = None
    best_makespan_found = None

    #

    NUMERIC_VARIABLE_NAMES = ["width", "n_circuits", "makespan"]
    LIST_VARIABLE_NAMES = ["widths", "heights", "x", "y"]
    SPECIAL_VARIABLE_NAMES = ["dims", "pos"]

    #

    raw_solutions = raw_results.split("----------")

    for (si, raw_solution) in enumerate(raw_solutions):
        result = {}
        raw_variables = raw_solution.split("\n")

        if len(raw_variables) < 1:
            continue

        for (_, raw_variable) in enumerate(raw_variables):
            raw_variable = raw_variable.strip()

            if len(raw_variable) < 1 or "===" in raw_variable:
                continue
            if raw_variable.startswith("%%%mzn-stat") or raw_variable.startswith("% "):
                continue

            var_name = raw_variable.split(" = ")[0]
            var_value = raw_variable.split(" = ")[1]

            if var_name in NUMERIC_VARIABLE_NAMES:
                var_value = __convert_raw_var_to_number(var_value)
            elif var_name in LIST_VARIABLE_NAMES:
                var_value = __convert_raw_var_to_list(var_value)
            elif var_name in SPECIAL_VARIABLE_NAMES:
                var_value = __convert_raw_var_to_special_type(var_name, var_value)
            else:
                continue
                # raise Exception(f"`{var_name}` not recognized.")

            if var_name == "makespan":
                if best_makespan_found is None or var_value < best_makespan_found:
                    best_result_index = si
                    best_makespan_found = var_value

            result[var_name] = var_value

        if len(result.keys()) > 0:
            results.append(result)

    #

    results = sorted(results, key=lambda x: x["makespan"], reverse=False)
    results = results[0:n_max_solutions]

    return {
        "results": results,
        "best_result_index": best_result_index,
        "best_makespan": best_makespan_found
    }
