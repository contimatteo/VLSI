import numpy as np
import json

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

    data_dict['width'] = int(txt_lines[0][:-1])

    data_dict['n_circuits'] = int(txt_lines[1][:-1])

    data_dict['dims'] = []
    for line_idx in range(2, len(txt_lines)):
        x, y = txt_lines[line_idx][:-1].split(sep=' ')
        data_dict['dims'].append((int(x), int(y)))

    #

    dzn_lines[0] = f"width = {str(data_dict['width'])};\n"

    dzn_lines[1] = f"n_circuits = {str(data_dict['n_circuits'])};\n"

    dzn_lines[2] = 'dims = ['
    for dim in sorted(data_dict['dims'], key=lambda dim: dim[0] * dim[1], reverse=True):
        # for dim in data_dict['dims']:
        dzn_lines[line_idx] += f"|{dim[0]},{dim[1]},\n"
    dzn_lines[-1] = dzn_lines[-1][:-1]  ### remove last comma
    dzn_lines[-1] += '|]'  ### close the array

    #

    with open(dzn_file_url, 'w', encoding="utf-8") as f:
        f.writelines(dzn_lines)
        f.close()

    assert dzn_file_url.exists() and dzn_file_url.is_file()

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


def __convert_raw_var_to_bool(raw_var: str):
    return str(raw_var).lower() == "true"


def __convert_raw_var_to_list(raw_var: str, is_num: bool):
    raw_var = raw_var.strip()
    assert isinstance(raw_var, str) and len(raw_var) > 0

    # list
    if raw_var[0] == "[":
        raw_var = raw_var.replace("[", "").replace("]", "").replace(" ", "")
        raw_var = raw_var.split(",")
        return [
            __convert_raw_var_to_number(val) if is_num else __convert_raw_var_to_bool(val)
            for val in raw_var
        ]

    raise Exception("raw variable format not supported.")


def __convert_raw_var_to_special_type(raw_var_name: str, raw_var_value: str):
    raw_var = raw_var_value.strip()
    assert isinstance(raw_var, str) and len(raw_var) > 0

    # 2x2 matrix
    if raw_var_name == "pos" or raw_var_name == "dims":
        raw_var = __convert_raw_var_to_list(raw_var, True)
        return np.array(raw_var, dtype=np.int64).reshape((-1, 2)).tolist()
    elif raw_var_name == "is_rotated":
        raw_var = __convert_raw_var_to_list(raw_var, False)
        return [str(raw_bool_var).lower() == "true" for raw_bool_var in raw_var]

    raise Exception("raw variable format not supported.")


def convert_raw_result_to_solutions_dict(raw_results: str, n_max_solutions: int) -> dict:
    results = []
    best_result_index = None
    best_makespan_found = None

    #

    NUMERIC_VARIABLE_NAMES = ["width", "n_circuits", "makespan"]
    LIST_VARIABLE_NAMES = ["widths", "heights", "x", "y"]
    SPECIAL_VARIABLE_NAMES = ["dims", "pos", "is_rotated"]

    #

    raw_results = raw_results.replace("%%%mzn-stat-end", "", 3)
    raw_solutions = raw_results.split("%%%mzn-stat-end")
    # raw_solutions = raw_results.split("----------")

    for (si, raw_solution) in enumerate(raw_solutions):
        result = {"stats": {}}
        raw_variables = raw_solution.split("\n")

        if len(raw_variables) < 1:
            continue

        for (_, raw_variable) in enumerate(raw_variables):
            raw_variable = raw_variable.strip()

            if raw_variable.startswith("% time elapsed: "):
                var_value = raw_variable.replace("% time elapsed: ", "").replace(" s", "").strip()
                result["stats"]["TOTAL_TIME_ELAPSED"] = float(var_value)
                continue

            if len(raw_variable) < 1 or "===" in raw_variable:
                continue
            if raw_variable.startswith("% ") or raw_variable.startswith("%%%mzn-stat-end"):
                continue

            if raw_variable.startswith("%%%mzn-stat"):
                tmp_value = (raw_variable.replace("%%%mzn-stat: ", "")).split("=")
                var_name, var_value = tmp_value[0], tmp_value[1]
                if var_name not in ["method"]:
                    var_value = float(var_value) if '.' in var_value else int(var_value)
                    result["stats"][var_name] = var_value
                continue

            if len(raw_variable.split(" = ")) < 2:
                continue

            var_name = raw_variable.split(" = ")[0]
            var_value = raw_variable.split(" = ")[1]

            if var_name in NUMERIC_VARIABLE_NAMES:
                var_value = __convert_raw_var_to_number(var_value)
            elif var_name in LIST_VARIABLE_NAMES:
                var_value = __convert_raw_var_to_list(var_value, True)
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
        "best_makespan": best_makespan_found,
        "solution": results[best_result_index],
    }
