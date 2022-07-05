import numpy as np
import json
import copy

from .storage import CP_data_file_url

###

NUMERIC_VARIABLE_NAMES = ["width", "n_circuits", "makespan", "min_makespan", "max_makespan"]
LIST_VARIABLE_NAMES = ["widths", "heights", "x", "y"]
SPECIAL_VARIABLE_NAMES = ["dims", "pos", "is_rotated"]

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


# def __convert_raw_result_to_solutions_dict__(raw_output: str, n_max_solutions: int) -> dict:
#     results = []
#     best_result_index = None
#     best_makespan_found = None
#     #
#     raw_output_split = raw_output.split("%%%mzn-stat-end")
#     raw_stats = raw_output_split[0] + "\n"
#     if "==========" in raw_output_split[1]:
#         raw_stats += raw_output_split[1].split("==========")[1]
#         raw_solutions = raw_output_split[1].split("==========")[0]
#         raw_solutions = raw_solutions.split("----------")
#     else:
#         raw_stats += raw_output_split[1].split("----------")[1]
#         raw_solutions = [raw_output_split[1].split("----------")[0]]
#     stats = {}
#     for (si, raw_stat) in enumerate(raw_stats.split("\n")):
#         if raw_stat.startswith("% ") or raw_stat.startswith("%%%mzn-stat-end"):
#             continue
#         if raw_stat.startswith("%%%mzn-stat"):
#             tmp_value = (raw_stat.replace("%%%mzn-stat: ", "")).split("=")
#             var_name, var_value = tmp_value[0], tmp_value[1]
#             if var_name not in ["method"]:
#                 var_value = float(var_value) if '.' in var_value else int(var_value)
#                 stats[var_name] = var_value
#             continue
#     stats["TOTAL_TIME"] = round(stats["initTime"] + stats["solveTime"] + stats["flatTime"], 2)
#     #
#     for (si, raw_solution) in enumerate(raw_solutions):
#         result = {"stats": copy.deepcopy(stats)}
#         raw_variables = raw_solution.split("\n")
#         if len(raw_variables) < 1:
#             continue
#         for (_, raw_variable) in enumerate(raw_variables):
#             raw_variable = raw_variable.strip()
#             if len(raw_variable) < 1 or "===" in raw_variable:
#                 continue
#             if len(raw_variable.split(" = ")) < 2:
#                 continue
#             var_name = raw_variable.split(" = ")[0]
#             var_value = raw_variable.split(" = ")[1]
#             if var_name in NUMERIC_VARIABLE_NAMES:
#                 var_value = __convert_raw_var_to_number(var_value)
#             elif var_name in LIST_VARIABLE_NAMES:
#                 var_value = __convert_raw_var_to_list(var_value, True)
#             elif var_name in SPECIAL_VARIABLE_NAMES:
#                 var_value = __convert_raw_var_to_special_type(var_name, var_value)
#             else:
#                 continue
#                 # raise Exception(f"`{var_name}` not recognized.")
#             if var_name == "makespan":
#                 if best_makespan_found is None or var_value < best_makespan_found:
#                     best_result_index = si
#                     best_makespan_found = var_value
#             result[var_name] = var_value
#         if len(result.keys()) > 1:
#             results.append(result)
#     #
#     results = sorted(results, key=lambda sol: sol["makespan"], reverse=False)
#     results = results[0:n_max_solutions]
#     return {
#         "results": results,
#         "best_result_index": best_result_index,
#         "best_makespan": best_makespan_found,
#         "solution": results[best_result_index],
#     }

###


def __parse_raw_stats(raw_stat: str):
    stat_splits = (raw_stat.replace("%%%mzn-stat: ", "")).split("=")
    var_name, var_value = stat_splits[0], stat_splits[1]
    return var_name, float(var_value) if '.' in var_value else int(var_value)


def __parse_raw_time_elasped(raw_stat: str):
    var_value = (raw_stat.replace("% time elapsed: ", "")).replace(" s", "")
    return "TOTAL_TIME", float(var_value)


def convert_raw_result_to_solutions_dict(raw_output: str, n_max_solutions: int) -> dict:
    raw_output_lines = raw_output.split("\n")

    stats = {}
    results = []
    current_result = None

    #

    for raw_line in raw_output_lines:
        raw_line = raw_line.strip()

        if len(raw_line) < 1:
            continue
        if raw_line.startswith("% Generated FlatZinc statistics:"):
            continue
        if raw_line.startswith("%%%mzn-stat-end"):
            continue
        if raw_line.startswith("%%%mzn-stat: method="):
            continue
        if raw_line.startswith("---") or raw_line.startswith("==="):
            continue

        if raw_line.startswith("% time elapsed:"):
            stat_name, stat_value = __parse_raw_time_elasped(raw_line)
            stats[stat_name] = max(
                stats[stat_name], stat_value
            ) if stat_name in stats else stat_value
            continue

        if raw_line.startswith("%%%mzn-stat:"):
            stat_name, stat_value = __parse_raw_stats(raw_line)
            stats[stat_name] = stat_value
            continue

        if " = " not in raw_line:
            continue
            # raise Exception(raw_line)

        raw_line_splits = raw_line.split(" = ")
        var_name, var_value = raw_line_splits[0], raw_line_splits[1]

        if var_name in NUMERIC_VARIABLE_NAMES:
            var_value = __convert_raw_var_to_number(var_value)
        elif var_name in LIST_VARIABLE_NAMES:
            var_value = __convert_raw_var_to_list(var_value, True)
        elif var_name in SPECIAL_VARIABLE_NAMES:
            var_value = __convert_raw_var_to_special_type(var_name, var_value)
        else:
            continue
            # raise Exception(f"`{var_name}` not recognized.")

        if var_name == "width":
            current_result = {}

        current_result[var_name] = var_value

        if var_name == "makespan":
            if len(current_result.keys()) > 0:
                results.append(copy.deepcopy(current_result))
            current_result = None

    #

    assert len(results) > 0

    if len(results) > 1:
        results = sorted(results, key=lambda sol: sol["makespan"], reverse=False)
        results = results[0:n_max_solutions]

    return {
        "all_solutions": results,
        "solution": results[0],
        "stats": stats,
    }
