import minizinc

from CP.utils import plot_solution, convert_txt_file_to_dzn
from CP.utils import CP_model_file_url, CP_data_file_url

###

DATA_FILE_NAME = "ins-3"
MODEL_FILE_NAME = "v2"
SOLVER_FILE_NAME = "gecode"

###


def load_model(file_name: str) -> minizinc.Model:
    return minizinc.Model(str(CP_model_file_url(file_name)))


def load_data(file_name: str, model: minizinc.Model) -> dict:
    in_dict = convert_txt_file_to_dzn(DATA_FILE_NAME)

    model.add_file(str(CP_data_file_url(file_name, "dzn")))

    return in_dict


def load_solver(file_name: str):
    assert isinstance(file_name, str)
    return minizinc.Solver.lookup(file_name)


def instantiate(solver: minizinc.Solver, model: minizinc.Model) -> minizinc.Instance:
    return minizinc.Instance(solver, model)


def solve(instance: minizinc.Instance, all_solutions=False) -> minizinc.Result:
    return instance.solve(all_solutions=all_solutions)


###


def main():
    model = load_model(MODEL_FILE_NAME)
    solver = load_solver(SOLVER_FILE_NAME)
    in_dict = load_data(DATA_FILE_NAME, model)

    #

    ### parse_solution instance
    instance = instantiate(solver, model)
    ### solve
    results = solve(instance)

    #

    for _ in range(len(results)):
        print(results)
        plot_solution(results["pos"], in_dict, results["objective"])


###

if __name__ == '__main__':
    main()
