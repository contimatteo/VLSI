import minizinc

from pathlib import Path
from txt_to_dzn import txt_to_dzn
from plot_solution import plot_solution


###


ROOT_CP = Path(__file__).parent

DIR_DATA = ROOT_CP.joinpath("data")
DIR_MODELS = ROOT_CP.joinpath("models")
DIR_SOLVERS = ROOT_CP.joinpath("solvers")

FILE_DATA_URL = DIR_DATA.joinpath("input/txt/ins-5.txt")
FILE_MODEL_URL = DIR_MODELS.joinpath("v2.mzn")
FILE_SOLVER_URL = DIR_SOLVERS.joinpath("geocode.mpc")


###


def load_model():
    return minizinc.Model(str(FILE_MODEL_URL))


def load_data(model):
    FILE_DATA_URL_DZN, in_dict = txt_to_dzn(FILE_DATA_URL)
    model.add_file(str(FILE_DATA_URL_DZN))
    return in_dict


def load_solver():
    return minizinc.Solver.lookup("gecode")
    # return minizinc.Solver.lookup(str(FILE_SOLVER_URL))


def create_instance(solver, model):
    return minizinc.Instance(solver, model)


def solve(instance, all_solutions=False):
    return instance.solve(all_solutions=all_solutions)


###


def main():
    model = load_model()
    solver = load_solver()
    
    in_dict = load_data(model)

    instance = create_instance(solver, model)

    results = solve(instance)

    for i in range(len(results)):
        print(results)
        plot_solution(results["pos"], in_dict, results["objective"])



###

if __name__ == '__main__':
    main()
