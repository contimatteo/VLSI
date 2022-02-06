from pathlib import Path

import minizinc

###

ROOT_CP = Path(__file__).parent

DIR_DATA = ROOT_CP.joinpath("data")
DIR_MODELS = ROOT_CP.joinpath("models")
DIR_SOLVERS = ROOT_CP.joinpath("solvers")

FILE_DATA_URL = DIR_DATA.joinpath("input/ins-1.dzn")
FILE_MODEL_URL = DIR_MODELS.joinpath("v2.mzn")
FILE_SOLVER_URL = DIR_SOLVERS.joinpath("geocode.mpc")

###


def load_model():
    return minizinc.Model(str(FILE_MODEL_URL))


def load_data(model):
    model.add_file(str(FILE_DATA_URL))


def load_solver():
    return minizinc.Solver.lookup("gecode")
    # return minizinc.Solver.lookup(str(FILE_SOLVER_URL))


def create_instance(solver, model):
    return minizinc.Instance(solver, model)


def solve(instance: minizinc.Instance, all_solutions=False):
    return instance.solve(all_solutions=all_solutions)


###


def main():
    model = load_model()
    solver = load_solver()

    load_data(model)

    ### parse_solution instance
    instance = create_instance(solver, model)
    ### solve
    results = solve(instance)

    for _ in range(len(results)):
        print("pos = ", results["pos"])


###

if __name__ == '__main__':
    main()
