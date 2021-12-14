import minizinc

###


def load_model():
    return minizinc.Model("./model.v2.mzn")


def load_data(model):
    model.add_file("./data/input/ins-1.dzn")


def load_solver():
    return minizinc.Solver.lookup("gecode")


def create_instance(solver, model):
    return minizinc.Instance(solver, model)


def solve(instance, all_solutions=False):
    return instance.solve(all_solutions=all_solutions)


###


def main():
    model = load_model()
    load_data(model)

    solver = load_solver()
    instance = create_instance(solver, model)

    results = solve(instance)

    for i in range(len(results)):
        print(results)


###

if __name__ == '__main__':
    main()
