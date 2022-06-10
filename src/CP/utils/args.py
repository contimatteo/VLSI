import argparse

from .storage import CP_data_file_url

###

MODELS_CHOICES = ["base", "base.rotation"]
SOLVERS_CHOICES = [
    "Chuffed",
    "COIN-BC",
    "CPLEX",
    "findMUS",
    "Gecode",
    "Gecode Gist",
    "Globalizer",
    "Gurobi",
    "SCIP",
    "Xpress",
]
OUTPUT_CHOICES = ["raw", "plot", "raw+plot"]

DEFAULT_SECONDS_TIME_LIMIT = 10
DEFAULT_MODEL_NAME = "base"
DEFAULT_SOLVER_NAME = "Chuffed"
DEFAULT_N_SOLUTIONS = 12
DEFAULT_OUTPUT_FORMAT = "raw+plot"

###


def parse_args():
    parser = argparse.ArgumentParser(description='CP solver of VLSI problem.')

    parser.add_argument('--data', required=True, type=str, help='name of txt data file')
    parser.add_argument(
        '--model',
        required=False,
        type=str,
        default=DEFAULT_MODEL_NAME,
        choices=MODELS_CHOICES,
        help='name of the model to use'
    )
    parser.add_argument(
        '--solver',
        required=False,
        type=str,
        default=DEFAULT_SOLVER_NAME,
        choices=SOLVERS_CHOICES,
        help='name of the solver to use'
    )
    parser.add_argument(
        '--solutions',
        required=False,
        type=int,
        default=DEFAULT_N_SOLUTIONS,
        help='max no. of solutions'
    )
    parser.add_argument(
        '--output',
        required=False,
        type=str,
        default=DEFAULT_OUTPUT_FORMAT,
        choices=OUTPUT_CHOICES,
        help='output format'
    )

    parser.add_argument(
        '--time',
        required=False,
        type=int,
        default=DEFAULT_SECONDS_TIME_LIMIT,
        help='computation (seconds) time limit'
    )
    parser.add_argument(
        '--stats', required=False, action="store_false", help='prints execution statistics infos'
    )
    parser.add_argument(
        '--verbose',
        required=False,
        type=int,
        default=0,
        choices=[0, 1],
        help='print execution verbose infos'
    )
    parser.add_argument(
        '--debug', required=False, action="store_true", help='prints development debug infos'
    )

    #

    args = parser.parse_args()

    if args.debug is True:
        print()
        print(args)
        print()

    #

    n_sol = args.solutions
    time_limit = args.time
    data_file_name = args.data

    assert n_sol > 0 and n_sol <= 64

    # assert time_limit >= 100 and time_limit <= 60000
    assert time_limit >= 1 and time_limit <= 300

    assert CP_data_file_url(data_file_name, "txt").is_file()

    #

    return args
