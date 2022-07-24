import argparse

from .storage import SAT_data_file_url

###

VERBOSE_CHOICES = [0, 1, 2]

DEFAULT_SECONDS_TIME_LIMIT = 300
DEFAULT_N_SOLUTIONS = 1
DEFAULT_VERBOSE = 1
DEFAULT_MODEL_NAME = "base.py"
MODELS_CHOICES = [
    # "base", "rotation", "rotation.search", "rotation.search.symmetry", "search", "search.symmetry"
    "base",
    "base_decimal_encoding_diffn",
    "rotation"
]
DEFAULT_SEARCH_STRATEGY = 'linear'
SEARCH_CHOICES = [
    'linear',
    'binary'
]

###


def parse_args():
    parser = argparse.ArgumentParser(description='SAT solver of VLSI problem.')

    parser.add_argument('--data', required=True, type=str, help='name of txt data file')
    parser.add_argument(
        '--model',
        required=False,
        type=str,
        default=DEFAULT_MODEL_NAME,
        choices=MODELS_CHOICES,
        help='name of the model to use'
    )
    # parser.add_argument(
    #     '--solver',
    #     required=False,
    #     type=str,
    #     default=DEFAULT_SOLVER_NAME,
    #     choices=SOLVERS_CHOICES,
    #     help='name of the solver to use'
    # )
    parser.add_argument(
        '--sol', required=False, type=int, default=DEFAULT_N_SOLUTIONS, help='max no. of solutions'
    )
    parser.add_argument(
        '--verbose',
        required=False,
        type=int,
        default=DEFAULT_VERBOSE,
        choices=VERBOSE_CHOICES,
        help='print execution verbose infos'
    )
    parser.add_argument(
        '--plot', required=False, action="store_true", help='show final solutions plot'
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
        '--debug', required=False, action="store_true", help='prints development debug infos'
    )
    parser.add_argument(
        '--search', 
        required=False,
        type=str,
        default=DEFAULT_SEARCH_STRATEGY,
        choices=SEARCH_CHOICES,
        help='makespan search strategy'
    )
    parser.add_argument(
        '--symmetry', required=False, action="store_true", help='add symmetry constraints'
    )

    #

    args = parser.parse_args()

    if args.debug is True:
        print()
        print(args)
        print()

    #

    n_sol = args.sol
    time_limit = args.time
    data_file_name = args.data

    assert n_sol > 0 and n_sol <= 64

    # assert time_limit >= 100 and time_limit <= 60000
    assert time_limit >= 1 and time_limit <= 1800

    assert SAT_data_file_url(data_file_name, "txt").is_file()

    #

    return args
