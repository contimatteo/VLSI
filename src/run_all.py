import argparse
from email.policy import default
import itertools
import os
import progressbar
from math import prod
import time

import CP.utils.args as CP_args
import SAT.utils.args as SAT_args
import SMT.utils.args as SMT_args
import ILP.utils.args as ILP_args

STRATEGY_CHOICES = ['all', 'CP', 'SAT', 'SMT', 'ILP']
DEFAULT_STRATEGY = 'all'

STRATEGY_ARGS = {
    'CP': {
        'model': CP_args.MODELS_CHOICES,
        'solver': CP_args.SOLVERS_CHOICES
    },
    'SAT': {
        'model': SAT_args.MODELS_CHOICES,
        'search': SAT_args.SEARCH_CHOICES,
        'symmetry': [True, False],
        'cumulative': [True, False]
    },
    'SMT': {
        'model': SMT_args.MODELS_CHOICES,
        'search': SMT_args.SEARCH_CHOICES,
        'symmetry': [True, False],
        'cumulative': [True, False]
    },
    'ILP': {
        'model': ILP_args.MODELS_CHOICES,
        'search': ILP_args.SEARCH_CHOICES,
        'symmetry': [False],
        'cumulative': [False]
    },
}

def parse_args():
    parser = argparse.ArgumentParser(description = 'solver for VLSI problem.')

    ###  to select between CP, SAT, SMT, ILP or run all strategies
    parser.add_argument(
        '--strategy', 
        required = False,
        type = str,
        default = DEFAULT_STRATEGY,
        choices = STRATEGY_CHOICES,
        help = 'name of the strategy to use'
    )

    return parser.parse_args()

###

def main(args):

    ###  initialize list of strategies to run
    if args.strategy == 'all':
        strategies = STRATEGY_CHOICES[1:]
    else:
        strategies = [args.strategy]


    script_default_str = 'python src/'

    for strategy in strategies:
        ###  list of all argument dictionaries for the specific strategy
        arg_lists = list(STRATEGY_ARGS[strategy].values())

        print(f'Running {strategy} models...')
        ###  adding progress bar
        bar = progressbar.ProgressBar(
            maxval = prod([len(arg_list) for arg_list in arg_lists]+[40]),
            widgets = [
                progressbar.Bar('=', '[', ']'), 
                ' ', progressbar.Percentage(), ' '
                ' [', progressbar.ETA(), ']'
            ]
        )
        bar.start()
        bar_counter = 0

        ###  iterate over the instances
        for i in range(40):
            ###  iterate over all possible arguments combination
            for arg_vals in itertools.product(*arg_lists):
                script_str = script_default_str + strategy + '.py --verbose 0' + f' --data "ins-{40-i}"' # 40-i to have pessimistic time left

                ###  argument counter
                a = 0

                for arg_name in STRATEGY_ARGS[strategy].keys():
                    ###  if args_val[a] is bool and is true, add "--{arg_name}" to the script
                    if isinstance(arg_vals[a], bool):
                        if arg_vals[a]:
                            script_str += f' --{arg_name}'
                    else:
                        script_str += f' --{arg_name} {arg_vals[a]}'
                    a += 1
                    
                ###  update progress bar 
                bar_counter += 1
                bar.update(bar_counter)
                
                try:
                    # print(script_str)
                    os.system(script_str)
                ###  KeyboardInterrupt used if no solution is given, just pass to the next instance
                except KeyboardInterrupt:
                    pass

        bar.finish()

###

if __name__ == '__main__':
    main(parse_args())