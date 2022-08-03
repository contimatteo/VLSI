import os
import json


def save_results(args, strategy: str, solutions_dict):

    ###  define filename
    idx = os.getcwd().find('src')
    filename = os.getcwd()[:os.getcwd().find('src')] if idx != -1 else os.getcwd()
    filename = os.path.join(filename, 'src', strategy, 'out', args.model, args.search)
    if args.symmetry:
        filename = os.path.join(filename, 'symmetry')
    if args.cumulative:
        filename = os.path.join(filename, 'cumulative')

    ###  create folder
    if not os.path.exists(filename):
        os.makedirs(filename)
    filename = os.path.join(filename, solutions_dict['data_file'] + '.json')

    ###  create dictionary to be written
    output_dict = solutions_dict['solution']
    output_dict.update(
        {
            'file': solutions_dict['data_file'],
            'TOTAL_TIME': solutions_dict['TOTAL_TIME']
        }
    )
    output_string = json.dumps(output_dict)

    with open(filename, 'w', encoding="utf-8") as file:
        file.write(output_string)
