import json
import os

from pathlib import Path

from helpers import CsvGenerator
from helpers import StorageUtils

###

DEBUG = False

###


def __valid_dir_guard(dir_url: Path) -> None:
    assert dir_url.exists()
    assert dir_url.is_dir()
    assert not StorageUtils.is_empty(dir_url)


def __valid_file_guard(file_url: Path) -> None:
    assert file_url.exists()
    assert file_url.is_file()


def __load_json_file(file_url: Path) -> dict:
    data = None
    with open(str(file_url), 'r', encoding="utf-8") as f:
        data = json.load(f)
    assert isinstance(data, dict)
    return data


###


def csv_load_and_inject_json_recursively(csv: CsvGenerator, technology: str) -> None:
    base_dir_url = StorageUtils.src_out_dir(technology)

    __valid_dir_guard(base_dir_url)

    # DEBUG and print("\n")

    for model_dir in os.scandir(base_dir_url):
        model_dir = Path(model_dir)
        # DEBUG and print(f"[{technology}] model = {model_dir.name}")

        __valid_dir_guard(model_dir)

        for search_or_solver_dir in os.scandir(model_dir):
            search_or_solver_dir = Path(search_or_solver_dir)
            # DEBUG and print(f"[{technology}] search/solver = {search_or_solver_dir.name}")

            __valid_dir_guard(search_or_solver_dir)

            json_files_content = []
            for json_file in os.scandir(search_or_solver_dir):
                json_file = Path(json_file)
                __valid_file_guard(json_file)
                json_files_content.append(__load_json_file(json_file))

            if technology == "CP":
                csv.CP_json_injection(json_files_content)
            elif technology == "SAT":
                csv.SAT_json_injection(json_files_content)
            elif technology == "SMT":
                csv.SMT_json_injection(json_files_content)
            elif technology == "ILP":
                csv.ILP_json_injection(json_files_content)
            else:
                pass

    # DEBUG and print("\n")


def main():
    csv = CsvGenerator()

    csv_load_and_inject_json_recursively(csv, "CP")
    csv_load_and_inject_json_recursively(csv, "SAT")
    csv_load_and_inject_json_recursively(csv, "SMT")

    df = csv.to_dataframe()

    DEBUG and print("\n\n")
    DEBUG and print(df.head(15))
    DEBUG and print("")
    DEBUG and print("shape \t\t ", df.shape)
    DEBUG and print(df.dtypes)
    DEBUG and print("\n\n")

    df.to_csv(StorageUtils.notebooks_csv_result_file, index=False)


###

if __name__ == "__main__":
    main()
