from pathlib import Path

###

ROOT_SRC = Path(__file__).parent.parent.parent

ROOT_CP = ROOT_SRC.joinpath("CP")

###


def CP_data_dir() -> Path:
    return ROOT_CP.joinpath("data")


def CP_models_dir() -> Path:
    return ROOT_CP.joinpath("models")


def CP_solvers_dir() -> Path:
    return ROOT_CP.joinpath("solvers")


###


def CP_solver_file_url(file_name: str) -> Path:
    assert isinstance(file_name, str)

    return CP_solvers_dir().joinpath(f"{file_name}.mzn")


def CP_model_file_url(file_name: str) -> Path:
    assert isinstance(file_name, str)

    return CP_models_dir().joinpath(f"{file_name}.mzn")


def CP_data_file_url(file_name: str, file_type: str) -> Path:
    assert isinstance(file_name, str)
    assert isinstance(file_type, str)
    assert file_type == 'txt' or file_type == 'dzn'

    return CP_data_dir().joinpath(f"input/{file_type}/{file_name}.{file_type}")
