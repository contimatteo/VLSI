from pathlib import Path

###

ROOT_SRC = Path(__file__).parent.parent.parent

ROOT_ILP = ROOT_SRC.joinpath("ILP")

###


def ILP_data_dir() -> Path:
    return ROOT_ILP.joinpath("data")


def ILP_models_dir() -> Path:
    return ROOT_ILP.joinpath("models")


def ILP_out_dir() -> Path:
    return ROOT_ILP.joinpath("out")


###


def ILP_model_file_url(file_name: str) -> Path:
    assert isinstance(file_name, str)

    return ILP_models_dir().joinpath(f"{file_name}.mzn")


def ILP_data_file_url(file_name: str, file_type: str) -> Path:
    assert isinstance(file_name, str)
    assert isinstance(file_type, str)
    assert file_type == 'txt'

    return ILP_data_dir().joinpath(f"input/{file_type}/{file_name}.{file_type}")


def ILP_out_file_url(file_name: str, sub_dir: str = None) -> Path:
    assert isinstance(file_name, str)
    assert sub_dir is None or isinstance(sub_dir, str)

    partial_file_url = f"{sub_dir}/" if sub_dir is not None else ""
    ILP_out_dir().joinpath(partial_file_url).mkdir(exist_ok=True, parents=True)

    return ILP_out_dir().joinpath(f"{partial_file_url}{file_name}.json")
