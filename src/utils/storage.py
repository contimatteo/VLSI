from pathlib import Path

###

ROOT_SRC = Path(__file__).parent.parent


class _Storage:

    @property
    def _root_dir_name(self) -> str:
        raise NotImplementedError

    #

    @property
    def _root_dir(self) -> Path:
        return ROOT_SRC.joinpath(self._root_dir_name)

    def data_dir(self) -> Path:
        return ROOT_SRC.joinpath("data")

    def models_dir(self) -> Path:
        return self._root_dir.joinpath("models")

    def solvers_dir(self) -> Path:
        return self._root_dir.joinpath("solvers")

    def out_dir(self) -> Path:
        return self.data_dir().joinpath("output/json")

    #

    def data_file_url(self, file_name: str, file_type: str) -> Path:
        assert isinstance(file_name, str)
        assert isinstance(file_type, str)
        assert file_type == 'txt' or file_type == 'dzn'

        return self.data_dir().joinpath(f"input/{file_type}/{file_name}.{file_type}")

    def out_file_url(self, file_name: str, sub_dir: str = None) -> Path:
        assert isinstance(file_name, str)
        assert sub_dir is None or isinstance(sub_dir, str)

        partial_file_url = f"{self._root_dir_name}"
        partial_file_url += f"/{sub_dir}/" if sub_dir is not None else ""

        self.out_dir().joinpath(partial_file_url).mkdir(exist_ok=True, parents=True)

        return self.out_dir().joinpath(f"{partial_file_url}{file_name}.json")


###


class CPStorageClass(_Storage):

    @property
    def _root_dir_name(self) -> str:
        return "CP"

    def model_file_url(self, file_name: str) -> Path:
        assert isinstance(file_name, str)
        return self.models_dir().joinpath(f"{file_name}.mzn")


class SATStorageClass(_Storage):

    @property
    def _root_dir_name(self) -> str:
        return "SAT"


class SMTStorageClass(_Storage):

    @property
    def _root_dir_name(self) -> str:
        return "SMT"


###

CPStorage = CPStorageClass()

SATStorage = SATStorageClass()

SMTStorage = SATStorageClass()
