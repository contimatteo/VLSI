import os

from pathlib import Path

###


class StorageUtilsClass():

    @staticmethod
    def is_empty(directory: Path) -> bool:
        # return any(Path(directory).iterdir())
        return len(os.listdir(str(directory))) < 1

    #

    @property
    def root_dir(self) -> Path:
        return Path(__file__).parent.parent.parent.parent

    #

    @property
    def notebooks_dir(self) -> Path:
        return self.root_dir.joinpath("notebooks")

    @property
    def notebooks_csv_dir(self) -> Path:
        return self.notebooks_dir.joinpath("csv_generator")

    @property
    def notebooks_csv_result_file(self) -> Path:
        return self.notebooks_csv_dir.joinpath("results.csv")

    #

    @property
    def src_dir(self) -> Path:
        return self.root_dir.joinpath("src")

    def src_out_dir(self, technology: str) -> Path:
        assert isinstance(technology, str)
        assert technology in ["CP", "SAT", "SMT", "ILP"]

        return self.src_dir.joinpath(technology).joinpath("out").joinpath("json")


###

StorageUtils = StorageUtilsClass()
