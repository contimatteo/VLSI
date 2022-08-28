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
        return Path(__file__).parent.parent

    def json_out_dir(self, technology: str) -> Path:
        return self.root_dir.joinpath("json").joinpath(technology)

    @property
    def csv_result_file(self) -> Path:
        return self.root_dir.joinpath("results.csv")


###

StorageUtils = StorageUtilsClass()
