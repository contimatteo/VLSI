from typing import List

import pandas as pd

###


class CsvGenerator():

    def __init__(self, solved_max_time: float = 300.0) -> None:
        self._solved_max_time = solved_max_time

        self._CP_results: List[dict] = []
        self._SAT_results: List[dict] = []
        self._SMT_results: List[dict] = []
        self._ILP_results: List[dict] = []

    #

    def CP_json_injection(self, json_data: List[dict]) -> None:
        for data in json_data:
            self._CP_results.append(
                pd.Series(
                    {
                        "technology": "CP",
                        "data_name": data["data_file"],
                        "data_index": data["data_file"].replace("ins-", ""),
                        "stats_tot_time": data["TOTAL_TIME"],
                        "stats_solved": data["TOTAL_TIME"] < self._solved_max_time,
                        "solver": data["solver"],
                        "model": data["model"],
                        "symmetry": "symmetry" in data["model"],
                        "cumulative": None,
                        "search": None,
                    }
                )
            )

    def SAT_json_injection(self, json_data: List[dict]) -> None:
        for data in json_data:
            self._SAT_results.append(
                pd.Series(
                    {
                        "technology": "SAT",
                        "data_name": data["data_file"],
                        "data_index": data["data_file"].replace("ins-", ""),
                        "stats_tot_time": data["TOTAL_TIME"],
                        "stats_solved": data["TOTAL_TIME"] < self._solved_max_time,
                        "solver": None,
                        "model": data["model"],
                        "symmetry": data["symmetry"],
                        "cumulative": data["cumulative"],
                        "search": data["search"],
                    }
                )
            )

    def SMT_json_injection(self, json_data: List[dict]) -> None:
        for data in json_data:
            self._SMT_results.append(
                pd.Series(
                    {
                        "technology": "SMT",
                        "data_name": data["data_file"],
                        "data_index": data["data_file"].replace("ins-", ""),
                        "stats_tot_time": data["TOTAL_TIME"],
                        "stats_solved": data["TOTAL_TIME"] < self._solved_max_time,
                        "solver": None,
                        "model": data["model"],
                        "symmetry": data["symmetry"],
                        "cumulative": data["cumulative"],
                        "search": data["search"],
                    }
                )
            )

    def ILP_json_injection(self, json_data: List[dict]) -> None:
        pass

    #

    def to_dataframe(self) -> pd.DataFrame:
        columns_and_types = {
            'technology': str,
            'data_name': str,
            'data_index': int,
            'stats_tot_time': float,
            'stats_solved': bool,
            'solver': str,
            'model': str,
            'symmetry': bool,
            'cumulative': bool,
            'search': str,
        }

        df_data = []
        df_data += self._CP_results
        df_data += self._SAT_results
        df_data += self._SMT_results
        df_data += self._ILP_results

        df = pd.DataFrame(df_data, columns=list(columns_and_types.keys()))
        df = df.astype(dtype=columns_and_types)

        return df
