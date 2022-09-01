import os
import glob
import pandas as pd
from tqdm import tqdm

out_folders = [
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "chuffed",
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep +
    # "chuffed",
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "rotation.search" + os.sep +
    # "chuffed",
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "search" + os.sep +
    # "chuffed",
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "search.symmetry" + os.sep +
    # "chuffed",
    # "src" + os.sep + "CP" + os.sep + "out" + os.sep + "json" + os.sep + "symmetry" + os.sep +
    # "chuffed",

    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "binary",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "binary.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "binary.symmetry",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "binary.symmetry.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "linear",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "linear.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "linear.symmetry",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "linear.symmetry.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "binary",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "binary.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "binary.symmetry",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "binary.symmetry.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "linear",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "linear.cumulative",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "linear.symmetry",
    "src" + os.sep + "SAT" + os.sep + "out" + os.sep + "json" + os.sep + "rotation" + os.sep + "linear.symmetry.cumulative",

    # "src" + os.sep + "ILP" + os.sep + "out" + os.sep + "json" + os.sep + "base",
    # "src" + os.sep + "SMT" + os.sep + "out" + os.sep + "json" + os.sep + "base" + os.sep + "linear"
]

for folder in tqdm(out_folders):
    frame = pd.DataFrame(dtype=object)
    csv_name = "CSV" + os.sep + folder.replace(os.sep, "_") + ".csv"

    for f in glob.glob(folder + os.sep + "*.json"):
        s = pd.read_json(f, typ="series")
        frame = pd.concat([frame, s], axis="columns")

    frame = frame.transpose()
    frame.set_index(keys="data_file", inplace=True)
    frame = frame.sort_index()
    # print(frame)
    frame.to_csv(csv_name)