import subprocess
import os
import time
import pandas as pd

SOLVERS: list[str] = ["cvc5", "Z3", "Amaya", "Lash", "cvc5_automata"]
NUMBER_OF_RUNS: int = 3


def get_solver_bin_path(solver: str) -> str:
    path: str = "/home/lfrf/ufmg/poc2/"
    match solver:
        case "cvc5" | "cvc5_automata":
            path += "cvc5/build/bin/cvc5"
        case "Z3":
            path += "z3/build/z3"
        case "Amaya":
            path += "amaya/run-amaya.py"
        case "Lash":
            path += "lash/bin/presburger"
    return path


def run() -> None:
    df: pd.DataFrame = pd.DataFrame([], columns=["solver", "file", "time"])
    for solver in SOLVERS:
        TIME_LIMIT: float = 120 if solver in ["Amaya", "Lash", "cvc5_automata"] else 20
        print(solver)
        bin_path: str = get_solver_bin_path(solver)
        args: list[str] = []
        args.append(bin_path)
        if solver == "Amaya":
            args = ["python3"] + args
            args.append("get-sat")
        if solver == "cvc5_automata":
            args.append("--automata")
        dir: str = (
            "/home/lfrf/ufmg/poc2/cvc5/lia_tests/frobenius/"
            if solver != "Lash"
            else "/home/lfrf/ufmg/poc2/amaya/benchmarks/formulae/frobenius/lash/"
        )
        for f in os.listdir(dir):
            index: str = f[4 : (f.find("."))]
            if int(index[index.find("_") + 1 :]) > 200:
                continue
            if int(index[index.find("_") + 1 :]) > 4 and solver in ["cvc5"]:
                print(index)
                df = df._append(
                    {"solver": solver, "file": index, "time": TIME_LIMIT},
                    ignore_index=True,
                )
                continue
            if int(index[index.find("_") + 1 :]) > 15 and solver in ["Z3"]:
                print(index)
                df = df._append(
                    {"solver": solver, "file": index, "time": TIME_LIMIT},
                    ignore_index=True,
                )
                continue
            args.append(dir + f)
            total_time: float = 0
            print(args)
            for i in range(NUMBER_OF_RUNS):
                print(i)
                start_time: float = time.perf_counter()
                try:
                    _ = subprocess.run(
                        args, capture_output=True, text=True, timeout=TIME_LIMIT
                    ).stdout
                    total_time += time.perf_counter() - start_time
                except subprocess.TimeoutExpired:
                    total_time += TIME_LIMIT
            total_time /= NUMBER_OF_RUNS
            df = df._append(
                {"solver": solver, "file": index, "time": total_time}, ignore_index=True
            )
            args.pop()
    df.to_csv("output.csv")


if __name__ == "__main__":
    run()
