import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt


# Normalize the result by the baseline
def normalize_results(group):
    baseline_value = group.loc[group["run"] == "baseline", "result"].values[0]
    group["result"] = group["result"] / baseline_value
    return group


if __name__ == "__main__":
    df = pd.read_csv("results.csv")
    # group by "benchmark", normalize the "result" column by the value of
    # "result" for the "baseline" "run".
    # df["result_norm"] = df.groupby("benchmark").apply(foo).values
    # df["result_norm"] = grouped.transform(lambda x: breakpoint())["result"]

    # Apply the normalization
    df = df.groupby("benchmark").apply(normalize_results).reset_index(drop=True)

    # plot grouped bar chart: each group corresponds to a benchmark, and bars
    # within each group are different "run" values. Y axis is "result".

    from statistics import geometric_mean

    giga = df[df.run == "giga"].result
    giga = geometric_mean(giga)
    vdce = df[df.run == "valnum-dce"].result
    vdce = geometric_mean(vdce)

    print(f"Giga: {giga} ({1 / giga} x)")
    print(f"Valnum-DCE: {vdce} ({1 / vdce} x)")

    # set up the matplotlib figure
    sns.set(style="whitegrid")
    f, ax = plt.subplots()
    f.set_size_inches(8, 8)

    # plot grouped bar chart
    sns.barplot(x="benchmark", y="result", hue="run", data=df, ax=ax)

    ax.set_ylabel("Instruction count relative to baseline (lower is better)")
    ax.set_xlabel("Benchmark")

    # x tick rotation
    plt.xticks(rotation=90)

    # make the plot more readable
    plt.legend(title="Run", loc="upper left")
    plt.tight_layout()

    # save the figure
    plt.savefig("plot.png", bbox_inches="tight", dpi=300)
