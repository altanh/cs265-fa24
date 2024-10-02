import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt

if __name__ == "__main__":
    df = pd.read_csv("results.csv")
    # group by "benchmark", normalize the "result" column by the value of
    # "result" for the "baseline" "run".
    df["result"] = (
        df.groupby("benchmark")
        .apply(lambda x: x["result"] / x[x["run"] == "baseline"]["result"].values[0])
        .values
    )

    # plot grouped bar chart: each group corresponds to a benchmark, and bars
    # within each group are different "run" values. Y axis is "result".

    # set up the matplotlib figure
    sns.set(style="whitegrid")
    f, ax = plt.subplots()

    # plot grouped bar chart
    sns.barplot(x="benchmark", y="result", hue="run", data=df, ax=ax)

    ax.set_ylabel("Performance relative to baseline")
    ax.set_xlabel("Benchmark")

    # x tick rotation
    plt.xticks(rotation=90)

    # make the plot more readable
    plt.legend(title="Run", loc="lower right")
    plt.tight_layout()

    # save the figure
    plt.savefig("plot.png", bbox_inches="tight", dpi=300)
