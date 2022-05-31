import matplotlib.pyplot as plt
import numpy as np

from matplotlib.patches import Rectangle

###


def plot_solutions_v1(sol, in_dict, tot_length):
    fig, ax = plt.subplots()
    plt.xticks(np.arange(0, in_dict['width'] + 1, 1))
    plt.yticks(np.arange(0, tot_length + 1, 1))
    plt.grid(visible=True, which='both', axis='both', alpha=0.2)

    for plate_idx in range(in_dict['n_circuits']):
        r = Rectangle(
            xy=(sol[plate_idx][0], sol[plate_idx][1]),
            height=in_dict['dims'][plate_idx][0],
            width=in_dict['dims'][plate_idx][1],
            edgecolor='white',
            facecolor=tuple(np.random.choice(range(256), size=3) / 255),
            fill=True,
            label=str(plate_idx)
        )
        ax.add_patch(r)

        # label rectangle
        ax.annotate(
            str(plate_idx + 1), (r.get_x() + r.get_width() / 2., r.get_y() + r.get_height() / 2.),
            color='black',
            weight='bold',
            fontsize=10,
            ha='center',
            va='center'
        )

    plt.show()


###


def plot_solutions_v2(solutions_dict):
    results = solutions_dict["results"]
    best_result_index = solutions_dict["best_result_index"]

    if len(results) < 1:
        return

    rows = 3  # int(len(results) / 2)
    cols = 4  # len(results) / rows

    #

    if len(results) == 1:
        fig, axs = plt.subplots(1)
    else:
        fig, axs = plt.subplots(nrows=rows, ncols=cols)

    def __single_solution_plot(ax, result):
        ax.set_xlim(0, result['width'])
        ax.set_ylim(0, result['makespan'])
        ax.set_xticks(np.arange(0, result['width'] + 1, 1))
        ax.set_yticks(np.arange(0, result["makespan"] + 1, 1))
        ax.grid(visible=True, which='both', axis='both', alpha=0.2)

        for c_idx in range(result['n_circuits']):
            x = result["x"][c_idx]
            y = result["y"][c_idx]
            w = result['widths'][c_idx]
            h = result['heights'][c_idx]

            r = Rectangle(
                xy=(x, y),
                height=h,
                width=w,
                edgecolor='white',
                facecolor=tuple(np.random.choice(range(256), size=3) / 255),
                fill=True,
                label=str(c_idx)
            )

            ax.add_patch(r)
            ax.annotate(
                str(c_idx + 1), (r.get_x() + r.get_width() / 2., r.get_y() + r.get_height() / 2.),
                color='black',
                weight='bold',
                fontsize=10,
                ha='center',
                va='center'
            )

    #

    result_index_to_plot = -1

    if len(results) == 1:
        __single_solution_plot(axs, results[0])
    else:
        for r in range(rows):
            for c in range(cols):
                result_index_to_plot += 1
                if result_index_to_plot >= len(results):
                    continue

                __single_solution_plot(axs[r, c], results[result_index_to_plot])

    #

    plt.show()
