import matplotlib.pyplot as plt
import numpy as np

from matplotlib.patches import Rectangle

###


def plot_solutions(solutions_dict: dict) -> None:
    assert isinstance(solutions_dict, dict)

    solutions = solutions_dict["all_solutions"]
    assert isinstance(solutions, list)

    if len(solutions) < 1:
        return

    rows = 3  # int(len(solutions) / 2)
    cols = 3  # len(solutions) / rows

    #

    if len(solutions) == 1:
        fig, axs = plt.subplots(1)
    else:
        fig, axs = plt.subplots(nrows=rows, ncols=cols)

    fig.canvas.set_window_title(solutions_dict["data"])

    def __single_solution_plot(ax, result):
        ax.set_xlim(0, result['width'])
        ax.set_ylim(0, result['makespan'])
        ax.set_xticks(np.arange(0, result['width'] + 1, 1))
        ax.set_yticks(np.arange(0, result["makespan"] + 1, 1))
        ax.grid(visible=True, which='both', axis='both', alpha=0.2)

        for c_idx in range(result['n_circuits']):
            if "is_rotated" not in result:
                result['is_rotated'] = [False for _ in result['heights']]

            x = result["x"][c_idx]
            y = result["y"][c_idx]
            is_rotated = result['is_rotated'][c_idx]
            w = result['widths'][c_idx] if not is_rotated else result['heights'][c_idx]
            h = result['heights'][c_idx] if not is_rotated else result['widths'][c_idx]

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

    if len(solutions) == 1:
        __single_solution_plot(axs, solutions[0])
    else:
        for r in range(rows):
            for c in range(cols):
                result_index_to_plot += 1
                if result_index_to_plot >= len(solutions):
                    continue

                __single_solution_plot(axs[r, c], solutions[result_index_to_plot])

    #

    plt.show()
