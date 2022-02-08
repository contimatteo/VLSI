import colorsys
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import numpy as np

def plot_solution(sol, in_dict, tot_length):
    fig, ax = plt.subplots()
    plt.xticks(np.arange(0, in_dict['width']+1, 1))
    plt.yticks(np.arange(0, tot_length+1, 1))
    plt.grid(
        visible=True,
        which='both',
        axis='both',
        alpha=0.2
    )

    for plate_idx in range(in_dict['n_circuits']):
        r = Rectangle(
            xy = (sol[plate_idx][0], sol[plate_idx][1]),
            width = in_dict['dims'][plate_idx][0],
            height = in_dict['dims'][plate_idx][1],
            edgecolor = 'white',
            facecolor = tuple(np.random.choice(range(256), size=3)/255),
            fill = True,
            label = str(plate_idx)
        )
        ax.add_patch(r)

        # label rectangle
        ax.annotate(
            str(plate_idx+1),
            (r.get_x()+r.get_width()/2., r.get_y()+r.get_height()/2.),
            color = 'black',
            weight = 'bold',
            fontsize = 10,
            ha = 'center',
            va = 'center'
        )

    plt.show()