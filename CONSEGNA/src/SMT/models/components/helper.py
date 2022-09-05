from platform import node
import numpy as np

###

# def compute_max_makespan(heights, widths, width, with_rotation=False) -> int:
#     n_cols = width // max(widths)
#     col_h = [0 for _ in range(n_cols)]
#     for h in heights:
#         col_h[np.argmin(col_h)] += h
#     if with_rotation:
#         max_makespan = min(
#             sum(
#                 [
#                     min(widths[c], heights[c]) if heights[c] < width else heights[c]
#                     for c in range(len(heights))
#                 ]
#             ), max(col_h)
#         )
#     else:
#         max_makespan = max(col_h)
#     return max_makespan

###


class Node:

    def __init__(self, c_index, w, h, parent, x=0, y=0):
        self.c_index = c_index
        self.w = w
        self.h = h
        self.x = x
        self.y = y
        self.parent = parent
        self.children_list = []

    def get_remaining_width(self):
        return self.w - sum([self.children_list[i].w for i in range(len(self.children_list))])

    def get_altitude(self):
        return self.y + self.h

    def attach_child(self, child):
        child.y = self.y + self.h
        child.x = self.x + self.w - self.get_remaining_width()
        child.parent = self
        self.children_list.append(child)

    def __str__(self):
        if self.parent:
            p_index = self.parent.c_index
        else:
            p_index = None
        return f"Node {self.c_index}, w = {self.w}, h = {self.h}, parent = {p_index}, rw = {self.get_remaining_width()}, x={self.x}, y={self.y}"


def compute_max_makespan(heights, widths, width, with_rotation=False):
    CIRCUITS = range(len(widths))
    list_of_nodes = [Node(c, widths[c], heights[c], None) for c in CIRCUITS]
    list_of_nodes = sorted(list_of_nodes, key=lambda a: a.w, reverse=True)

    root = Node(-1, width, 0, None)
    attached = [root]

    for c in CIRCUITS:
        fringe = [
            attached[i] for i in range(len(attached))
            if attached[i].get_remaining_width() >= list_of_nodes[c].w
        ]
        fringe = sorted(fringe, key=lambda b: b.get_altitude())

        fringe[0].attach_child(list_of_nodes[c])
        attached.append(list_of_nodes[c])

    #        print([fringe[k].c_index for k in range(len(fringe))])
    #        print([str(attached[k]) for k in range(len(attached))])

    makespan = max([list_of_nodes[c].get_altitude() for c in CIRCUITS])

    list_of_nodes = sorted(list_of_nodes, key=lambda n: n.c_index)

    default_solution = {
        "width": width,
        "n_circuits": len(widths),
        "widths": widths,
        "heights": heights,
        "x": [node.x for node in list_of_nodes],
        "y": [node.y for node in list_of_nodes],
        "min_makespan": 0,
        "max_makespan": makespan,
        "makespan": makespan
    }

    return default_solution
