import numpy as np

### TODO: This is the same file of SAT/components/helper.py, use only one single helper forall?

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

    def __init__(self, c_index, w, h, parent):
        self.c_index = c_index
        self.w = w
        self.h = h
        self.parent = parent
        self.children_list = []
        self.parent_altitude = 0

    def get_remaining_width(self):
        return self.w - sum([self.children_list[i].w for i in range(len(self.children_list))])

    def get_altitude(self):
        return self.h + self.parent_altitude

    def attach_child(self, child):
        self.children_list.append(child)
        child.parent = self
        child.parent_altitude = self.h + self.parent_altitude

    def __str__(self):
        if self.parent:
            p_index = self.parent.c_index
        else:
            p_index = None
        return f"Node {self.c_index}, w = {self.w}, h = {self.h}, parent = {p_index}, rw = {self.get_remaining_width()}"


def compute_max_makespan(heights, widths, width, with_rotation=False):
    list_of_nodes = [Node(i, widths[i], heights[i], None) for i in range(len(widths))]
    list_of_nodes = sorted(list_of_nodes, key=lambda a: a.w, reverse=True)

    root = Node(-1, width, 0, None)
    attached = [root]

    for i in range(len(list_of_nodes)):
        fringe = [
            attached[j] for j in range(len(attached))
            if attached[j].get_remaining_width() >= list_of_nodes[i].w
        ]
        fringe = sorted(fringe, key=lambda b: b.get_altitude())

        fringe[0].attach_child(list_of_nodes[i])
        attached.append(list_of_nodes[i])

    #        print([fringe[k].c_index for k in range(len(fringe))])
    #        print([str(attached[k]) for k in range(len(attached))])

    return max([list_of_nodes[k].get_altitude() for k in range(len(list_of_nodes))])
