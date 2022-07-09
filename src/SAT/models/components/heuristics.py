import numpy as np

def compute_max_makespan(heights, widths, width, with_rotation=False) -> int:
    n_cols = width // max(widths)
    col_h = [0 for _ in range(n_cols)]
    for h in heights:
        col_h[np.argmin(col_h)] += h
    if with_rotation:
        max_makespan = min(
            sum(
                [
                    min(widths[c], heights[c]) if heights[c] < width else heights[c]
                    for c in range(len(heights))
                ]
            ), max(col_h)
        )
    else:
        max_makespan = max(col_h)
    return max_makespan