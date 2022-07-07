%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


predicate c_consecutive_on_x(int: c1, int: c2) = (
    x[c1] + widths[c1] == x[c2] \/ x[c2] + widths[c2] == x[c1]
);

predicate c_consecutive_on_y(int: c1, int: c2) = (
    y[c1] + heights[c1] == y[c2] \/ y[c2] + heights[c2] == y[c1]
);

predicate c_can_be_swapped_on_x(int: c1, int: c2) = (
    c_consecutive_on_x(c1, c2) /\ y[c1] == y[c2] /\ heights[c1] == heights[c2]
);

predicate c_can_be_swapped_on_y(int: c1, int: c2) = (
   c_consecutive_on_y(c1, c2) /\ x[c1] == x[c2] /\ widths[c1] == widths[c2]
);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function var int: makespan(array[CIRCUITS] of var Ys: y) = 
    max(c in CIRCUITS)(y[c] + heights[c]);

function var int: max_makespan2(array[CIRCUITS] of int: heights, int: num_cols) =
    let{
       array[1..num_cols] of int: cols_h = [0 | i in 1..num_cols],

    } in 
    forall(c in index_set(heights))(
        cols[arg_min(cols)] = cols[arg_min(cols)] + heights[c]
    ),
    max(cols)
