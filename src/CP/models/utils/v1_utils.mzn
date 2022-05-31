%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

predicate circuits_with_same_x(int: c1, int: c2) = (
    x[c1] == x[c2]
);
predicate circuits_with_same_y(int: c1, int: c2) = (
    y[c1] == y[c2]
);

predicate circuits_with_equal_width(int: c1, int: c2) = (
    widths[c1] == widths[c2]
);

predicate circuits_with_equal_height(int: c1, int: c2) = (
    heights[c1] == heights[c2]
);

predicate circuits_with_equal_dim(int: c1, int: c2) = (
    circuits_with_equal_width(c1, c2) /\ circuits_with_equal_height(c1, c2)
);


predicate circuits_adjacent_on_x(int: c1, int: c2) = (
    x[c1] + widths[c1] == x[c2] \/ x[c2] + widths[c2] == x[c1]
);

predicate circuits_adjacent_on_y(int: c1, int: c2) = (
    y[c1] + heights[c1] == y[c2] \/ y[c2] + heights[c2] == y[c1]
);

predicate circuits_can_be_merged_on_x(int: c1, int: c2) = (
    circuits_adjacent_on_x(c1, c2) /\ circuits_with_same_y(c1, c2) /\ circuits_with_equal_height(c1, c2)
);

predicate circuits_can_be_merged_on_y(int: c1, int: c2) = (
   circuits_adjacent_on_y(c1, c2) /\ circuits_with_same_x(c1, c2) /\ circuits_with_equal_width(c1, c2)
);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function var int: makespan(array[CIRCUITS] of var Ys: y) = 
    max(c in CIRCUITS)(y[c] + heights[c])

