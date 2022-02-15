%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
    pos[c1,1] + widths[c1] == pos[c2,1] \/ pos[c2,1] + widths[c2] == pos[c1,1]
);

predicate circuits_adjacent_on_y(int: c1, int: c2) = (
    pos[c1,2] + heights[c1] == pos[c2,2] \/ pos[c2,2] + heights[c2] == pos[c1,2]
);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function var int: makespan(array[CIRCUITS, 1..2] of var POS: pos) = 
    max(c in CIRCUITS)(pos[c, 1] + heights[c]);

