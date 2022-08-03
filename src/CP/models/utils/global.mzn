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


% function var int: makespan(array[CIRCUITS] of var Ys: y) = 
%     max(c in CIRCUITS)(y[c] + heights[c])

