%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


predicate circuits_have_equal_dim(int: c1, int: c2) = (
    c1 < c2 /\ widths[c1] == widths[c2] /\ heights[c1] == heights[c2]
);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function var int: makespan(array[CIRCUITS, 1..2] of var POS: pos) = 
    max(c in CIRCUITS)(pos[c, 1] + heights[c]);

