include "lex_less.mzn";
include "lex_lesseq.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  create virtual circuits
int: v_n_circuits = n_circuits * (n_circuits-1) div 2;
int: rv_n_circuits = n_circuits + v_n_circuits;
%%%  set of virtual circuit indexes
set of int: V_CIRCUITS = 1..v_n_circuits;
set of int: RV_CIRCUITS = 1..rv_n_circuits;

%%%  possible couple of circuits (simple combination of possible c1,c2 indexes)
array [1..2, V_CIRCUITS] of CIRCUITS: c_pairs = array2d(
    1..2, V_CIRCUITS, [c1 | c1,c2 in CIRCUITS where c1<c2] ++ [c2 | c1,c2 in CIRCUITS where c1<c2]
);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate c_grid_x_symmetry() = lex_lesseq(x, [width - x[c] - widths[c] | c in CIRCUITS]);
predicate c_grid_y_symmetry() = lex_lesseq(y, [makespan - y[c] - heights[c] | c in CIRCUITS]);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate c_equal_dim_symmetry() = (
    forall(c1,c2 in CIRCUITS where c1<c2)(
        if widths[c1] == widths[c2] /\ heights[c1] == heights[c2] 
        then lex_lesseq([ x[c1], y[c1] ], [ x[c2], y[c2] ])
        else true
        endif
    )
);

predicate rv_equal_dim_symmetry() = (
    forall(c1 in CIRCUITS, c2 in V_CIRCUITS)(
        if vc_is_valid(c2) /\ widths[c1] == vc_width(c2) /\ heights[c1] == vc_height(c2) 
        then lex_lesseq([ x[c1], y[c1] ], [ vc_x(c2), vc_y(c2) ])
        else true
        endif
    )
);

predicate vv_equal_dim_symmetry() = (
    forall(c1,c2 in V_CIRCUITS where c1<c2)(
        let {
            var int: vc_x1 = vc_x(c1); var int: vc_y1 = vc_y(c1);
            var int: vc_w1 = vc_width(c1); var int: vc_h1 = vc_height(c1);
            var int: vc_x2 = vc_x(c2); var int: vc_y2 = vc_y(c2);
        } in
        if vc_is_valid(c1) /\ vc_is_valid(c2) /\ 
           not (vc_x1 == vc_x2 /\ vc_y1 == vc_y2) /\
           vc_w1 == vc_width(c2) /\ vc_h1 == vc_height(c2) /\
           ( abs(vc_x1 - vc_x2) >= vc_w1 \/ abs(vc_y1 - vc_y2) >= vc_h1 )
        then lex_lesseq([ vc_x1, vc_y1 ], [ vc_x2, vc_y2 ])
        else true
        endif
    )
);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  remove swapping between consecutive circuits on X axis
%%%  remove swapping between consecutive circuits on Y axis
predicate c_consecutive_symmetry() = (
    forall(c1,c2 in CIRCUITS where c1<c2)(
        if c_can_be_swapped_on_x(c1, c2) then lex_less([ x[c1] ], [ x[c2] ]) else true endif
        /\
        if c_can_be_swapped_on_y(c1, c2) then lex_less([ y[c1] ], [ y[c2] ]) else true endif
    )
);
