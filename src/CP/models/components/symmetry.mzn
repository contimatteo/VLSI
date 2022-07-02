include "lex_lesseq.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


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


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate c_equal_dim_symmetry() = (
    % forall(c1,c2 in RV_CIRCUITS where c1<c2)(
    %     if 
    %         rv_width(c1) == rv_width(c2) /\ rv_height(c1) == rv_height(c2) 
    %         /\ rv_is_valid(c1) /\ rv_is_valid(c2) 
    %         /\ not (rv_x(c1)==rv_x(c2) /\ rv_y(c1)==rv_y(c2))
    %     then
    %         if abs(rv_x(c1) - rv_x(c2)) >= rv_width(c1)
    %         then rv_x(c1) < rv_x(c2)
    %         else 
    %             if abs(rv_y(c1) - rv_y(c2)) >= rv_height(c1)
    %             then rv_y(c1) < rv_y(c2)
    %             else true
    %             endif
    %         endif
    %     else true
    %     endif
    % )

    forall(c1,c2 in CIRCUITS where c1<c2)(
        if widths[c1] == widths[c2] /\ heights[c1] == heights[c2] 
        then lex_lesseq([ x[c1], y[c1] ], [ x[c2], y[c2] ])
        else true
        endif
    )
    % /\
    % forall(c1 in CIRCUITS, c2 in V_CIRCUITS)(
    %     if vc_is_valid(c2) /\ widths[c1] == vc_width(c2) /\ heights[c1] == vc_height(c2) 
    %     then lex_lesseq([ x[c1], y[c1] ], [ vc_x(c2), vc_y(c2) ])
    %     else true
    %     endif
    % )
    % /\
    % forall(c1,c2 in V_CIRCUITS where c1<c2)(
    %     let {
    %         var int: vc_x1 = vc_x(c1);
    %         var int: vc_y1 = vc_y(c1);
    %         var int: vc_w1 = vc_width(c1);
    %         var int: vc_h1 = vc_height(c1);
    %         var int: vc_x2 = vc_x(c2);
    %         var int: vc_y2 = vc_y(c2);
    %     } in
    %     if 
    %         vc_is_valid(c1) /\ vc_is_valid(c2) /\ 
    %         not (vc_x1 == vc_x2 /\ vc_y1 == vc_y2) /\
    %         vc_w1 == vc_width(c2) /\ vc_h1 == vc_height(c2) /\
    %         ( abs(vc_x1 - vc_x2) >= vc_w1 \/ abs(vc_y1 - vc_y2) >= vc_h1 )
    %     then lex_lesseq([ vc_x1, vc_y1 ], [ vc_x2, vc_y2 ])
    %     else true
    %     endif
    % )
);


predicate c_consecutive_symmetry() = (
    true
    %%%  INFO: details in order to avoid UNSAT solution for near circuits
    %%%  |  check for each circuit c if it's composed by precedent circuits c1, c2
    %%%  |  if composed by 2 precedent circuits c1, c2
    %%%  |  and they have same height -> cannot swap c in horizontal dim
    %%%  |  and they have same width -> cannot swap c in vertical dim
    %
    % %%% impose an ordering constraint for each couple of real circuits that is swappable in a virtual circuit
    %  constraint forall (vc in 1..v_n_circuits where rv_is_valid(vc))( 
    %     forall (c1,c2 in RV_CIRCUITS where
    %         c1 < c2 /\ % c1 != vc /\ c2 != vc /\
    %         rv_x(c1) >= rv_x(vc) /\ 
    %         rv_x(c1) < rv_x(vc) + rv_width(vc) /\ %%% no need to check if c1 fits in vc: vc is valid
    %         rv_y(c1) >= rv_y(vc) /\
    %         rv_y(c1) < rv_y(vc)+ rv_height(vc) /\
    %         rv_x(c2) >= rv_x(vc) /\ 
    %         rv_x(c2) < rv_x(vc) + rv_width(vc) /\
    %         rv_y(c2) >= rv_y(vc) /\
    %         rv_y(c2) < rv_y(vc)+ rv_height(vc)
    %     )( 
    %         if (rv_y(c1) = rv_y(c2) /\ rv_height(c1) = rv_height(c2)) %CASE: aligned along x axis with c2 left of c1
    %         then rv_x(c1) < rv_x(c2)
    %         else 
    %                 if (rv_x(c1) = rv_x(c2) /\ rv_width(c1) = rv_width(c2)) %CASE: aligned along on y axis with c1 above c2
    %                 then rv_y(c1) < rv_y(c2)
    %                 else true
    %                 endif
    %         endif
    %     %)    
    % ));
    %
    % %%%  remove swapping between consecutive circuits on X axis
    % constraint forall(c1,c2 in CIRCUITS where c1<c2)(
    %     % if c_can_be_swapped_on_x(c1, c2) then x[c1] < x[c2] else true endif
    %     c_can_be_swapped_on_x(c1, c2) -> x[c1] < x[c2]
    % );
    % %%%  remove swapping between consecutive circuits on Y axis
    % constraint forall(c1,c2 in CIRCUITS where c1<c2)(
    %     % if c_can_be_swapped_on_y(c1, c2) then y[c1] < y[c2] else true endif
    %     c_can_be_swapped_on_y(c1, c2) -> y[c1] < y[c2]
    % );
    %
);