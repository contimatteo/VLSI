predicate break_swapping(
    int: n_circuits,
    array[CIRCUITS] of var Xs: x,
    array[CIRCUITS] of var Ys: y,
    array[CIRCUITS] of int: heights,
    array[CIRCUITS] of int: widths
) = 
    let {
        %%%  create virtual circuits
        %%%  # of virtual circuits
        int: n_v_circuits = n_circuits*(n_circuits-1) div 2,
        int: tot_circuits = n_circuits + n_v_circuits,
        %%%  set of virtual circuit indexes 
        set of int: V_CIRCUITS = 1..n_v_circuits,

        %%%  possible couple of circuits (simple combination of possible c1,c2 indexes)
        array [1..2, V_CIRCUITS] of CIRCUITS: couples = array2d(
            1..2, V_CIRCUITS, [c1 | c1,c2 in CIRCUITS where c1<c2] ++ [c2 | c1,c2 in CIRCUITS where c1<c2]
        ),

        %%%  array of horizontal dimension of virtual ciruits
        array[V_CIRCUITS] of var int: v_widths = [
            %%%  if c1 on the right -> x[c1]+widths[c1]-x[c2]
            if x[couples[1,i]]>x[couples[2,i]] 
            then x[couples[1,i]] + widths[couples[1,i]] - x[couples[2,i]] 
            else 
                %%% if c1 on the left -> x[c2]+widths[c2]-x[c1]
                if x[couples[1,i]]<x[couples[2,i]]
                then x[couples[2,i]] + widths[couples[2,i]] - x[couples[1,i]]
                else 
                    %%% if c1 and c2 with same x, check who is higher
                    %%%  maybe better to choose the max width
                    if y[couples[1,i]]>y[couples[2,i]]
                    then widths[couples[1,i]]
                    else widths[couples[2,i]]
                    endif
                endif 
            endif | i in V_CIRCUITS
        ],

        %%%  array of vertical dimension of virtual circuits
        array[V_CIRCUITS] of var int: v_heights = [
            %%%  if c1 on the top -> y[c1]+heights[c1]-y[c2]
            if y[couples[1,i]]>y[couples[2,i]] 
            then y[couples[1,i]] + heights[couples[1,i]] - y[couples[2,i]] 
            else 
                %%% if c1 on the bottom -> y[c2]+heights[c2]-y[c1]
                if y[couples[1,i]]<y[couples[2,i]]
                then y[couples[2,i]] + heights[couples[2,i]] - y[couples[1,i]]
                else 
                    %%% if c1 and c2 with same y, check who is on the right
                    %%%  maybe better to choose the max height
                    if x[couples[1,i]]>x[couples[2,i]]
                    then heights[couples[1,i]]
                    else heights[couples[2,i]]
                    endif
                endif 
            endif | i in V_CIRCUITS
        ],

        %%%  x and y of virtual circuits
        %%%  couples (generator expression) must be 1d array ...
        array[V_CIRCUITS] of var Xs: v_x = [min(x[couples[1,i]], x[couples[2,i]]) | i in V_CIRCUITS],
        array[V_CIRCUITS] of var Ys: v_y = [min(y[couples[1,i]], y[couples[2,i]]) | i in V_CIRCUITS],

        %%%  boolean array of validity for virtual blocks
        array[V_CIRCUITS] of var bool: is_valid = [
            %%%  check only circuits starting on the bottom left of the top right corner
            forall(c in CIRCUITS where x[c]<v_x[vc]+v_widths[vc] /\ y[c]<v_y[vc]+v_heights[vc])(                
                %%%  if bottom left corner of c is inside, all the circuit must be inside
                if x[c]>=v_x[vc] /\ y[c]>=v_y[vc]
                then x[c]+widths[c]<=v_x[vc]+v_widths[vc] /\ y[c]+heights[c]<=v_y[vc]+v_heights[vc]
                %%%  otherwise all the circuit must be outside
                else x[c]+widths[c]<=v_x[vc] \/ y[c]+heights[c]<=v_y[vc]                    
                endif
            )
            
            | vc in V_CIRCUITS
        ],

        %%% merged info
        array[1..tot_circuits] of var int: tot_widths = widths ++ v_widths,
        array[1..tot_circuits] of var int: tot_heights = heights ++ v_heights,
        array[1..tot_circuits] of var Xs: tot_x = x ++ v_x,
        array[1..tot_circuits] of var Ys: tot_y = y ++ v_y,
        array[1..tot_circuits] of var bool: tot_is_valid = [true | c in CIRCUITS] ++ is_valid,

    } in (
        
        forall(c1,c2 in 1..tot_circuits where c1<c2)(
            %%%  remove swapping
            if 
                tot_widths[c1] == tot_widths[c2] /\ tot_heights[c1] == tot_heights[c2] 
                /\ 
                tot_is_valid[c1] /\ tot_is_valid[c2] 
                /\
                not (tot_x[c1]==tot_x[c2] /\ tot_y[c1]==tot_y[c2])
            then 
                if tot_x[c1] != tot_x[c2]
                then tot_x[c1] < tot_x[c2]
                else tot_y[c1] < tot_y[c2]
                endif
            else true
            endif
        )
    );