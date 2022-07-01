
%%%  array of horizontal dimension of virtual ciruits
function var int: vc_width (V_CIRCUITS: vc_index) = (
    %%%  if c1 on the right -> x[c1]+widths[c1]-x[c2]
    if x[c_pairs[1,vc_index]]>x[c_pairs[2,vc_index]] 
    then x[c_pairs[1,vc_index]] + widths[c_pairs[1,vc_index]] - x[c_pairs[2,vc_index]] 
    else 
        %%% if c1 on the left -> x[c2]+widths[c2]-x[c1]
        if x[c_pairs[1,vc_index]]<x[c_pairs[2,vc_index]]
        then x[c_pairs[2,vc_index]] + widths[c_pairs[2,vc_index]] - x[c_pairs[1,vc_index]]
        else 
            %%% if c1 and c2 with same x, check who is higher
            %%%  maybe better to choose the max width
            if y[c_pairs[1,vc_index]]>y[c_pairs[2,vc_index]]
            then widths[c_pairs[1,vc_index]]
            else widths[c_pairs[2,vc_index]]
            endif
        endif 
    endif
);


function var int: vc_height (V_CIRCUITS: vc_index) = (
    %%%  if c1 on the top -> y[c1]+heights[c1]-y[c2]
    if y[c_pairs[1,vc_index]]>y[c_pairs[2,vc_index]] 
    then y[c_pairs[1,vc_index]] + heights[c_pairs[1,vc_index]] - y[c_pairs[2,vc_index]] 
    else 
        %%% if c1 on the bottom -> y[c2]+heights[c2]-y[c1]
        if y[c_pairs[1,vc_index]]<y[c_pairs[2,vc_index]]
        then y[c_pairs[2,vc_index]] + heights[c_pairs[2,vc_index]] - y[c_pairs[1,vc_index]]
        else 
            %%% if c1 and c2 with same y, check who is on the right
            if x[c_pairs[1,vc_index]]>x[c_pairs[2,vc_index]]
            then heights[c_pairs[1,vc_index]]
            else heights[c_pairs[2,vc_index]]
            endif
        endif 
    endif
);

function var int: vc_x (V_CIRCUITS: vc_index) = (
    min(x[c_pairs[1,vc_index]], x[c_pairs[2,vc_index]])
);

function var int: vc_y (V_CIRCUITS: vc_index) = (
    min(y[c_pairs[1,vc_index]], y[c_pairs[2,vc_index]])
);


function var bool: vc_is_valid (V_CIRCUITS: vc_index) = (
    %%%  check only circuits starting on the bottom left of the top right corner
    forall(c in CIRCUITS where x[c]<vc_x(vc_index)+vc_width(vc_index) /\ y[c]<vc_y(vc_index)+vc_height(vc_index))(                
        %%%  if bottom left corner of c is inside, all the circuit must be inside
        if x[c]>=vc_x(vc_index) /\ y[c]>=vc_y(vc_index)
        then x[c]+widths[c]<=vc_x(vc_index)+vc_width(vc_index) /\ y[c]+heights[c]<=vc_y(vc_index)+vc_height(vc_index)
        %%%  otherwise all the circuit must be outside
        else x[c]+widths[c]<=vc_x(vc_index) \/ y[c]+heights[c]<=vc_y(vc_index)                    
        endif
    )
);


function var int: rv_width (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_width(c_index - n_circuits)
        else widths[c_index]
    endif
);

function var int: rv_height (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_height(c_index - n_circuits)
        else heights[c_index]
    endif
);

function var Xs: rv_x (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_x(c_index - n_circuits)
        else x[c_index]
    endif
);

function var Ys: rv_y (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_y(c_index - n_circuits)
        else y[c_index]
    endif
);

function var bool: rv_is_valid (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_is_valid(c_index - n_circuits)
        else true
    endif
);
