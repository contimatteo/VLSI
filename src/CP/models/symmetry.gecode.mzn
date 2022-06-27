include "alldifferent.mzn";
include "cumulative.mzn";
include "utils/symmetry_breaking.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  number of circuits
int: n_circuits;
%%%  set of circuit indexes (used for following arrays)
set of int: CIRCUITS = 1..n_circuits;
%%%  array of xi and yi: the horizontal and the vertical dimension of the circuit i
array[CIRCUITS,1..2] of int: dims;

%%%  width of the silicon plate
int: width;
%%%  array of horizontal dimension of the ciruits
array[CIRCUITS] of int: widths = [dims[c,1] | c in CIRCUITS];
%%%  array of vertical dimension of the circuits
array[CIRCUITS] of int: heights = [dims[c,2] | c in CIRCUITS];

%%% define makespan boundaries
int: sum_area = sum(c in CIRCUITS)(heights[c]*widths[c]);
int: min_makespan = round(sum_area / width);
int: max_makespan = sum(heights);

set of int: Xs = 0..(width - min(widths));
set of int: Ys = 0..(max_makespan - min(heights));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;

var int: makespan = max(c in CIRCUITS)(y[c] + heights[c]);

%%% TODO: ragionare se si possono assegnare gli indici solo ai bordi
array[int] of var int: grid = [
    (x[c]+w) + (y[c]+h)*width | c in CIRCUITS, w in 0..widths[c]-1, h in 0..heights[c]-1
];


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  all circuits must have each dimension greater than zero
constraint assert ( 
    min(dims) > 0, 
    "[ERROR] each circuit must have each dimension greater than zero." 
);

constraint assert(
    CIRCUITS == index_set(x) /\ CIRCUITS == index_set(y) /\ CIRCUITS == index_set(heights) /\ CIRCUITS == index_set(widths),
    "[ERROR] `x`, `y`, `heights` and `widths` arrays must have identical indexes."
);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  base problem constraints (by definition)
constraint cumulative(y, heights, widths, width);
constraint cumulative(x, widths, heights, makespan);
constraint forall(c in CIRCUITS)(x[c] + widths[c] <= width);

%%%  exploit the `grid` variable definition
constraint alldifferent(grid); %%% GECODE
% constraint forall(i1, i2 in index_set(grid) where i1 < i2) (grid[i1] != grid[i2]); %%% CHUFFED


%%% place the circuit with the max height at position (0,0);
%constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;

%%%  define `makespan` boundaries.
constraint makespan >= min_makespan /\ makespan <= max_makespan;
% constraint makespan >= max(heights) /\ makespan <= max_makespan;

%%%  prevent circuits (and group of circuits) to swap
% constraint symmetry_breaking_constraint(break_swapping(n_circuits, x, y, widths, heights));

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %
%%%  create virtual circuits
%%%  # of virtual circuits
int: n_v_circuits = n_circuits*(n_circuits-1) div 2;
int: tot_circuits = n_circuits + n_v_circuits;
%%%  set of virtual circuit indexes 
set of int: V_CIRCUITS = 1..n_v_circuits;

%%%  possible couple of circuits (simple combination of possible c1,c2 indexes)
array [1..2, V_CIRCUITS] of CIRCUITS: couples = array2d(
    1..2, V_CIRCUITS, [c1 | c1,c2 in CIRCUITS where c1<c2] ++ [c2 | c1,c2 in CIRCUITS where c1<c2]
);

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
];

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
];

%%%  x and y of virtual circuits
%%%  couples (generator expression) must be 1d array ...
array[V_CIRCUITS] of var Xs: v_x = [min(x[couples[1,i]], x[couples[2,i]]) | i in V_CIRCUITS];
array[V_CIRCUITS] of var Ys: v_y = [min(y[couples[1,i]], y[couples[2,i]]) | i in V_CIRCUITS];

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
];

%%% merged info
array[1..tot_circuits] of var int: tot_widths = widths ++ v_widths;
array[1..tot_circuits] of var int: tot_heights = heights ++ v_heights;
array[1..tot_circuits] of var Xs: tot_x = x ++ v_x;
array[1..tot_circuits] of var Ys: tot_y = y ++ v_y;
array[1..tot_circuits] of var bool: tot_is_valid = [true | c in CIRCUITS] ++ is_valid;

constraint forall(c1,c2 in 1..tot_circuits where c1<c2)(
    %%%  remove swapping
    if 
        tot_widths[c1] == tot_widths[c2] /\ tot_heights[c1] == tot_heights[c2] 
        /\ 
        tot_is_valid[c1] /\ tot_is_valid[c2] 
        /\
        not (tot_x[c1]==tot_x[c2] /\ tot_y[c1]==tot_y[c2])
        /\
        abs(tot_x[c1] - tot_x[c2]) >= tot_widths[c1] \/ abs(tot_y[c1] - tot_y[c2]) >= tot_heights[c1]
    then 
        if tot_x[c1]!=tot_x[c2]     %abs(tot_x[c1] - tot_x[c2]) >= tot_widths[c1] %\/ abs(tot_y[c1] - tot_y[c2]) >= tot_heights[c1]
        then true %tot_x[c1] < tot_x[c2]
        else true %tot_y[c1] < tot_y[c2]
        endif
    else true
    endif
);

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

constraint makespan=min_makespan;
solve satisfy;
% solve minimize makespan;


output [
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "dims = ", show(dims), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "min_makespan = ", show(min_makespan), "\n",
    "max_makespan = ", show(max_makespan), "\n",
    "makespan = ", show(makespan), "\n",
    "n_v_circuits = ", show(n_v_circuits), "\n",
    "couples = ", show(couples), "\n",
    "couples c1 = ", show([couples[1,i] | i in V_CIRCUITS]), "\n",
    "couples c2 = ", show([couples[2,i] | i in V_CIRCUITS]), "\n",
    "tot_widths = ", show(tot_widths), "\n",
    "tot_heights = ", show(tot_heights), "\n",
    "tot_x = ", show(tot_x), "\n",
    "tot_y = ", show(tot_y), "\n",
    "tot_is_valid = ", show(tot_is_valid), "\n",
    "model = symmetry.gecode"
];
