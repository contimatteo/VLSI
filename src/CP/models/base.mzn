include "./utils/v1_cumulative.mzn";
include "./utils/v1_utils.mzn";

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


%%%  number of circuits
int: n_circuits;
%%%  set of circuit indexes (used for following arrays)
set of int: CIRCUITS = 1..n_circuits;
%%%  array of xi and yi: the horizontal and the vertical dimension of the circuit i
array[CIRCUITS,1..2] of int: dims;

set of int: WIDTHS = 1..width;
%%%  width of the silicon plate
int: width;
%%%  array of horizontal dimension of the circuits
array[CIRCUITS] of WIDTHS: widths = [dims[i,1] | i in CIRCUITS];
  
%%%  array of vertical dimension of the circuits
% array[CIRCUITS] of int: 1..infinity = [dims[i,2] | i in CIRCUITS];
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

%%%  define position x and y of bottom left corner of each circuit
%int: max_makespan = sum(heights);
% #rotation if we rotate the circuits we can sum the smaller dimension of every circuit (if it fits the width and we can rotate it)
int: max_makespan = sum(i in 1..n_circuits)(if heights[i] < width then min(heights[i], widths[i]) else heights[i] endif);

set of int: Xs = 0..(width - min(widths));
set of int: Ys = 0..(max_makespan - min(heights));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;
array[0..width, 0..max_makespan] of var CIRCUITS: grid; 

var int: makespan = max(c in CIRCUITS)(y[c] + heights[c]);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

%# rotation array: is the circuit at index i rotated or not
array[CIRCUITS] of var bool: rotation;

% #rotation functions to retrieve the actual height and width of a circuit
function var int: r_height(int: i) = (not rotation[i]) * heights[i] + rotation[i] * widths[i];
function var int: r_width(int: i) = (not rotation[i]) * widths[i] + rotation[i] * heights[i];


%%%  all circuits must have each dimension greater than zero
constraint assert ( 
    min(heights) > 0, 
    "[ERROR] each circuit must have the height dimension greater than zero."
);

constraint assert(
    CIRCUITS == index_set(x) /\ CIRCUITS == index_set(y) /\ CIRCUITS == index_set(heights) /\ CIRCUITS == index_set(widths),
    "[ERROR] `x`, `y`, `heights` and `widths` arrays must have identical indexes."
);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

%%%  base problem constraints (by definition)
%constraint cumulative(y,heights, widths, width);
%#rotation 
constraint cumulative(y, [r_height(i) | i in CIRCUITS], [r_width(i) | i in CIRCUITS], width);
%constraint cumulative(x, widths, heights, makespan);
constraint cumulative(x, [r_width(i) | i in CIRCUITS], [r_height(i) | i in CIRCUITS], makespan);

constraint forall(c in CIRCUITS)(x[c] + widths[c] <= width);
constraint forall(c in CIRCUITS)(
    forall(k in 0..r_width(c)-1, h in 0..r_height(c)-1)(
        grid[ x[c]+k, y[c]+h ] == c
    )
);

%%% place the circuit with the max height at position (0,0); #rotation 
constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;

%%% define `makespan` boundaries. #rotation: we could increase lower bound
constraint makespan >= max(heights) /\ makespan <= max_makespan; 

% SIMMETRY --> tutti i circuiti con le stesse dimensioni
% constraint forall(c1,c2 in CIRCUITS) (
%     if c1 < c2 /\ circuits_with_equal_dim(c1, c2)
%     then lex_lesseq([ x[c1], y[c1] ], [ x[c2], y[c2] ])
%     else true
%     endif
% );

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


solve minimize makespan;


output [
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "dims = ", show(dims), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "makespan = ", show(makespan), "\n"
];
