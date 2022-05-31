include "./utils/v1_cumulative.mzn";
include "./utils/v1_utils.mzn";


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
array[CIRCUITS] of 1..width: widths = [dims[i,1] | i in CIRCUITS];

%%%  array of vertical dimension of the circuits
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

%%%  define position x and y of bottom left corner of each circuit
int: max_makespan = sum(heights);

set of int: Xs = 0..(width - min(widths));
set of int: Ys = 0..(max_makespan - min(heights));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;


% var int: makespan = max(c in CIRCUITS)(pos[c, 1] + heights[c]);
var int: makespan = max(c in CIRCUITS)(y[c] + heights[c]);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


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
constraint v1_cumulative(x, y, heights, widths, width);

%%% place the circuit with the max height at position (0,0);
constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;

%%%  TODO: remove this
constraint makespan == 8;

% % SIMMETRY --> tutti i circuiti con le stesse dimensioni
% constraint forall(c1,c2 in CIRCUITS) (
%     if c1 < c2 /\ circuits_with_equal_dim(c1, c2)
%     then lex_lesseq([ pos[c1, i] | i in 1..2 ], [ pos[c2, i] | i in 1..2 ])
%     else true
%     endif
% );

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


solve satisfy;


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
