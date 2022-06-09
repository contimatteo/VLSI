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
%%%  array of horizontal dimension of the ciruits
array[CIRCUITS] of WIDTHS: widths = [dims[i,1] | i in CIRCUITS];

%%%  array of vertical dimension of the circuits
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

%%%  define position x and y of bottom left corner of each circuit
int: max_makespan = sum(heights);

set of int: Xs = 0..(width - min(widths));
set of int: Ys = 0..(max_makespan - min(heights));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;

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
constraint cumulative(y, heights, widths, width);
constraint cumulative(x, widths, heights, makespan);
constraint forall(c in CIRCUITS)(x[c] + widths[c] <= width);
<<<<<<< Updated upstream
%%% ragionare se si possono assegnare gli indici solo ai bordi
=======
>>>>>>> Stashed changes
constraint (
    alldifferent([ (x[c]+k) + (y[c]+h)*width | c in CIRCUITS, 
                                               k in 0..widths[c]-1, 
                                               h in 0..heights[c]-1]));


%%% place the circuit with the max height at position (0,0);
constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;

%%% define `makespan` boundaries.
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
