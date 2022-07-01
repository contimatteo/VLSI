include "alldifferent.mzn";
include "cumulative.mzn";

include "components/symmetry.mzn";
include "utils/symmetry.mzn";
include "utils/global.mzn";

mzn_ignore_symmetry_breaking_constraints = false;

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


%%% ISSUE: the previous formalization cannot work in combination with the new symmetries formulation.
%%% place the circuit with the max height at position (0,0);
%constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;
%%% TODO: place ONE of the circuits with the max height at position (0,0);
%%% ...

%%%  define `makespan` boundaries.
constraint makespan >= min_makespan /\ makespan <= max_makespan;


%%%  prevent circuits (and group of circuits) to swap
constraint symmetry_breaking_constraint(c_equal_dim_symmetry());
constraint symmetry_breaking_constraint(c_consecutive_symmetry());


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


ann: search_makespan = int_search([ makespan ], input_order, indomain_min);

solve :: seq_search([ search_makespan ]) minimize makespan;
% constraint makespan == min_makespan;    
% solve :: seq_search([ search_makespan ]) satisfy;


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
    % "v_n_circuits = ", show(v_n_circuits), "\n",
    % "c_pairs = ", show(c_pairs), "\n",
    % "c_pairs c1 = ", show([c_pairs[1,i] | i in V_CIRCUITS]), "\n",
    % "c_pairs c2 = ", show([c_pairs[2,i] | i in V_CIRCUITS]), "\n",
    % "rv_width = ", show(rv_width), "\n",
    % "vc_height = ", show([ vc_height(c) | c in V_CIRCUITS ]), "\n",
    % "tot_heights = ", show(tot_heights), "\n",
    % "tot_x = ", show(tot_x), "\n",
    % "tot_y = ", show(tot_y), "\n",
    % "tot_is_valid = ", show(tot_is_valid), "\n"
];
