include "cumulative.mzn";
include "diffn.mzn";

include "components/search.mzn";


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
%int: max_makespan = sum(heights);
int: max_makespan;

set of int: Xs = 0..(width - min(widths));
set of int: Ys = 0..(max_makespan - min(heights));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;

var int: makespan = max(c in CIRCUITS)(y[c] + heights[c]);

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


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
constraint diffn(x, y, widths, heights) :: domain;
constraint cumulative(y, heights, widths, width) :: domain;
constraint cumulative(x, widths, heights, makespan) :: domain;
constraint forall(c in CIRCUITS)(x[c] + widths[c] <= width);

%%% force the biggest block to be always to the bottom left of the second biggest
constraint x[1] <= x[2] /\ y[1] <= y[2];

%%% define `makespan` boundaries.
constraint makespan >= min_makespan /\ makespan <= max_makespan;

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


solve :: seq_search([
    ann_search_makespan,
    ann_search_x,
    ann_search_y,
]) :: ann_restart minimize makespan;


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


output [
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "min_makespan = ", show(min_makespan), "\n",
    "max_makespan = ", show(max_makespan), "\n",
    "makespan = ", show(makespan), "\n",
];
