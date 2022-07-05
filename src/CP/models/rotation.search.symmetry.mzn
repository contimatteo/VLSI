include "cumulative.mzn";
include "diffn.mzn";

include "components/symmetry.mzn";
include "components/search.mzn";
include "utils/symmetry.mzn";
include "utils/global.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

%%% rotations: whether the circuit at index `i` rotated or not
array[CIRCUITS] of var bool: is_rotated;

function var int: r_height(int: c) = (not is_rotated[c]) * heights[c] + is_rotated[c] * widths[c];
function var int: r_width(int: c) = (not is_rotated[c]) * widths[c] + is_rotated[c] * heights[c];


%%%  number of circuits
int: n_circuits;
%%%  set of circuit indexes (used for following arrays)
set of int: CIRCUITS = 1..n_circuits;
%%%  array of xi and yi: the horizontal and the vertical dimension of the circuit i
array[CIRCUITS,1..2] of int: dims;

%%%  width of the silicon plate
int: width;

%%%  array of horizontal dimension of the ciruits
% array[CIRCUITS] of var int: widths = [ (not is_rotated[c]) * dims[c,1] + is_rotated[c] * dims[c,2] | c in CIRCUITS ];
array[CIRCUITS] of int: widths = [dims[i,1] | i in CIRCUITS];
%%%  array of vertical dimension of the circuits
% array[CIRCUITS] of var int: heights = [ (not is_rotated[c]) * dims[c,2] + is_rotated[c] * dims[c,1] | c in CIRCUITS ];
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

%%% define makespan boundaries
int: sum_area = sum(c in CIRCUITS)(heights[c]*widths[c]);
int: min_makespan = round(sum_area / width);
int: max_makespan = sum(c in 1..n_circuits)(if heights[c] < width then min(heights[c], widths[c]) else heights[c] endif);

set of int: Xs = 0..(width - min(dims));
set of int: Ys = 0..(max_makespan - min(dims));
array[CIRCUITS] of var Xs: x;
array[CIRCUITS] of var Ys: y;

var int: makespan = max(c in CIRCUITS)(y[c] + r_height(c));


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
constraint diffn(x, y, [r_width(c) | c in CIRCUITS], [r_height(c) | c in CIRCUITS]) :: domain;
constraint cumulative(y, [r_height(c) | c in CIRCUITS], [r_width(c) | c in CIRCUITS], width) :: domain;
constraint cumulative(x, [r_width(c) | c in CIRCUITS], [r_height(c) | c in CIRCUITS], makespan) :: domain;
constraint forall(c in CIRCUITS)(x[c] + r_width(c) <= width);

%%% define `makespan` boundaries.
constraint makespan >= min_makespan /\ makespan <= max_makespan;

%%% force the biggest block to be always to the bottom left of the second biggest
constraint x[1] <= x[2] /\ y[1] <= y[2];

%%%  prevent circuits (and group of circuits) to swap
constraint symmetry_breaking_constraint(c_grid_x_symmetry());
constraint symmetry_breaking_constraint(c_grid_y_symmetry());
constraint symmetry_breaking_constraint(c_equal_dim_symmetry());
constraint symmetry_breaking_constraint(c_consecutive_symmetry());


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


solve :: seq_search([
    ann_search_makespan,
    ann_search_x,
    ann_search_y,
    %%% 'indomain_random' is not supported yet!
    % ann_search_rot,
]) :: ann_restart minimize makespan;


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %



output [
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "dims = ", show(dims), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "is_rotated = ", show(is_rotated), "\n",
    "min_makespan = ", show(min_makespan), "\n",
    "max_makespan = ", show(max_makespan), "\n",
    "makespan = ", show(makespan), "\n"
];
