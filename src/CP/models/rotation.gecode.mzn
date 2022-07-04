% include "alldifferent.mzn";
% include "cumulative.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

% %%% rotations: whether the circuit at index `i` rotated or not
% array[CIRCUITS] of var bool: is_rotated;

% function var int: r_height(int: c) = (not is_rotated[c]) * heights[c] + is_rotated[c] * widths[c];
% function var int: r_width(int: c) = (not is_rotated[c]) * widths[c] + is_rotated[c] * heights[c];


% %%%  number of circuits
% int: n_circuits;
% %%%  set of circuit indexes (used for following arrays)
% set of int: CIRCUITS = 1..n_circuits;
% %%%  array of xi and yi: the horizontal and the vertical dimension of the circuit i
% array[CIRCUITS,1..2] of int: dims;

% %%%  width of the silicon plate
% int: width;
% %%%  array of horizontal dimension of the ciruits
% % array[CIRCUITS] of var int: widths = [ (not is_rotated[c]) * dims[c,1] + is_rotated[c] * dims[c,2] | c in CIRCUITS ];
% array[CIRCUITS] of int: widths = [dims[i,1] | i in CIRCUITS];
% %%%  array of vertical dimension of the circuits
% % array[CIRCUITS] of var int: heights = [ (not is_rotated[c]) * dims[c,2] + is_rotated[c] * dims[c,1] | c in CIRCUITS ];
% array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

% %%% define makespan boundaries
% int: sum_area = sum(c in CIRCUITS)(dims[c,1]*dims[c,2]);
% int: min_makespan = round(sum_area / width);
% % int: max_makespan = sum(heights);
% int: max_makespan = sum(c in 1..n_circuits)(if heights[c] < width then min(heights[c], widths[c]) else heights[c] endif);

% set of int: Xs = 0..(width - min(dims));
% set of int: Ys = 0..(max_makespan - min(dims));
% array[CIRCUITS] of var Xs: x;
% array[CIRCUITS] of var Ys: y;

% var int: makespan = max(c in CIRCUITS)(y[c] + r_height(c));

% %%% TODO: ragionare se si possono assegnare gli indici solo ai bordi
% array[int] of var int: grid = [
%     % (x[c]+k) + (y[c]+h)*width | c in CIRCUITS, k in 0..widths[c]-1, h in 0..heights[c]-1
%     ( x[c] + (w * (not is_rotated[c]) + h * is_rotated[c]) ) + 
%     ( y[c] + (w * is_rotated[c] + h * (not is_rotated[c])) ) * width
%     | c in CIRCUITS, w in 0..widths[c]-1, h in 0..heights[c]-1
% ];


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% %%%  all circuits must have each dimension greater than zero
% constraint assert ( 
%     min(dims) > 0, 
%     "[ERROR] each circuit must have each dimension greater than zero." 
% );

% constraint assert(
%     CIRCUITS == index_set(x) /\ CIRCUITS == index_set(y) /\ CIRCUITS == index_set(heights) /\ CIRCUITS == index_set(widths),
%     "[ERROR] `x`, `y`, `heights` and `widths` arrays must have identical indexes."
% );


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

% %%%  base problem constraints (by definition)
% % constraint cumulative(y, heights, widths, width);
% % constraint cumulative(x, widths, heights, makespan);
% % constraint forall(c in CIRCUITS)(x[c] + widths[c] <= width);
% constraint cumulative(y, [r_height(c) | c in CIRCUITS], [r_width(c) | c in CIRCUITS], width);
% constraint cumulative(x, [r_width(c) | c in CIRCUITS], [r_height(c) | c in CIRCUITS], makespan);
% constraint forall(c in CIRCUITS)(x[c] + r_width(c) <= width);

% %%%  exploit the `grid` variable definition
% constraint alldifferent(grid); %%% GECODE
% % constraint forall(i1, i2 in index_set(grid) where i1 < i2) (grid[i1] != grid[i2]); %%% CHUFFED


% %%% place the circuit with the max height at position (0,0);
% constraint x[arg_max(heights)] == 0 /\ y[arg_max(heights)] == 0;

% %%% define `makespan` boundaries.
% constraint makespan >= min_makespan /\ makespan <= max_makespan;
% % constraint makespan >= max(heights) /\ makespan <= max_makespan;


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% solve minimize makespan;


% output [
%     "width = ", show(width), "\n",
%     "n_circuits = ", show(n_circuits), "\n",
%     "dims = ", show(dims), "\n",
%     "widths = ", show(widths), "\n",
%     "heights = ", show(heights), "\n",
%     "x = ", show(x), "\n",
%     "y = ", show(y), "\n",
%     "is_rotated = ", show(is_rotated), "\n",
%     "min_makespan = ", show(min_makespan), "\n",
%     "max_makespan = ", show(max_makespan), "\n",
%     "makespan = ", show(makespan), "\n",
%     "model = rotation.gecode"
% ];
