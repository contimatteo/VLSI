include "./utils/my_cumulative.mzn";

% number of circuits
int: n_circuits;
% set of circuit indexes (used for following arrays)
set of int: CIRCUITS = 1..n_circuits;
% array of xi and yi: the horizontal and the vertical dimension of the circuit i
array[CIRCUITS,1..2] of int: dims;

% width of the silicon plate
int: width;
% array of horizontal dimension of the ciruits
array[CIRCUITS] of int: widths = [dims[i,1] | i in CIRCUITS];

% array of vertical dimension of the circuits
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

% define position x and y of bottom left corner of each circuit
int: max_length = sum(heights);
array[CIRCUITS,1..2] of var 0..max_length: pos;
array[int] of var int: x = [pos[c, 2] | c in CIRCUITS];
array[int] of var int: y = [pos[c, 1] | c in CIRCUITS];


constraint my_cumulative(n_circuits, x, y, heights, widths, width);

var int: tot_length = max(c in CIRCUITS)(pos[c, 1] + heights[c]);

solve minimize tot_length;


output [
    "Pos x = ", show(pos), "\n",
    "Total lenght = ", show(tot_length), "\n"
    ];