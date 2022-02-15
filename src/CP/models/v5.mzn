%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


include "./utils/mc_cumulative.mzn";
include "./utils/mc_utils.mzn";


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% number of circuits
int: n_circuits;
% width of the silicon plate
int: width;

% set of circuit indexes (used for following arrays)
set of int: CIRCUITS = 1..n_circuits;

% array of xi and yi: the horizontal and the vertical dimension of the circuit i
array[CIRCUITS,1..2] of int: dims;
% array of horizontal dimension of the ciruits
array[CIRCUITS] of int: widths = [dims[i,1] | i in CIRCUITS];
% array of vertical dimension of the circuits
array[CIRCUITS] of int: heights = [dims[i,2] | i in CIRCUITS];

% define position x and y of bottom left corner of each circuit
int: max_length = sum(heights);
% define domain of finale `pos` variable.
set of int: POS = 0..max_length;

% find the circuit (index) with the max height.
int: circuit_index_with_max_height = arg_max(heights);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% define position x and y of bottom left corner of each circuit
array[CIRCUITS, 1..2] of var POS: pos;

array[CIRCUITS] of var int: x = [pos[c, 2] | c in CIRCUITS];
array[CIRCUITS] of var int: y = [pos[c, 1] | c in CIRCUITS];

var int: makespan = makespan(pos);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


constraint my_cumulative(n_circuits, x, y, heights, widths, width);

% place the circuit with the max height at position (0,0);
constraint pos[circuit_index_with_max_height, 1] == 0 /\ pos[circuit_index_with_max_height, 2] == 0;

% SIMMETRY --> tutti i circuiti alti e lunghi uguali
constraint forall(c1,c2 in CIRCUITS) (
    if c1 < c2 /\ circuits_with_equal_dim(c1, c2)
    then lex_lesseq([ pos[c1, i] | i in 1..2 ], [ pos[c2, i] | i in 1..2 ])
    else true
    endif
);
% SIMMETRY --> tutti i circuiti LUNGHI uguali e adiacenti (rispetto a x)
constraint forall(c1,c2 in CIRCUITS) (
    if c1 < c2 /\ circuits_adjacent_on_x(c1, c2) /\ circuits_with_equal_width(c1, c2)
    then lex_lesseq([ pos[c1, i] | i in 1..2 ], [ pos[c2, i] | i in 1..2 ])
    else true
    endif
);
% SIMMETRY --> tutti i circuiti ALTI uguali e adiacenti (rispetto a y)
constraint forall(c1,c2 in CIRCUITS) (
    if c1 < c2 /\ circuits_adjacent_on_y(c1, c2) /\ circuits_with_equal_height(c1, c2)
    then lex_lesseq([ pos[c1, i] | i in 1..2 ], [ pos[c2, i] | i in 1..2 ])
    else true
    endif
);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% constraint makespan <= max_length / 2;
constraint makespan == 8;

% solve minimize makespan;
solve satisfy;


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


output [
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "dims = ", show(dims), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "pos = ", show(pos), "\n",
    "makespan = ", show(makespan), "\n"
];
