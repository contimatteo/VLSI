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

% 
int: min_makespan = min(heights);
int: max_makespan = sum(heights);
% define domain of finale `pos` variable.
set of int: POS = 0..max_makespan;


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% define position x and y of bottom left corner of each circuit
array[CIRCUITS, 1..2] of var POS: pos;

array[CIRCUITS] of var int: x = [pos[c, 2] | c in CIRCUITS];
array[CIRCUITS] of var int: y = [pos[c, 1] | c in CIRCUITS];

var int: makespan = makespan(pos);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


constraint my_cumulative(n_circuits, x, y, heights, widths, width);


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% PROVEEEEEEEE

array[CIRCUITS, CIRCUITS] of var bool: c_list_for_simmetry_mask = array2d(CIRCUITS, CIRCUITS, (
    [ 
        if c1 <= c2 /\ (
            c1 == c2 
            \/ 
            circuits_can_be_merged_on_x(c1, c2) 
            \/ 
            circuits_can_be_merged_on_y(c1, c2)
        )
        then true
        else false
        endif
        | c1,c2 in CIRCUITS
    ]
));

% array[int] of CIRCUITS: c_list_for_simmetry = [ 
%     i | i,j in CIRCUITS where 
%         i <= j /\
%         (
%             c_list_for_simmetry_mask[i,j] == true 
%             \/ 
%             c_list_for_simmetry_mask[j,i] == true
%         )
% ];


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% constraint makespan <= max_makespan / 2;
constraint makespan >= min_makespan /\ makespan <= max_makespan;

% constraint x[4] == 3 /\ y[4] == 0;
% constraint x[7] == 3 /\ y[7] == 3;
% constraint x[8] == 0 /\ y[8] == 0;

% solve minimize makespan;
solve 
    % :: seq_search([
    %     int_search(makespan, first_fail, indomain_min)
    % ])
    satisfy;


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


output [
    "\n",
    "\n",
    "width = ", show(width), "\n",
    "n_circuits = ", show(n_circuits), "\n",
    "dims = ", show(dims), "\n",
    "widths = ", show(widths), "\n",
    "heights = ", show(heights), "\n",
    "x = ", show(x), "\n",
    "y = ", show(y), "\n",
    "pos = ", show(pos), "\n",
    "makespan = ", show(makespan), "\n",
    "c_list_for_simmetry_mask = ", show(c_list_for_simmetry_mask), "\n",
    % "c_list_for_simmetry = ", show(c_list_for_simmetry), "\n",
    "\n",
    "\n"
];
