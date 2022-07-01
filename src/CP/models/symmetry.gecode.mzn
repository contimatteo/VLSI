include "alldifferent.mzn";
include "cumulative.mzn";
include "utils/symmetry.mzn";
include "utils/global.mzn";


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
% constraint symmetry_breaking_constraint(break_swapping(n_circuits, x, y, widths, heights));

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

%%%  create virtual circuits
int: v_n_circuits = n_circuits * (n_circuits-1) div 2;
int: rv_n_circuits = n_circuits + v_n_circuits;
%%%  set of virtual circuit indexes
set of int: V_CIRCUITS = 1..v_n_circuits;
set of int: RV_CIRCUITS = 1..rv_n_circuits;

%%%  possible couple of circuits (simple combination of possible c1,c2 indexes)
array [1..2, V_CIRCUITS] of CIRCUITS: c_pairs = array2d(
    1..2, V_CIRCUITS, [c1 | c1,c2 in CIRCUITS where c1<c2] ++ [c2 | c1,c2 in CIRCUITS where c1<c2]
);


%%%  INFO: details in order to avoid UNSAT solution for near circuits
%%%  |  check for each circuit c if it's composed by precedent circuits c1, c2
%%%  |  if composed by 2 precedent circuits c1, c2
%%%  |  and they have same height -> cannot swap c in horizontal dim
%%%  |  and they have same width -> cannot swap c in vertical dim


%%%  remove swapping (same size circuits) (with abs)
constraint forall(c1,c2 in RV_CIRCUITS where 
        c1<c2 /\
        rv_width(c1) == rv_width(c2) /\ rv_height(c1) == rv_height(c2) /\ 
        rv_is_valid(c1) /\ rv_is_valid(c2) /\
        not (rv_x(c1)==rv_x(c2) /\ rv_y(c1)==rv_y(c2))
        )(
    if abs(rv_x(c1) - rv_x(c2)) >= rv_width(c1)
    then rv_x(c1) < rv_x(c2)
    else 
        if abs(rv_y(c1) - rv_y(c2)) >= rv_height(c1)
        then rv_y(c1) < rv_y(c2)
        else true
        endif
    endif
);

% %%% impose an ordering constraint for each couple of real circuits that is swappable in a virtual circuit
%  constraint forall (vc in 1..v_n_circuits where rv_is_valid(vc))( 
%     forall (c1,c2 in RV_CIRCUITS where
%         c1 < c2 /\ % c1 != vc /\ c2 != vc /\
%         rv_x(c1) >= rv_x(vc) /\ 
%         rv_x(c1) < rv_x(vc) + rv_width(vc) /\ %%% no need to check if c1 fits in vc: vc is valid
%         rv_y(c1) >= rv_y(vc) /\
%         rv_y(c1) < rv_y(vc)+ rv_height(vc) /\
%         rv_x(c2) >= rv_x(vc) /\ 
%         rv_x(c2) < rv_x(vc) + rv_width(vc) /\
%         rv_y(c2) >= rv_y(vc) /\
%         rv_y(c2) < rv_y(vc)+ rv_height(vc)
%     )( 
%         if (rv_y(c1) = rv_y(c2) /\ rv_height(c1) = rv_height(c2)) %CASE: aligned along x axis with c2 left of c1
%         then rv_x(c1) < rv_x(c2)
%         else 
%                 if (rv_x(c1) = rv_x(c2) /\ rv_width(c1) = rv_width(c2)) %CASE: aligned along on y axis with c1 above c2
%                 then rv_y(c1) < rv_y(c2)
%                 else true
%                 endif
%         endif
%     %)    
% ));


% %%%  remove swapping between consecutive circuits on X axis
% constraint forall(c1,c2 in CIRCUITS where c1<c2)(
%     % if c_can_be_swapped_on_x(c1, c2) then x[c1] < x[c2] else true endif
%     c_can_be_swapped_on_x(c1, c2) -> x[c1] < x[c2]
% );
% %%%  remove swapping between consecutive circuits on Y axis
% constraint forall(c1,c2 in CIRCUITS where c1<c2)(
%     % if c_can_be_swapped_on_y(c1, c2) then y[c1] < y[c2] else true endif
%     c_can_be_swapped_on_y(c1, c2) -> y[c1] < y[c2]
% );


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

ann: search_makespan = int_search([ makespan ], input_order, indomain_min);

solve 
    ::seq_search([ search_makespan ])
    minimize makespan;


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
    % "tot_heights = ", show(tot_heights), "\n",
    % "tot_x = ", show(tot_x), "\n",
    % "tot_y = ", show(tot_y), "\n",
    % "tot_is_valid = ", show(tot_is_valid), "\n"
];
