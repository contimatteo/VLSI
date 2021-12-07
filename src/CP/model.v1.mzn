%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  IMPORT  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

include "globals.mzn";


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  CONSTANTS  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: GRID_MIN_X = 0;
int: GRID_MIN_Y = 0;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  INPUT  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: PLATE_WIDTH; % width of the silicon plate

int: N_CIRCUITS; % number of necessary circuits to place inside the plate

array[1..N_CIRCUITS,1..2] of int: CIRCUITS_DIM;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  COMPUTED  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

set of int: CIRCUITS = 1..N_CIRCUITS;

int: GRID_MAX_X = 19; % TODO: ...
int: GRID_MAX_Y = 19; % TODO: ...

set of int: GRID_X_RANGE = GRID_MIN_X..GRID_MAX_X;
set of int: GRID_Y_RANGE = GRID_MIN_Y..GRID_MAX_Y;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  VARIABLES  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% grid coordinates of {circuits}
array[CIRCUITS] of var GRID_X_RANGE: circuits_x;
array[CIRCUITS] of var GRID_Y_RANGE: circuits_y;

% height of the silicon plate
var int: plate_length;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  CONSTRAINTS  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint plate_length > 0;
constraint plate_length < PLATE_WIDTH + N_CIRCUITS;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  MINIMIZE  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve minimize plate_length;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  OUTPUT  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output [
    "\n",
    ">  PLATE_WIDTH = ", show(PLATE_WIDTH), "\n",
    ">   N_CIRCUITS = ", show(N_CIRCUITS), "\n", 
    "> plate_length = ", show(plate_length), "\n"
];


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%