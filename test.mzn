include "globals.mzn";

int: n_plates;
set of int: PLATES = 1..n_plates;
array[PLATES,1..2] of int: dims;
array[PLATES] of int: lengths = [dims[i,2] | i in PLATES];

int: width;
set of int: WIDTHS = 1..width;
array[PLATES] of int: widths = [dims[i,1] | i in PLATES];

int: max_length = sum(lengths);
array[PLATES] of var 0..max_length: pos;

constraint cumulative(pos, lengths, widths, width);

var int: tot_length = max(p in PLATES)(pos[p] + lengths[p]);

solve minimize tot_length;

output [
    "Pos = ", show(pos), "\n",
    "End = ", show([pos[p]+lengths[p] | p in PLATES]), "\n",
    "Total lenght = ", show(tot_length), "\n"
    ];