include "all_different.mzn";
include "disjunctive.mzn";
include "fzn_cumulative.mzn";
include "fzn_cumulative_reif.mzn";
include "./my_fzn_cumulative.mzn";

predicate my_cumulative(int: n_plates,
                        array[int] of var int: x,
                        array[int] of var int: y,
                        array[int] of var int: lengths,
                        array[int] of var int: widths, 
                        var int: b) =

    % checking if y, lengths and widths have the same index set (corresponding to the set of tasks)                   
    assert(index_set(y) == index_set(lengths) /\ index_set(y) == index_set(widths),
        "cumulative: the 3 array arguments must have identical index sets",
      
    % checking that all length and width values are positive
    if length(y) >= 1 then
    assert(lb_array(lengths) >= 0 /\ lb_array(widths) >= 0,
        "cumulative: lengths and widths must be non-negative",
      
    % checking if we can place more than one plate in x axis
    if  
       let { int: mr = lb_array(widths); 
             int: mri = arg_min([ lb(widths[i]) | i in index_set(widths) ]) } in
       forall(i in index_set(widths))
             (is_fixed(widths[i]) /\ (fix(widths[i]) + mr > ub(b) \/ i = mri))
    then
         % no parallel plates => (if all lengths=1 then all_different, else disjunctive)          
         if forall(i in index_set(lengths))(is_fixed(lengths[i]) /\ fix(lengths[i]) == 1)
         then
            all_different(y)
         else
            disjunctive(y, lengths)
         endif
    
    % we can place more than one plate on x axis
    else
       my_fzn_cumulative(n_plates, x, y, lengths, widths, b)
    endif
    )
    endif);