include "all_different.mzn";
include "disjunctive.mzn";
include "fzn_cumulative.mzn";
include "fzn_cumulative_reif.mzn";
include "./mc_fzn_cumulative.mzn";

predicate my_cumulative(int: n_circuits,
                        array[int] of var int: x,
                        array[int] of var int: y,
                        array[int] of var int: heights,
                        array[int] of var int: widths, 
                        var int: width_boundary) =

    % checking if y, heights and widths have the same index set (corresponding to the set of tasks)                   
    assert(index_set(y) == index_set(heights) /\ index_set(y) == index_set(widths),
        "cumulative: the 3 array arguments must have identical index sets",
      
    % checking that all length and width values are positive
    if length(y) >= 1 then
    assert(lb_array(heights) >= 0 /\ lb_array(widths) >= 0,
        "cumulative: heights and widths must be non-negative",
      
    % checking if we can place more than one plate in x axis
    if  
       let { int: min_width = lb_array(widths); 
             int: min_width_idx = arg_min([ lb(widths[i]) | i in index_set(widths) ]) } in
       forall(i in index_set(widths))
             (is_fixed(widths[i]) /\ (fix(widths[i]) + min_width > ub(width_boundary) \/ i = min_width_idx))
    then
         % no parallel plates => (if all heights=1 then all_different, else disjunctive)          
         if forall(i in index_set(heights))(is_fixed(heights[i]) /\ fix(heights[i]) == 1)
         then
            all_different(y)
         else
            disjunctive(y, heights)
         endif
    
    % we can place more than one plate on x axis
    else
       my_fzn_cumulative(n_circuits, x, y, heights, widths, width_boundary)
    endif
    )
    endif);