include "all_different.mzn";
include "disjunctive.mzn";
% include "fzn_cumulative.mzn";
include "fzn_cumulative_reif.mzn";
include "./v1_fzn_cumulative.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate v1_cumulative(array[int] of var int: x,
                        array[int] of var int: y,
                        array[int] of int: heights,
                        array[int] of int: widths, 
                        int: width_boundary) =

    (
        % checking if we can place more than one plate in x axis
        if  
            let { 
                int: min_width = min(widths); 
                int: min_width_idx = arg_min(widths) 
            } 
            in 
                forall(i in index_set(widths))
                    % (is_fixed(widths[i]) /\ (fix(widths[i]) + min_width > ub(width_boundary) \/ i = min_width_idx))
                    ( widths[i] + min_width > width_boundary \/ i = min_width_idx )
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
            v1_fzn_cumulative(x, y, heights, widths, width_boundary)
        endif
    );
