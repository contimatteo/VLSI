include "all_different.mzn";
include "disjunctive.mzn";
% include "fzn_cumulative.mzn";
include "fzn_cumulative_reif.mzn";
include "./v1_fzn_cumulative.mzn";


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate v1_cumulative(array[CIRCUITS] of var Xs: x,
                        array[CIRCUITS] of var Ys: y,
                        array[CIRCUITS] of int: heights, % array[CIRCUITS] of HEIGHTS: heights,
                        array[CIRCUITS] of WIDTHS: widths, 
                        int: width_boundary) =

    (
        %%% check if we can place more than one circuit on the same `x` axis value
        if  
            let { 
                int: min_width = min(widths); 
                int: min_width_idx = arg_min(widths);
                set of int: circuits = index_set(widths); 
            }
            %%% check if the sum(current_c_width, min_width) is greater than the global width boundary
            %%% `c = min_width_idx` is for skipping the circuit with the minimum width
            in forall(c in circuits)
                ( widths[c] + min_width > width_boundary \/ c = min_width_idx )
        
        %%% we have to stack each circuit on top of the other ones
        then
            %%% all circuits must have `x` equal to zero
            forall(x_i in x) (x_i == 0) 
            /\
            %%% check if all circuits have the `height` equal to 1
            if forall(h in heights) (h == 1)
            then
                all_different(y)
            else
                disjunctive(y, heights)
            endif
        
        %%%  we can place more than one circuit on the same `x` axis value
        else
            v1_fzn_cumulative(x, y, heights, widths, width_boundary)
        endif
    );
