include "globals.mzn";

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

predicate v1_fzn_cumulative(array[CIRCUITS] of var Xs: x,
                            array[CIRCUITS] of var Ys: y,
                            array[CIRCUITS] of int: heights, % array[CIRCUITS] of HEIGHTS: heights,
                            array[CIRCUITS] of WIDTHS: widths, 
                            var int: width_boundary) =
        
        % if cardinality of CIRCUITS==0 then cardinality of y==0 or width_boundary>=0
        if 0==card(CIRCUITS) then /*true*/ 0==card(index_set(y)) \/ width_boundary>=0
        else
            let {
                int: lowest   = min([ lb(y[i])                  | i in CIRCUITS ]),
                int: highest  = max([ ub(y[i]) + ub(heights[i]) | i in CIRCUITS ])
            } in (
                % if highest - lowest > 5000 then fzn_cumulative_task(n_circuits, x, y, heights, widths, width_boundary)
                % else fzn_cumulative_time(n_circuits, x, y, heights, widths, width_boundary)
                % endif
                fzn_cumulative_time(x, y, heights, widths, width_boundary)
            )
        endif
        ;


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


predicate fzn_cumulative_time(array[int] of var int: x,
                              array[int] of var int: y,
                              array[int] of var int: heights,
                              array[int] of var int: widths, 
                              var int: width_boundary) =
    let { 
        int: y_min  = min([ lb(y[c]) | c in CIRCUITS ]),
        int: y_max  = max([ ub(y[c]) + ub(heights[c]) | c in CIRCUITS ]),
        var int: y_sum = sum(c in CIRCUITS)(y[c])
    } in (
        %%% for each height check if the circuits at that height do not overlap
        forall( h in y_min..y_max ) (
            let{
                %%% array of circuits at height = h
                % array[int] of var int: is_circuit_at_height = [
                %     bool2int(y[c] <= h /\ h < y[c] + heights[c]) | c in CIRCUITS
                % ]
                array[CIRCUITS] of var bool: is_circuit_at_height = [
                    y[c] <= h /\ h < y[c] + heights[c] | c in CIRCUITS
                ],
                array[int] of var opt int: circuits_at_height_h = [ c | c in CIRCUITS where is_circuit_at_height[c] ]
            } in
                forall(c1,c2 in circuits_at_height_h where c1<c2 )(
                    x[c1] + widths[c1] <= x[c2] \/ x[c2] + widths[c2] <= x[c1]
                )
                % forall(i,j in CIRCUITS where x[i]<x[j] /\ is_circuit_at_height[i] /\ is_circuit_at_height[j])(
                %     x[i] + widths[i] <= x[j]
                % )
        ) /\
        %%% for each circuit check if they do not pass the width boundary
        forall(p in CIRCUITS)(x[p] + widths[p] <= width_boundary) 
        % /\
        %%% remove horizontal symmetry
        % lex_lesseq(x, [width_boundary - x[p] - widths[p] | p in CIRCUITS]) 
        % /\
        %%% remove vertical simmetry
        % lex_lesseq(y, [y_sum - y[p] - heights[p] | p in CIRCUITS])
    );


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% % to change (but not used, check why)
% predicate fzn_cumulative_task(int: n_circuits,
%                               array[int] of var int: x,
%                               array[int] of var int: y,
%                               array[int] of var int: heights,
%                               array[int] of var int: widths, 
%                               var int: width_boundary) =
%     let {
%         set of int: CIRCUITS = 
%             {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(heights[i]) > 0 },
%         var int: y_sum = sum(p in CIRCUITS)(y[p])
%     } in (
%         forall( j in CIRCUITS ) ( 
%             width_boundary >= widths[j] + sum( i in CIRCUITS where i != j ) ( 
%                 bool2int(y[i] <= y[j] /\ y[j] < y[i] + heights[i] ) * widths[i]
%         ) /\
%         forall(p in CIRCUITS)(x[p] + widths[p] <= width_boundary) 
%         /\
%         lex_lesseq(x, [width_boundary - x[p] - widths[p] | p in CIRCUITS]) 
%         /\
%         lex_lesseq(y, [y_sum - y[p] - heights[p] | p in CIRCUITS])
%         )
%     );