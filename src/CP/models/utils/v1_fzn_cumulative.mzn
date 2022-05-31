include "globals.mzn";

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

predicate v1_fzn_cumulative(array[int] of var int: x,
                         array[int] of var int: y,
                         array[int] of var int: heights,
                         array[int] of var int: widths, 
                         var int: width_boundary) =
        let {
            set of int: CIRCUITS = 
                {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(heights[i]) > 0 }
        } in
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
         set of int: CIRCUITS = 
            {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(heights[i]) > 0 },
            
        int: y_min  = min([ lb(y[c]) | c in CIRCUITS ]),
        int: y_max  = max([ ub(y[c]) + ub(heights[c]) | c in CIRCUITS ]),
        var int: y_sum = sum(c in CIRCUITS)(y[c])
    } in (
        % for each height check if the circuits at that height do not overlap
        forall( h in y_min..y_max ) (
            let{
                % array of circuits at height = h
                array[int] of var int: is_plate_at_h = [
                    bool2int(y[c] <= h /\ h < y[c] + heights[c]) | c in CIRCUITS
                    ]
            } in
                forall(i,j in CIRCUITS where i<j /\ is_plate_at_h[i]==1 /\ is_plate_at_h[j]==1)(
                    x[i] + widths[i] <= x[j] \/ x[j] + widths[j] <= x[i]
                )
        ) /\
        % for each circuit check if they do not pass the width boundary
        forall(p in CIRCUITS)(x[p] + widths[p] <= width_boundary) 
        % /\
        % remove horizontal symmetry
        % lex_lesseq(x, [width_boundary - x[p] - widths[p] | p in CIRCUITS]) 
        % /\
        % remove vertical simmetry
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