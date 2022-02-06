include "globals.mzn";

predicate my_fzn_cumulative(int: n_plates,
                            array[int] of var int: x,
                            array[int] of var int: y,
                            array[int] of var int: lengths,
                            array[int] of var int: widths, 
                            var int: b) =
        let {
            set of int: PLATES = 
                {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 }
        } in
            if 0==card(PLATES) then /*true*/ 0==card(index_set(y)) \/ b>=0
            else
                let {
                    int: early = min([ lb(y[i])                  | i in PLATES ]), 
                    int: late  = max([ ub(y[i]) + ub(lengths[i]) | i in PLATES ]) 
                } in (
                    if late - early > 5000 then
                      fzn_cumulative_task(n_plates, x, y, lengths, widths, b)
                    else
                      fzn_cumulative_time(n_plates, x, y, lengths, widths, b)
                    endif
                )
            endif
            ;


predicate fzn_cumulative_time(int: n_plates,
                              array[int] of var int: x,
                              array[int] of var int: y,
                              array[int] of var int: lengths,
                              array[int] of var int: widths, 
                              var int: b) =
    let { 
         set of int: PLATES = 
            {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 },
            
        int: y_min = min([ lb(y[p]) | p in PLATES ]), 
        int: y_max  = max([ ub(y[p]) + ub(lengths[p]) | p in PLATES ]),
        var int: y_sum = sum(p in PLATES)(y[p])
    } in (
        forall( l in y_min..y_max ) (
            let{
                array[int] of var int: is_plate_at_l = [
                    bool2int(y[p] <= l /\ l < y[p] + lengths[p]) | p in PLATES
                    ]
            } in
                forall(i,j in PLATES where i<j /\ is_plate_at_l[i]==1 /\ is_plate_at_l[j]==1)(
                    x[i] + widths[i] <= x[j] \/ x[j] + widths[j] <= x[i]
                )
        ) /\
        forall(p in PLATES)(x[p] + widths[p] <= b) 
        /\
        lex_lesseq(x, [b - x[p] - widths[p] | p in PLATES]) 
        /\
        lex_lesseq(y, [y_sum - y[p] - lengths[p] | p in PLATES])
    );

% to change (but not used, check why)
predicate fzn_cumulative_task(int: n_plates,
                              array[int] of var int: x,
                              array[int] of var int: y,
                              array[int] of var int: lengths,
                              array[int] of var int: widths, 
                              var int: b) =
    let {
        set of int: PLATES = 
            {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 },
        var int: y_sum = sum(p in PLATES)(y[p])
    } in (
        forall( j in PLATES ) ( 
            b >= widths[j] + sum( i in PLATES where i != j ) ( 
                bool2int(y[i] <= y[j] /\ y[j] < y[i] + lengths[i] ) * widths[i]
        ) /\
        forall(p in PLATES)(x[p] + widths[p] <= b) 
        /\
        lex_lesseq(x, [b - x[p] - widths[p] | p in PLATES]) 
        /\
        lex_lesseq(y, [y_sum - y[p] - lengths[p] | p in PLATES])
        )
    );