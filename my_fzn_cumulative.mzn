include "disjunctive.mzn";

predicate my_fzn_cumulative(int: n_plates,
                            array[int, int] of var int: pos,
                            array[int] of var int: lengths,
                            array[int] of var int: widths, 
                            var int: b) =
        let {
            array[int] of var int: y = [pos[i, 1] | i in 1..n_plates], 
            set of int: Tasks = 
                {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 }
        } in
            if 0==card(Tasks) then /*true*/ 0==card(index_set(y)) \/ b>=0
            else
                let {
                    int: early = min([ lb(y[i])                  | i in Tasks ]), 
                    int: late  = max([ ub(y[i]) + ub(lengths[i]) | i in Tasks ]) 
                } in (
                    if late - early > 5000 then
                      fzn_cumulative_task(n_plates, pos, lengths, widths, b)
                    else
                      fzn_cumulative_time(n_plates, pos, lengths, widths, b)
                    endif
                )
            endif
            ;


predicate fzn_cumulative_time(int: n_plates,
                              array[int, int] of var int: pos,
                              array[int] of var int: lengths,
                              array[int] of var int: widths, 
                              var int: b) =
    let {
         array[int] of var int: x = [pos[i, 2] | i in 1..n_plates],
         array[int] of var int: y = [pos[i, 1] | i in 1..n_plates], 
         set of int: Tasks = 
            {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 },
        int: early = min([ lb(y[i]) | i in Tasks ]), 
        int: late  = max([ ub(y[i]) + ub(lengths[i]) | i in Tasks ]) 
    } in (
        forall( l in early..late ) (
            let{
                array[int] of var int: is_task_at_l = [
                    bool2int(y[t] <= l /\ l < y[t] + lengths[t]) | t in Tasks
                    ]
            } in
                b >= sum( t in Tasks ) (
                    is_task_at_l[t] * widths[t]
                ) /\
                forall(i,j in Tasks where i<j /\ is_task_at_l[i]==1 /\ is_task_at_l[j]==1)(
                    x[i] + widths[i] <= x[j] \/ x[j] + widths[j] <= x[i]
                    )
        )
    );

% to change (but not used, check why)
predicate fzn_cumulative_task(int: n_plates,
                             array[int, int] of var int: pos,
                             array[int] of var int: lengths,
                             array[int] of var int: widths, 
                             var int: b) =
    let {
        array[int] of var int: x = [pos[i, 2] | i in 1..n_plates],
        array[int] of var int: y = [pos[i, 1] | i in 1..n_plates], 
        set of int: Tasks = 
            {i | i in index_set(y) where ub(widths[i]) > 0 /\ ub(lengths[i]) > 0 }
    } in (
        forall( j in Tasks ) ( 
            b >= widths[j] + sum( i in Tasks where i != j ) ( 
                bool2int(y[i] <= y[j] /\ y[j] < y[i] + lengths[i] ) * widths[i]
            ) /\
        forall( t in Tasks ) (
            2 == x[t]
            )
        )
    );