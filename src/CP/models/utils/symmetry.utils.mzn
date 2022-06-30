
%%%  array of horizontal dimension of virtual ciruits
function var int: vc_width (V_CIRCUITS: vc_index) = (
    %%%  if c1 on the right -> x[c1]+widths[c1]-x[c2]
    if x[c_pairs[1,vc_index]]>x[c_pairs[2,vc_index]] 
    then x[c_pairs[1,vc_index]] + widths[c_pairs[1,vc_index]] - x[c_pairs[2,vc_index]] 
    else 
        %%% if c1 on the left -> x[c2]+widths[c2]-x[c1]
        if x[c_pairs[1,vc_index]]<x[c_pairs[2,vc_index]]
        then x[c_pairs[2,vc_index]] + widths[c_pairs[2,vc_index]] - x[c_pairs[1,vc_index]]
        else 
            %%% if c1 and c2 with same x, check who is higher
            %%%  maybe better to choose the max width
            if y[c_pairs[1,vc_index]]>y[c_pairs[2,vc_index]]
            then widths[c_pairs[1,vc_index]]
            else widths[c_pairs[2,vc_index]]
            endif
        endif 
    endif
);


function var int: vc_height (V_CIRCUITS: vc_index) = (
    %%%  if c1 on the top -> y[c1]+heights[c1]-y[c2]
    if y[c_pairs[1,vc_index]]>y[c_pairs[2,vc_index]] 
    then y[c_pairs[1,vc_index]] + heights[c_pairs[1,vc_index]] - y[c_pairs[2,vc_index]] 
    else 
        %%% if c1 on the bottom -> y[c2]+heights[c2]-y[c1]
        if y[c_pairs[1,vc_index]]<y[c_pairs[2,vc_index]]
        then y[c_pairs[2,vc_index]] + heights[c_pairs[2,vc_index]] - y[c_pairs[1,vc_index]]
        else 
            %%% if c1 and c2 with same y, check who is on the right
            if x[c_pairs[1,vc_index]]>x[c_pairs[2,vc_index]]
            then heights[c_pairs[1,vc_index]]
            else heights[c_pairs[2,vc_index]]
            endif
        endif 
    endif
);

function var int: vc_x (V_CIRCUITS: vc_index) = (
    min(x[c_pairs[1,vc_index]], x[c_pairs[2,vc_index]])
);

function var int: vc_y (V_CIRCUITS: vc_index) = (
    min(y[c_pairs[1,vc_index]], y[c_pairs[2,vc_index]])
);


function var bool: vc_is_valid (V_CIRCUITS: vc_index) = (
    %%%  check only circuits starting on the bottom left of the top right corner
    forall(c in CIRCUITS where x[c]<vc_x(vc_index)+vc_width(vc_index) /\ y[c]<vc_y(vc_index)+vc_height(vc_index))(                
        %%%  if bottom left corner of c is inside, all the circuit must be inside
        if x[c]>=vc_x(vc_index) /\ y[c]>=vc_y(vc_index)
        then x[c]+widths[c]<=vc_x(vc_index)+vc_width(vc_index) /\ y[c]+heights[c]<=vc_y(vc_index)+vc_height(vc_index)
        %%%  otherwise all the circuit must be outside
        else x[c]+widths[c]<=vc_x(vc_index) \/ y[c]+heights[c]<=vc_y(vc_index)                    
        endif
    )
);


function var int: rv_width (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_width(c_index - n_circuits)
        else widths[c_index]
    endif
);

function var int: rv_height (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_height(c_index - n_circuits)
        else heights[c_index]
    endif
);

function var Xs: rv_x (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_x(c_index - n_circuits)
        else x[c_index]
    endif
);

function var Ys: rv_y (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_y(c_index - n_circuits)
        else y[c_index]
    endif
);

function var bool: rv_is_valid (RV_CIRCUITS: c_index) = (
    if c_index > n_circuits
        then vc_is_valid(c_index - n_circuits)
        else true
    endif
);


% %%% merged info
% array[1..tot_circuits] of var bool: tot_is_valid = [true | c in CIRCUITS] ++ is_valid;
% %%%  check for each circuit c if it's composed by precedent circuits c1, c2
% %%%  if composed by 2 precedent circuits c1, c2
% %%%  and they have same height -> cannot swap c in horizontal dim
% %%%  ande they have same width -> cannot swap c in vertical dim

% %%%  remove swapping (same size circuits) (with abs)
% constraint forall(c1,c2 in 1..n_circuits where c1<c2)(
%     if 
%         tot_widths[c1] == tot_widths[c2] /\ tot_heights[c1] == tot_heights[c2] 
%         /\ 
%         tot_is_valid[c1] /\ tot_is_valid[c2] 
%         /\
%         not (tot_x[c1]==tot_x[c2] /\ tot_y[c1]==tot_y[c2])
%     then 
%         if abs(tot_x[c1] - tot_x[c2]) >= tot_widths[c1]
%         then tot_x[c1] < tot_x[c2]
%         else 
%             if abs(tot_y[c1] - tot_y[c2]) >= tot_heights[c1]
%             then tot_y[c1] < tot_y[c2]
%             else true
%             endif
%         endif
%     else true
%     endif
% );


% % %%%  remove swapping (same size circuits) (whithout abs)
% % constraint forall(c1,c2 in 1..tot_circuits where 
% % c1<c2)(
% %     if 
% %         tot_widths[c1] == tot_widths[c2] /\ tot_heights[c1] == tot_heights[c2] 
% %         /\ 
% %         tot_is_valid[c1] /\ tot_is_valid[c2] 
% %         /\
% %         not (tot_x[c1]==tot_x[c2] /\ tot_y[c1]==tot_y[c2])
% %     then 
% %         %if abs(tot_x[c1] - tot_x[c2]) >= tot_widths[c1] 
% %         if (tot_x[c1] > tot_x[c2]) /\ (tot_x[c1] - tot_x[c2] >= tot_widths[c2]) %CASE: constraint on x axis with c2 left of c1
% %         then tot_x[c1] > tot_x[c2]
% %         else 
% %             if (tot_x[c1] < tot_x[c2]) /\ (tot_x[c2] - tot_x[c1] >= tot_widths[c1]) %CASE: constraint on x axis with c2 right of c1
% %             then tot_x[c1] < tot_x[c2]
% %             else
% %                 %if abs(tot_y[c1] - tot_y[c2]) >= tot_heights[c1]
% %                 if (tot_y[c1] > tot_y[c2]) /\ (tot_y[c1] - tot_y[c2] >= tot_heights[c2]) %CASE: costraint on y axis with c1 above c2
% %                 then tot_y[c1] > tot_y[c2]
% %                 else 
% %                     if (tot_y[c1] < tot_y[c2]) /\ (tot_y[c2] - tot_y[c1] >= tot_heights[c1]) %CASE: constraint on y axis with c1 under c2
% %                     then tot_y[c1] < tot_y[c2]
% %                     else true
% %                     endif
% %                 endif
% %             endif
% %         endif
% %     else true
% %     endif
% % );

% % %%% impose an ordering constraint for each couple of real circuits that is swappable in a virtual circuit
% %  constraint forall (vc in 1..n_v_circuits where tot_is_valid[vc])( 
% %     forall (c1,c2 in 1..n_circuits where
% %         c1 < c2 /\
% %         %c1 != vc /\
% %         %c2 != vc /\

% %         tot_x[c1] >= tot_x[vc] /\ 
% %         tot_x[c1] < tot_x[vc] + tot_widths[vc] /\ %%% no need to check if c1 fits in vc: vc is valid
% %         tot_y[c1] >= tot_y[vc] /\
% %         tot_y[c1] < tot_y[vc]+ tot_heights[vc] /\
            
% %         tot_x[c2] >= tot_x[vc] /\ 
% %         tot_x[c2] < tot_x[vc] + tot_widths[vc] /\
% %         tot_y[c2] >= tot_y[vc] /\
% %         tot_y[c2] < tot_y[vc]+ tot_heights[vc]
            
% %     )( 
% %         if (tot_y[c1] = tot_y[c2] /\ tot_heights[c1] = tot_heights[c2]) %CASE: aligned along x axis with c2 left of c1
% %         then tot_x[c1] < tot_x[c2]
% %         else 
% %                 if (tot_x[c1] = tot_x[c2] /\ tot_widths[c1] = tot_widths[c2]) %CASE: aligned along on y axis with c1 above c2
% %                 then tot_y[c1] < tot_y[c2]
% %                 else true
% %                 endif
% %         endif
% %     %)    
% % ));

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %

% %constraint makespan=min_makespan;
% %solve satisfy;
% % solve minimize makespan;

% ann: search_makespan = int_search([ makespan ], input_order, indomain_min);
% ann: search_y = int_search(y, first_fail, indomain_min);

% solve 
%     ::seq_search([ search_makespan, search_y ])
%     minimize makespan;

% output [
%     "width = ", show(width), "\n",
%     "n_circuits = ", show(n_circuits), "\n",
%     "dims = ", show(dims), "\n",
%     "widths = ", show(widths), "\n",
%     "heights = ", show(heights), "\n",
%     "x = ", show(x), "\n",
%     "y = ", show(y), "\n",
%     "min_makespan = ", show(min_makespan), "\n",
%     "max_makespan = ", show(max_makespan), "\n",
%     "makespan = ", show(makespan), "\n",
%     "n_v_circuits = ", show(n_v_circuits), "\n",
%     "c_pairs = ", show(c_pairs), "\n",
%     "c_pairs c1 = ", show([c_pairs[1,i] | i in V_CIRCUITS]), "\n",
%     "c_pairs c2 = ", show([c_pairs[2,i] | i in V_CIRCUITS]), "\n",
%     "tot_widths = ", show(tot_widths), "\n",
%     "tot_heights = ", show(tot_heights), "\n",
%     "tot_x = ", show(tot_x), "\n",
%     "tot_y = ", show(tot_y), "\n",
%     "tot_is_valid = ", show(tot_is_valid), "\n"
% ];
