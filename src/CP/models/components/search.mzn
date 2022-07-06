%%% https://www.minizinc.org/doc-2.5.5/en/fzn-spec.html

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


ann: ann_search_x = int_search(x, input_order, indomain_min);
% ann: ann_search_x = int_search(x, input_order, indomain);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


ann: ann_search_y = int_search(y, input_order, indomain_min);
% ann: ann_search_y = int_search(y, input_order, indomain);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% ann: ann_search_makespan = int_search([ makespan ], input_order, indomain_min);
% ann: ann_search_makespan = int_search([ makespan ], input_order, indomain_max);
ann: ann_search_makespan = int_search([ makespan ], input_order, indomain_split);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% ann: ann_restart = restart_geometric(2, 50)
ann: ann_restart = restart_luby(150);
% ann: ann_restart = restart_none;
