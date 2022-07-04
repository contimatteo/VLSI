% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% ann: ann_search_x = int_search(x, input_order, indomain_min);
ann: ann_search_x = int_search(x, first_fail, indomain_min);
% ann: ann_search_x = int_search(x, dom_w_deg, indomain_min);
% ann: ann_search_x = int_search(x, input_order, indomain_random);
% ann: ann_search_x = int_search(x, first_fail, indomain_random);
% ann: ann_search_x = int_search(x, dom_w_deg, indomain_random);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% ann: ann_search_y = int_search(y, input_order, indomain_min);
ann: ann_search_y = int_search(y, first_fail, indomain_min);
% ann: ann_search_y = int_search(y, dom_w_deg, indomain_min);
% ann: ann_search_y = int_search(y, input_order, indomain_random);
% ann: ann_search_y = int_search(y, first_fail, indomain_random);
% ann: ann_search_y = int_search(y, dom_w_deg, indomain_random);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


ann: ann_search_makespan = int_search([ makespan ], input_order, indomain_min);


% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %


% ann: ann_restart = restart_constant(100);
ann: ann_restart = restart_linear(1000);
% ann: ann_restart = restart_geometric(1.5,100)
% ann: ann_restart = restart_luby(100);
% ann: ann_restart = restart_none;
