%%
%%
%% SIMMETRY (soluzioni uguali da non considerare)
%%  1. tutti i circuiti uguali (x,y) 
%%
%%  2. 2.1 + 2.2
%%      2.1 tutti i circuiti alti uguali (x) + che scambiati non violano il `my_cumulative_partial`
%%      2.2 tutti i circuiti alti uguali (y) + che scambiati non violano il `my_cumulative_partial`
%%
%%  3. ogni coppia di circuti (c1, c2) adiacenti e con la stessa altezza, iteriamo su ogni circuito diverso da (c1,c2):
%%      3.1 tutti i circuiti con altezza uguale a c1/c2 + che scambiati non violano il `my_cumulative_partial`
%%


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

predicate switch_pos(x, c1, c2, new_x) = (
    % ISSUE: funziona solo per i circuiti non adiacenti!
    % se `c1` e `c2` sono adiacenti devo scambiarli in modo più intelligente.
    % --> devo far partire la nuova posizione di `c1` da `x[c2] + length[c2]`

    if are_adjacent(c1, c2)
    then:
        % ...
    else:
        % questo funziona solo se `c1` e `c2` NON sono adiacenti.
        let x_tmp = x[c1];
        new_x[c1] = x[c2];
        new_x[c2] = x_tmp;    
)


predicate my_cumulative_partial(c1, c2, max_w) = (
    % `is_circuit_at_h` have to be computed.

    forall(j in CIRCUITS where c1 != j /\ is_circuit_at_h[c1] == 1)(
        x[c1] + widths[c1] <= x[j] /\ x[c1] + widths[c1] <= max_w
    )

    forall(j in CIRCUITS where c2 != j /\ is_circuit_at_h[c2] == 1)(
        x[c2] + widths[c2] <= x[j] /\ + widths[c2] <= max_w
    )
)

%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% 2.1
constraint forall (c1,c2 in PLATES_with_same_y where c1 != c2)
                  (
                    switch_pos(x, y, c1,c2, new_x, new_y);
                    my_cumulative_partial(new_x, new_y, ....) --> c1,c2 simmetrici!
                  )

%% 2.2
constraint forall (c1,c2 in PLATES_with_same_y where c1 != c2)
                  (
                    switch_pos(x, y, c1,c2, new_x, new_y);
                    my_cumulative_partial(new_x, new_y, ....) --> c1,c2 simmetrici!
                  )



%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%  
%%  
%% SIMMETRY (soluzioni uguali da non considerare)
%%  
%%  1. tutti i circuiti alti e lunghi uguali (salvarsi quelli uguali in una struttura dati)
%%  
%%  2. tutti i circuiti ALTI uguali e adiacenti (consecutivi sull'assse `x`) --> non considerati al punto 1
%%  3. tutti i circuiti LUNGHI uguali e adiacenti (consecutivi sull'assse `y`) --> non considerati al punto 1
%%  
%%  4. tutti i circuiti ALTI uguali , non adiacenti, che scambiati non violano `my_cumulative_partial` --> non considerati al punto 1
%%  5. tutti i circuiti LUNGHI uguali , non adiacenti, che scambiati non violano `my_cumulative_partial` --> non considerati al punto 1
%%  
%%  


%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%  
%%  
%% SIMMETRY (miglioramenti) (soluzioni uguali da non considerare)
%%  
%%  6. mergiare a turno tutte le coppie di circuiti `c1` e `c2` ALTI uguali e adiacenti 
%%     (consecutivi sull'assse `x`) e applicare tutti i punti (1-4)
%%
%%  7. mergiare a turno tutte le coppie di circuiti `c1` e `c2` LUNGHI uguali e adiacenti 
%%     (consecutivi sull'assse `y`) e applicare tutti i punti (1-4)
%%  
%%  

