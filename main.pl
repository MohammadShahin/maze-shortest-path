/*
 * AI first assignment, by Mohammad Shahin on March 16 2021.
 * The actor starts from cell (0, 0).
 * Use 'rand(N)' to generate a random map of size N * N, then all optimal solution (if there any any)
 * will be printed.
 * Use 'test(N, [Xcovid1, Ycovid1], [Xcovid2, Ycovid2], [Xdoc, Ydoc], [Xhome, Yhome], [Xmask, Ymask])' 
 * to run the algorithms with specific data about the objects.
 bla bla bla
*/

 % The positions of the four types of agents are declared as dynamic procedures.
 % All of them accept two parameter (say, X and Y), and they are true only when the positions actaully 
 % is what the name of the procedure suggests. For example, home(X, Y) gives true only for the home's 
 % coordinates. 
 % They are defined as dynamic since they are randomly chosen during the execution of the program.

:- dynamic covid/2.
:- dynamic doctor/2.
:- dynamic home/2.
:- dynamic mask/2.

 % The final asnwers of the problem are also defined as dynamic procedures, since their values change
 % as the program runs.
 % 'optimalPaths(L)', where L is a path that the actor should follow to reach home with the minimum 
 % number of steps. Please note that all optimal paths are generated. 
 % 'optimalPathLength(Len)', where Len is the number of cells the actor has to go through to reach 
 % home using one of the optimal paths.
 % '1' in 'optimalPaths1' and 'optimalPathLength1' indicates that these variables are used for the
 % backtracking approach, while '2' is used for the breadth-first search approach.

:- dynamic optimalPaths1/1.
:- dynamic optimalPathLength1/1.

:- dynamic optimalPaths2/1.
:- dynamic optimalPathLength2/1.


% A helper procedure for accessing the reachable cells in the breadth-first search approach.
:- dynamic children/2.

 % 'GenerateCovid(N)' is used to generate a Covid agent at some random cell in a map of size N % N.
 % There are no rules restricting how covid agents' postions are chosen, and they are generated 
 % firstly.

generateCovid(N) :-
    random(0, N, X),
    random(0, N, Y),
    show("Covid", X, Y),
    assert(covid(X, Y)).

 % 'GenerateDoctor(N)' is used to generate a Doctor at some random cell in a map of size N*N.
 % It follows the condition that Doctor cannot be inside the Covid zone.

generateDoctor(N) :-
    random(0, N, X),
    random(0, N, Y),
    ((\+covidZone(X, Y), show("Doc", X, Y), assert(doctor(X, Y))); (generateDoctor(N))).

 % 'GenerateHome(N)' is used to generate a Home at some random cell in a map of size N*N.
 % It follows the conditions that Home cannot be inside the Covid infected cells.

generateHome(N) :-
    random(0, N, X),
    random(0, N, Y),
    ((\+covidInfectedCell(X, Y), show("Home", X, Y), assert(home(X, Y))); (covidInfectedCell(X, Y), 
                                                                          generateHome(N))).

 % 'GenerateMask(N)' is used to generate a Mask at some random cell in a map of size N*N.
 % It follows the condition that Mask cannot be inside the Covid zone.

generateMask(N) :-
    random(0, N, X),
    random(0, N, Y),
    ((\+covidZone(X, Y), show("Mask", X, Y), assert(mask(X, Y))); (covidZone(X, Y), generateMask(N))).

% 'allDirections' contains all possible moves.

allDirections(-1, -1).
allDirections(-1, 0).
allDirections(-1, 1).
allDirections(0, -1).
allDirections(0, 1).
allDirections(1, -1).
allDirections(1, 0).
allDirections(1, 1).

% 'covidInfectedCell' decides whether some cell (X, Y) is covid infected or not.

covidInfectedCell(X, Y) :-
    covid(X, Y) ; \+forall(allDirections(I, J), (Xnew is X + I, Ynew is Y + J,\+covid(Xnew, Ynew))).

% 'covidZone' decides whether some cell (X, Y) is covid zone or not.

covidZone(X, Y) :-
    covid(X, Y) ; \+forall(allDirections(I, J), (Xnew is X + I, Ynew is Y + J,\+covid(Xnew, Ynew))).

% A procedure added for showing details about the map.
show(T, X, Y) :-
    write(T), write(" at "), write(X), write(" , "), writeln(Y), true.

% A helper procedure for finding the maximum value among two values A and B.
max(A, B, C) :-
    (A > B -> C = A ; C = B).

% A procedure to check if the current cell is inside the map.
inMap(X, Y, N) :-
	X >= 0,
    N > X,
    Y >= 0,
    N > Y.

% A method to update the answers for the backtracking approach.
updateAnswer1(CurPath) :-
    length(CurPath, CurLength), optimalPathLength1(OptLength), 
    (CurLength < OptLength -> (
                              retract(optimalPathLength1(OptLength)), 
                              retractall(optimalPaths1(_)), 
                              assert(optimalPathLength1(CurLength)),
                                  assert(optimalPaths1(CurPath))
                              ) 
    ; true), false.

% A method to update the answers for the breadth-first search approach.
updateAnswer2(CurPath) :-
    length(CurPath, CurLength), optimalPathLength2(OptLength), 
    (CurLength < OptLength -> (
                              retract(optimalPathLength2(OptLength)), 
                              retractall(optimalPaths2(_)), 
                              assert(optimalPathLength2(CurLength)),
                                  assert(optimalPaths2(CurPath))
                              ) 
    ; true), false.


% A method to find the path from cell (X, Y) to home directly.
goHome(X, Y, Path) :-
    (home(X, Y) -> Path = [[X, Y]]
    	; ( home(Xhome, Yhome),
            (Xhome > X -> I = 1; (Xhome < X ->  I = -1; I = 0)),
            (Yhome > Y -> J = 1; (Yhome < Y ->  J = -1; J = 0)),
            Xnew is X + I, Ynew is Y + J,
            goHome(Xnew, Ynew, Path2),
            append([[X, Y]], Path2, Path)
      	  )
    ).
    

% The main procedure for traversing the map using backtracking approach. 
backtrack(X, Y, N, CurrentPath) :-
    
    % To check if the current cell is not off the map.
    inMap(X, Y, N),
    
    % To check if the current cell is valid (the actor can pass through it). 
    \+covidZone(X, Y),
    
    % There is no need to visit some cell twice while going in some path.
    \+member([X, Y], CurrentPath),
    
    % 'NewCurrentPath' is the new varaible for current path (to be sent in the next steps). 
    append(CurrentPath, [[X, Y]], NewCurrentPath),
   	
    % If the current path in the best cases will not result in a better solution than the optimal one so
    % far, then there is no need to go even deeper in it. 
    ((length(NewCurrentPath, CurLength), home(Xhome, Yhome), abs(Xhome - X, Xdif), abs(Yhome - Y, Ydif),
      max(Xdif, Ydif, DisHome), BestCase is DisHome + CurLength, optimalPathLength1(OptLength),
      BestCase > OptLength) 
     -> false; true),
    
    % If the current cell is home, then the goal is reached and the final answers are changed if the 
    % new found path is better than the current optimal one(s).
    (home(X, Y) -> updateAnswer1(NewCurrentPath); true),
    
    % If the current cell is doctor or mask, then now the actor can go directly to home because Covid
    % does not affect anymore. So we take the shortest path from the current cell to home (this is 
    % an optimization to improve the performance).
    ((doctor(X, Y) ; mask(X, Y)) -> (
                     goHome(X, Y, Lst),
                     append(CurrentPath, Lst, PathHome),
                     updateAnswer1(PathHome)
                   )
    ; true),
    
    % Finally, we proceed with the backtracking by trying every possible direction. 
    forall(allDirections(I, J), 
           ((Xnew is X + I, Ynew is Y + J, backtrack(Xnew, Ynew, N, NewCurrentPath))
           ; true)).

% A helper procedure for updating the queue in the breadth-first search approach.
consed( A, B, [B|A]).

% The main procedure for traversing the map using breadth-first search approach. 
bfs([Visited|Rest], N) :- 
    Visited = [[Xcur, Ycur]|_],
	% show("", Xcur, Ycur),
    
    % If the current cell is home, then the goal is reached and we know for sure that the current path
    % is the best among all the others, so no need to look for other paths.
    (home(Xcur, Ycur) -> (reverse(Visited, Path), updateAnswer2(Path)) ; true),
    
	% If the current path is longer than the optimal path found so far, then there will be no shorter
    % paths, since it is a bfs approach.
    ((length(Visited, CurLength), optimalPathLength2(OptLength), CurLength > OptLength) 
     -> false ; true),
    
    % If the current cell is doctor or mask, then now the actor can go directly to home because Covid
    % does not affect them anymore. So we take the shortest path from the current cell to home (this 
    % is an optimization to improve the performance).
    ((doctor(Xcur, Ycur) ; mask(Xcur, Ycur)) -> (
                     goHome(Xcur, Ycur, Lst),
                     Lst = [_|Lst2],
                     reverse(Visited, CurrentPath),                        
                     append(CurrentPath, Lst2, PathHome),
                     (updateAnswer2(PathHome) ; true)
                   )
    ; true),
    
    % Storing the cells that are reachable from the current cell in 'children' procedure. 
    retractall(children(_,_)),
    forall(allDirections(I, J), 
           ((X is Xcur + I, Y is Ycur + J, inMap(X, Y, N) , assert(children(X, Y)))) ; true),
    
    % Iterating the children to add them to the queue (excluding the visited ones).
    findall( [Xnew, Ynew],
        ( children(Xnew, Ynew), \+covidZone(Xnew, Ynew), \+member([Xnew, Ynew], Visited)),
        [T|Extend]),
    maplist( consed(Visited), [T|Extend], VisitedExtended),
    append( Rest, VisitedExtended, UpdatedQueue),
    
    % Finally we run the bfs again for the updated queue. 
    bfs(UpdatedQueue, N).
           
                                      
main(N) :- 
    N > 0,
    generateCovid(N),
    generateCovid(N),
    generateDoctor(N),
    generateHome(N),
    generateMask(N),
    writeln(""),
    MaxLength is 4 * N,
    retractall(optimalPathLength1(_)),
    assert(optimalPathLength1(MaxLength)),
    retractall(optimalPaths1(_)),
    retractall(optimalPathLength2(_)),
    assert(optimalPathLength2(MaxLength)),
    retractall(optimalPaths2(_)),
    statistics(runtime,[StartRand1|_]),
    (backtrack(0, 0, N, []); true),
    statistics(runtime,[StopRand1|_]),
    TimeTaken1 is StopRand1 - StartRand1,
    optimalPathLength1(Len1), 
    writeln("Using backtracking:"),
    write("Time taken: "), writeln(TimeTaken1),
    ((Len1 \== MaxLength, writeln("WIN!"), forall(optimalPaths1(L1), writeln(L1))) ; 
    (Len1 == MaxLength, writeln("LOSS!"))),
    statistics(runtime,[StartRand2|_]),
  (bfs([[[0, 0]]], N) ; true),
    statistics(runtime,[StopRand2|_]),
    TimeTaken2 is StopRand2 - StartRand2,
    optimalPathLength2(Len2), 
    writeln(""),
    writeln("Using breadth-first search:"),
    write("Time taken: "), writeln(TimeTaken2),
    ((Len2 \== MaxLength, writeln("WIN!"), forall(optimalPaths2(L2), writeln(L2))) ; 
    (Len2 == MaxLength, writeln("LOSS!"))).

                                      
test(N, [CX1, CY1], [CX2, CY2], [DX, DY], [HX, HY], [MX, MY]) :-
    retractall(covid(_, _)),
    retractall(doctor(_, _)),
    retractall(home(_,_)),
    retractall(mask(_,_)),
    assert(covid(CX1, CY1)),
    assert(covid(CX2, CY2)),
    assert(doctor(DX, DY)),
    assert(home(HX, HY)),
    assert(mask(MX, MY)),
    MaxLength is 4 * N,
    retractall(optimalPathLength1(_)),
    assert(optimalPathLength1(MaxLength)),
    retractall(optimalPaths1(_)),
    retractall(optimalPathLength2(_)),
    assert(optimalPathLength2(MaxLength)),
    retractall(optimalPaths2(_)),
    statistics(runtime,[StartRand1|_]),
    (backtrack(0, 0, N, []); true),
    statistics(runtime,[StopRand1|_]),
    TimeTaken1 is StopRand1 - StartRand1,
    optimalPathLength1(Len1), 
    writeln("Using backtracking:"),
    write("Time taken: "), writeln(TimeTaken1),
    ((Len1 \== MaxLength, writeln("WIN!"), forall(optimalPaths1(L1), writeln(L1))) ; 
    (Len1 == MaxLength, writeln("LOSS!"))),
    statistics(runtime,[StartRand2|_]),
  (bfs([[[0, 0]]], N) ; true),
    statistics(runtime,[StopRand2|_]),
    TimeTaken2 is StopRand2 - StartRand2,
    optimalPathLength2(Len2), 
    writeln(""),
    writeln("Using breadth-first search:"),
    write("Time taken: "), writeln(TimeTaken2),
    ((Len2 \== MaxLength, writeln("WIN!"), forall(optimalPaths2(L2), writeln(L2))) ; 
    (Len2 == MaxLength, writeln("LOSS!"))).

