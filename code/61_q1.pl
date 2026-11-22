% candidate_solution(?Solution)
% Solution is a fully filled-in assignment, before any clue is applied:
% four p(Name, Dept, Lang, Project) terms in the fixed order
% Alex, Ben, Carla, Dana. The departments, languages and projects are each
% a permutation of their four values, so every value of every attribute
% is used exactly once. On backtracking it enumerates all
% 4! * 4! * 4! = 13824 assignments, each exactly once.
candidate_solution([p('Alex',  DeptA, LangA, ProjA),
                    p('Ben',   DeptB, LangB, ProjB),
                    p('Carla', DeptC, LangC, ProjC),
                    p('Dana',  DeptD, LangD, ProjD)]) :-
    permutation([research, development, design, testing],
                [DeptA, DeptB, DeptC, DeptD]),
    permutation([python, java, 'c++', javascript],
                [LangA, LangB, LangC, LangD]),
    permutation(['AI', web, embedded, data],
                [ProjA, ProjB, ProjC, ProjD]).

% CLUE 1: The friend who prefers the AI project does not work in research
% and is not Dana.
% Succeeds when the (unique) person whose project is 'AI' has a department
% other than research and is not 'Dana'; fails otherwise.
clue(1, Solution) :-
    member(p(Name, Dept, _Lang, 'AI'), Solution),
    Dept \== research,
    Name \== 'Dana'.