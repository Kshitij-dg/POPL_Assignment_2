% tests/P1_tests.pl -- CS F301 Assignment 2, Group 61, Problem P1
%
% Plain test runner (plunit is not used: only lists, apply, yall and
% aggregate are permitted). Run from the repository root:
%   swipl -q -f tests/P1_tests.pl -g run_p1_tests -t halt
% Prints PASS/FAIL/ERROR per test and a summary; run_p1_tests/0 fails
% (non-zero exit status) if any test does not pass.

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(yall)).
:- use_module(library(aggregate)).

% Resolved relative to this file, so it loads code/61_q1.pl.
:- ensure_loaded('../code/61_q1.pl').

% ------------------------------------------------------------- runner

% run_p1_tests: runs every p1_test/2 goal once and reports the results.
run_p1_tests :-
    findall(Name-Goal, p1_test(Name, Goal), Tests),
    run_test_list(Tests, 0, 0, Passed, Failed),
    Total is Passed + Failed,
    format("~nP1 summary: ~w/~w passed, ~w failed~n",
           [Passed, Total, Failed]),
    Failed =:= 0.

% run_test_list(+Tests, +P0, +F0, -P, -F): runs the tests in order,
% accumulating pass and fail counts.
run_test_list([], P, F, P, F).
run_test_list([Name-Goal | Rest], P0, F0, P, F) :-
    run_one(Goal, Result),
    report(Result, Name),
    (   Result == pass
    ->  P1 is P0 + 1, F1 = F0
    ;   P1 = P0, F1 is F0 + 1
    ),
    run_test_list(Rest, P1, F1, P, F).

% run_one(+Goal, -Result): Result is pass, fail or error(E). Exceptions
% are caught so that one broken test cannot stop the whole run.
run_one(Goal, Result) :-
    catch(( call(Goal) -> Result = pass ; Result = fail ),
          E, Result = error(E)).

report(pass, Name)     :- format("PASS  ~w~n", [Name]).
report(fail, Name)     :- format("FAIL  ~w~n", [Name]).
report(error(E), Name) :- format("ERROR ~w: ~q~n", [Name, E]).

% ----------------------------------------------------------- fixtures

% fixture(Name, Solution): hand-made full assignments (every attribute
% value used exactly once). layout_example is the layout shown in the
% PDF, which the PDF says is not the answer.
fixture(layout_example,
        [p('Alex', research, python, 'AI'),
         p('Ben', development, java, web),
         p('Carla', design, 'c++', embedded),
         p('Dana', testing, javascript, data)]).
fixture(fixture_a,
        [p('Alex', design, java, 'AI'),
         p('Ben', research, 'c++', web),
         p('Carla', testing, python, embedded),
         p('Dana', development, javascript, data)]).
fixture(fixture_b,
        [p('Alex', testing, python, embedded),
         p('Ben', design, java, web),
         p('Carla', development, 'c++', 'AI'),
         p('Dana', research, javascript, data)]).
fixture(fixture_c,
        [p('Alex', testing, 'c++', web),
         p('Ben', development, python, embedded),
         p('Carla', design, javascript, 'AI'),
         p('Dana', research, java, data)]).

% expected_true(Fixture, Clues): exactly these clue numbers (1-9) hold
% for the fixture; every other clue must fail. Every clue is true for at
% least one fixture and false for at least one.
expected_true(layout_example, [2, 4, 7, 9]).
expected_true(fixture_a,      [1, 2, 3, 4, 5]).
expected_true(fixture_b,      [1, 2, 3, 4, 5, 7]).
expected_true(fixture_c,      [1, 6, 8]).

% expected_count(Active, N): expected count_solutions(Active, N) results.
expected_count([], 13824).
expected_count([1], 7776).
expected_count([2], 7776).
expected_count([3], 3456).
expected_count([4], 2592).
expected_count([5], 3456).
expected_count([6], 7776).
expected_count([7], 5184).
expected_count([8], 2592).
expected_count([9], 3456).
expected_count([3, 5], 1152).
expected_count([2, 6], 3888).
expected_count([4, 7], 1080).
expected_count([1, 8], 1944).
expected_count([8, 1], 1944).                  % order of Active is irrelevant
expected_count([1, 1], 7776).                  % a repeated clue counts once
expected_count([1, 2, 3, 4, 5, 6, 7], 16).
expected_count([1, 2, 3, 4, 5, 6, 7, 8], 3).
expected_count([1, 2, 3, 4, 5, 6, 7, 8, 9], 1).

% ------------------------------------------------------------ helpers

% valid_assignment(+S): S lists Alex, Ben, Carla, Dana in order and uses
% each department, language and project exactly once.
valid_assignment([p('Alex', D1, L1, P1), p('Ben', D2, L2, P2),
                  p('Carla', D3, L3, P3), p('Dana', D4, L4, P4)]) :-
    msort([D1, D2, D3, D4], Ds),
    msort([research, development, design, testing], Ds),
    msort([L1, L2, L3, L4], Ls),
    msort([python, java, 'c++', javascript], Ls),
    msort([P1, P2, P3, P4], Ps),
    msort(['AI', web, embedded, data], Ps).

% clue_result(+K, +S, +Expected): clue K succeeds exactly once on S when
% Expected is true, and does not succeed at all when Expected is false.
clue_result(K, S, true)  :- aggregate_all(count, clue(K, S), 1).
clue_result(K, S, false) :- aggregate_all(count, clue(K, S), 0).

% design_embedded(+S): independent statement of clue 9's condition.
design_embedded(S) :-
    once(member(p(_, design, _, Project), S)),
    Project == embedded.

% rotate_names(+S, -R): R gives each person's attributes to a different
% name; a clue that never mentions a name must give the same result.
rotate_names([p(N1, D1, L1, P1), p(N2, D2, L2, P2),
              p(N3, D3, L3, P3), p(N4, D4, L4, P4)],
             [p(N2, D1, L1, P1), p(N3, D2, L2, P2),
              p(N4, D3, L3, P3), p(N1, D4, L4, P4)]).

% main_output_solution(-Solution): runs main/0, captures its output,
% requires exactly four newline-terminated lines of the form
% "Name = [Dept, Lang, Project]" in the order Alex, Ben, Carla, Dana,
% and returns the printed assignment.
main_output_solution(Solution) :-
    with_output_to(string(Out), main),
    split_string(Out, "\n", "", Parts),
    append(Lines, [""], Parts),
    maplist(parse_main_line, ['Alex', 'Ben', 'Carla', 'Dana'],
            Lines, Solution).

% parse_main_line(+Name, +Line, -Term): Line describes Name; it must be
% exactly what format "~w = [~w, ~w, ~w]" produces for the parsed values.
parse_main_line(Name, Line, p(Name, Dept, Lang, Project)) :-
    split_string(Line, "=", " ", [NameStr, Rest]),
    atom_string(Name, NameStr),
    string_concat("[", Inner0, Rest),
    once(string_concat(Inner, "]", Inner0)),
    split_string(Inner, ",", " ", [DS, LS, PS]),
    atom_string(Dept, DS),
    atom_string(Lang, LS),
    atom_string(Project, PS),
    format(string(Rebuilt), "~w = [~w, ~w, ~w]",
           [Name, Dept, Lang, Project]),
    Line == Rebuilt.

% -------------------------------------------------------------- tests

% p1_test(Name, Goal): Goal must succeed for the test to pass.

% candidate_solution/1
p1_test('candidate_solution/1 yields 13824 assignments',
        ( findall(S, candidate_solution(S), L), length(L, 13824) )).
p1_test('candidate_solution/1 yields no duplicates',
        ( findall(S, candidate_solution(S), L),
          sort(L, U), length(U, 13824) )).
p1_test('every candidate is a valid full assignment in name order',
        forall(candidate_solution(S), valid_assignment(S))).
p1_test('every fixture is a generated candidate',
        forall(fixture(_, S), candidate_solution(S))).

% Individual clues: full truth table over the fixtures (36 checks).
p1_test(Name, clue_result(K, S, Expected)) :-
    fixture(F, S),
    expected_true(F, TrueClues),
    between(1, 9, K),
    (   memberchk(K, TrueClues) -> Expected = true ; Expected = false ),
    format(atom(Name), "clue(~w) is ~w for ~w", [K, Expected, F]).
p1_test('each clue succeeds at most once on every candidate',
        forall(( candidate_solution(S), between(1, 9, K) ),
               ( aggregate_all(count, clue(K, S), C), C =< 1 ))).

% count_solutions/2: empty list, single clues, subsets, 1-8 and 1-9.
p1_test(Name, count_solutions(Active, N)) :-
    expected_count(Active, N),
    format(atom(Name), "count_solutions(~w) = ~w", [Active, N]).

% Clue 9
p1_test('clue 9 source mentions no friend by name',
        ( findall(S-Body, clause(clue(9, S), Body), [Clause]),
          term_string(Clause, Str),
          forall(member(Nm, ["Alex", "Ben", "Carla", "Dana"]),
                 \+ sub_string(Str, _, _, _, Nm)) )).
p1_test('clue 9 holds exactly when the design person prefers embedded',
        forall(candidate_solution(S),
               (   clue(9, S) -> design_embedded(S)
               ;   \+ design_embedded(S)
               ))).
p1_test('clue 9 result is unchanged when names are rotated',
        forall(candidate_solution(S),
               (   rotate_names(S, R),
                   (   clue(9, S) -> clue(9, R) ; \+ clue(9, R) )
               ))).
p1_test('clue 9 is true in exactly one of the solutions of clues 1-8',
        ( findall(S, ( candidate_solution(S),
                       forall(between(1, 8, K), clue(K, S)) ), Sols),
          Sols \== [],
          include([X]>>clue(9, X), Sols, Kept),
          length(Kept, 1) )).

% main/0
p1_test('main/0 prints exactly four lines "Name = [Dept, Lang, Project]" for Alex, Ben, Carla, Dana',
        main_output_solution(_)).
p1_test('main/0 prints a valid assignment that satisfies clues 1-8',
        ( main_output_solution(S),
          candidate_solution(S),
          forall(between(1, 8, K), clue(K, S)) )).