% tests/P2_tests.pl
% Tests for CS F301 Assignment 2, Group 61, Problem P2 (code/61_q2.pl).
%
% Run from the repository root:
%   swipl -q -f tests/P2_tests.pl -g run_p2_tests -t halt
%
% run_p2_tests/0 prints one PASS / FAIL / ERROR line per test and a final
% summary. It fails if any test does not pass, so swipl exits with a
% nonzero status.
%
% The oracle_* predicates are an independent reference implementation
% (own tree representation, own enumeration, own evaluator, own renderer)
% used to check soundness and completeness on small inputs. They share no
% code with code/61_q2.pl.

:- set_prolog_flag(double_quotes, string).   % "..." are strings (SWI default)
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(aggregate)).
:- ensure_loaded('../code/61_q2.pl').        % resolved relative to this file

:- discontiguous test_case/2.

% ======================================================================
% Test runner
% ======================================================================

% run_p2_tests
% Runs every test_case/2 in clause order, reports each outcome and a
% summary, and fails if at least one test failed or raised an error.
run_p2_tests :-
    findall(Name-Goal, test_case(Name, Goal), Cases),
    run_cases(Cases, 0, 0, Passed, Failed),
    Total is Passed + Failed,
    format("~nP2 summary: ~d passed, ~d failed, ~d total~n",
           [Passed, Failed, Total]),
    (   Failed =:= 0
    ->  format("ALL P2 TESTS PASSED~n")
    ;   format("P2 TESTS FAILED~n"),
        fail
    ).

% run_cases(+Cases, +P0, +F0, -P, -F): run each case, counting passes and
% failures through accumulators (no global state).
run_cases([], Passed, Failed, Passed, Failed).
run_cases([Name-Goal|Rest], P0, F0, Passed, Failed) :-
    run_case(Goal, Outcome),
    report(Outcome, Name),
    (   Outcome == pass
    ->  P1 is P0 + 1, F1 = F0
    ;   P1 = P0, F1 is F0 + 1
    ),
    run_cases(Rest, P1, F1, Passed, Failed).

% run_case(+Goal, -Outcome): Outcome is pass, fail or error(E).
% The first solution is enough; exceptions are caught and reported.
run_case(Goal, Outcome) :-
    catch(( once(Goal) -> Outcome = pass ; Outcome = fail ),
          Error,
          Outcome = error(Error)).

report(pass,     Name) :- format("PASS  ~w~n", [Name]).
report(fail,     Name) :- format("FAIL  ~w~n", [Name]).
report(error(E), Name) :- format("ERROR ~w: ~q~n", [Name, E]).

% ======================================================================
% Independent oracle (reference implementation for small inputs)
% Trees: n(N) | bin(Symbol, Left, Right), Symbol in '+', '-', '*', '/'.
% ======================================================================

% oracle_tree(+Nums, -Tree): every binary tree over Nums in order,
% including trees with invalid divisions (filtered by oracle_value/2).
oracle_tree([N], n(N)).
oracle_tree(Nums, bin(Symbol, Left, Right)) :-
    length(Nums, K),
    K >= 2,
    Max is K - 1,
    between(1, Max, J),                 % size of the left part
    length(LeftNums, J),
    append(LeftNums, RightNums, Nums),
    oracle_tree(LeftNums, Left),
    oracle_tree(RightNums, Right),
    member(Symbol, ['+', '-', '*', '/']).

% oracle_value(+Tree, -Value): integer value; fails on a zero divisor or
% inexact division anywhere in the tree. Exactness is checked by
% multiplying back, not with mod.
oracle_value(n(N), N).
oracle_value(bin(Symbol, Left, Right), Value) :-
    oracle_value(Left, A),
    oracle_value(Right, B),
    oracle_apply(Symbol, A, B, Value).

oracle_apply('+', A, B, V) :- V is A + B.
oracle_apply('-', A, B, V) :- V is A - B.
oracle_apply('*', A, B, V) :- V is A * B.
oracle_apply('/', A, B, V) :-
    B =\= 0,
    Q is A div B,
    Q * B =:= A,
    V = Q.

oracle_level('+', 1).
oracle_level('-', 1).
oracle_level('*', 2).
oracle_level('/', 2).

% oracle_text(+Tree, +MinLevel, -Text): Text is wrapped in parentheses
% when its top level is below MinLevel. A left child needs the parent's
% level, a right child needs one more (classic precedence printer).
oracle_text(n(N), _, Text) :-
    number_codes(N, Codes),
    atom_codes(Text, Codes).
oracle_text(bin(Symbol, Left, Right), MinLevel, Text) :-
    oracle_level(Symbol, Level),
    RightMin is Level + 1,
    oracle_text(Left,  Level,    LeftText),
    oracle_text(Right, RightMin, RightText),
    atomic_list_concat([LeftText, Symbol, RightText], Bare),
    (   Level < MinLevel
    ->  atomic_list_concat(['(', Bare, ')'], Text)
    ;   Text = Bare
    ).

% oracle_equations(+List, -Sorted): all valid equation strings, sorted.
oracle_equations(List, Sorted) :-
    findall(Eq, oracle_equation(List, Eq), All),
    sort(All, Sorted).

oracle_equation(List, Eq) :-
    length(List, K),
    K >= 2,
    Max is K - 1,
    between(1, Max, J),
    length(LeftNums, J),
    append(LeftNums, RightNums, List),
    oracle_tree(LeftNums, LeftTree),
    oracle_value(LeftTree, LeftValue),
    oracle_tree(RightNums, RightTree),
    oracle_value(RightTree, RightValue),
    LeftValue =:= RightValue,
    oracle_text(LeftTree,  0, LeftText),
    oracle_text(RightTree, 0, RightText),
    atomic_list_concat([LeftText, '=', RightText], EqAtom),
    atom_string(EqAtom, Eq).

% ======================================================================
% Test helpers for the implementation's tree representation
% ======================================================================

t_node(add(L, R), '+', L, R).
t_node(sub(L, R), '-', L, R).
t_node(mul(L, R), '*', L, R).
t_node(div(L, R), '/', L, R).

% to_oracle(+Tree, -OracleTree): translate num/add/sub/mul/div trees.
to_oracle(num(N), n(N)).
to_oracle(Tree, bin(Symbol, OL, OR)) :-
    t_node(Tree, Symbol, L, R),
    to_oracle(L, OL),
    to_oracle(R, OR).

% well_formed(+Tree): leaves are non-negative integers, nodes are binary.
well_formed(num(N)) :-
    integer(N),
    N >= 0.
well_formed(Tree) :-
    t_node(Tree, _, L, R),
    well_formed(L),
    well_formed(R).

% tree_leaves(+Tree, -Leaves): leaf numbers from left to right.
tree_leaves(num(N), [N]).
tree_leaves(Tree, Leaves) :-
    t_node(Tree, _, L, R),
    tree_leaves(L, A),
    tree_leaves(R, B),
    append(A, B, Leaves).

% digit_chars(+Chars, -Digits): keep only digit characters, in order.
digit_chars([], []).
digit_chars([C|Cs], Digits) :-
    (   char_type(C, digit(_))
    ->  Digits = [C|Rest]
    ;   Digits = Rest
    ),
    digit_chars(Cs, Rest).

% The PDF's expected answer for [4,2,5,3].
pdf_4253(["4*2-5=3", "4*2=5+3", "4-2=5-3", "4/2=5-3",
          "4=2*(5-3)", "4=2+(5-3)", "4=2+5-3"]).

% Small inputs checked against the oracle (zeros, repeats, negatives,
% invalid divisions, multi-digit numbers, no-solution cases).
oracle_list([4,2,5,3]).
oracle_list([2,4,8]).
oracle_list([2,3,4]).
oracle_list([0,0]).
oracle_list([0,0,0]).
oracle_list([1,1,1]).
oracle_list([2,2,2,2]).
oracle_list([6,3,2]).
oracle_list([3,5,2]).
oracle_list([1,3,1,3]).
oracle_list([7,2,2,7]).
oracle_list([2,1,3,0,1]).
oracle_list([10,2,5]).
oracle_list([1,2,12]).
oracle_list([1,2,3,4,5]).
oracle_list([8,4,2,1,0]).

expression_oracle_list([1,2,3]).
expression_oracle_list([4,0,2,0]).
expression_oracle_list([1,1,1,1]).
expression_oracle_list([3,5,2,4]).

% ======================================================================
% eval_op/4
% ======================================================================

test_case('eval_op: 3+4 = 7', (eval_op(+, 3, 4, R), R == 7)).
test_case('eval_op: 3-5 = -2 (negative result)', (eval_op(-, 3, 5, R), R == -2)).
test_case('eval_op: -2*3 = -6', (eval_op(*, -2, 3, R), R == -6)).
test_case('eval_op: 8/4 = 2 (integer result)', (eval_op(/, 8, 4, R), integer(R), R == 2)).
test_case('eval_op: -6/3 = -2', (eval_op(/, -6, 3, R), R == -2)).
test_case('eval_op: 6/-3 = -2', (eval_op(/, 6, -3, R), R == -2)).
test_case('eval_op: -6/-3 = 2', (eval_op(/, -6, -3, R), R == 2)).
test_case('eval_op: 0/5 = 0 (zero result)', (eval_op(/, 0, 5, R), R == 0)).
test_case('eval_op: 7/2 fails (inexact)', \+ eval_op(/, 7, 2, _)).
test_case('eval_op: -7/2 fails (inexact, negative)', \+ eval_op(/, -7, 2, _)).
test_case('eval_op: 5/0 fails (zero divisor)', \+ eval_op(/, 5, 0, _)).
test_case('eval_op: 0/0 fails (zero divisor)', \+ eval_op(/, 0, 0, _)).
test_case('eval_op: unknown operator fails', \+ eval_op(^, 2, 3, _)).

% ======================================================================
% split_nonempty/3
% ======================================================================

test_case('split_nonempty: all splits of [4,2,5,3] in order',
    ( findall(L-R, split_nonempty([4,2,5,3], L, R), S),
      S == [[4]-[2,5,3], [4,2]-[5,3], [4,2,5]-[3]] )).
test_case('split_nonempty: exactly N-1 splits for lengths 2..7',
    forall(between(2, 7, K),
           ( numlist(1, K, L),
             aggregate_all(count, split_nonempty(L, _, _), C),
             C =:= K - 1 ))).
test_case('split_nonempty: parts nonempty and rejoin to the input',
    forall(split_nonempty([1,2,3,4], L, R),
           ( L \== [], R \== [], append(L, R, [1,2,3,4]) ))).
test_case('split_nonempty: [] fails', \+ split_nonempty([], _, _)).
test_case('split_nonempty: [7] fails', \+ split_nonempty([7], _, _)).

% ======================================================================
% precedence/2
% ======================================================================

test_case('precedence: levels of all node types',
    ( precedence(num(4), A),
      precedence(add(num(1), num(2)), B),
      precedence(sub(num(1), num(2)), C),
      precedence(mul(num(1), num(2)), D),
      precedence(div(num(1), num(2)), E),
      [A, B, C, D, E] == [3, 1, 1, 2, 2] )).
test_case('precedence: only the outermost node counts',
    ( precedence(mul(add(num(1), num(2)), num(3)), P), P == 2 )).
test_case('precedence: non-tree term fails', \+ precedence(pow(num(2), num(3)), _)).

% ======================================================================
% expression/3
% ======================================================================

test_case('expression: [] fails', \+ expression([], _, _)).
test_case('expression: [7] gives only num(7) with value 7',
    ( findall(T-V, expression([7], T, V), S), S == [num(7)-7] )).
test_case('expression: [4,2] gives exactly the four trees and values',
    ( findall(T-V, expression([4,2], T, V), S0),
      msort(S0, S),
      msort([add(num(4),num(2))-6, sub(num(4),num(2))-2,
             mul(num(4),num(2))-8, div(num(4),num(2))-2], Expected),
      S == Expected )).
test_case('expression: [5,0] has 3 trees, no division (zero divisor)',
    ( aggregate_all(count, expression([5,0], _, _), N), N == 3,
      \+ expression([5,0], div(_, _), _) )).
test_case('expression: [7,2] has no division tree (inexact)',
    \+ expression([7,2], div(_, _), _)).
test_case('expression: inexact intermediate (7/2)*2 rejected',
    \+ expression([7,2,2], mul(div(num(7), num(2)), num(2)), _)).
test_case('expression: zero divisor from a subtree 4/(3-3) rejected',
    \+ expression([4,3,3], div(num(4), sub(num(3), num(3))), _)).
test_case('expression: negative intermediate (3-5)*2 = -4',
    ( expression([3,5,2], mul(sub(num(3), num(5)), num(2)), V), V =:= -4 )).
test_case('expression: negative exact division (3-5)/2 = -1',
    ( expression([3,5,2], div(sub(num(3), num(5)), num(2)), V), V =:= -1 )).
test_case('expression: zero result 0/4 = 0',
    ( expression([0,4], div(num(0), num(4)), V), V =:= 0 )).
test_case('expression: both groupings 1+2+3 and 1+(2+3) exist',
    ( expression([1,2,3], add(add(num(1), num(2)), num(3)), V1), V1 =:= 6,
      expression([1,2,3], add(num(1), add(num(2), num(3))), V2), V2 =:= 6 )).
test_case('expression: leaves keep the input order',
    forall(expression([3,1,4,1], T, _),
           ( tree_leaves(T, Leaves), Leaves == [3,1,4,1] ))).
test_case('expression: every tree is a well-formed binary tree',
    forall(expression([1,2,3,4], T, _), well_formed(T))).
test_case('expression: trees for [1,1,1] are pairwise distinct',
    ( findall(T, expression([1,1,1], T, _), Ts),
      length(Ts, N), sort(Ts, U), length(U, N) )).

% Soundness: every generated value matches the independent evaluator.
test_case(Name, Goal) :-
    expression_oracle_list(L),
    format(atom(Name), 'expression: values match independent evaluator for ~w', [L]),
    Goal = forall(expression(L, T, V),
                  ( to_oracle(T, O), oracle_value(O, W), W =:= V )).

% Completeness: distinct trees, and as many as the oracle's valid trees.
test_case(Name, Goal) :-
    expression_oracle_list(L),
    format(atom(Name), 'expression: distinct and complete vs oracle for ~w', [L]),
    Goal = ( findall(T, expression(L, T, _), Ts),
             length(Ts, N1), sort(Ts, U), length(U, N1),
             aggregate_all(count, (oracle_tree(L, O), oracle_value(O, _)), N2),
             N1 =:= N2 ).

% ======================================================================
% render_expr/2
% ======================================================================

render_case(mul(add(num(4),num(2)),num(3)),                     "(4+2)*3").
render_case(add(num(4),mul(num(2),num(3))),                     "4+2*3").
render_case(mul(div(num(8),num(4)),num(2)),                     "8/4*2").
render_case(div(num(8),mul(num(4),num(2))),                     "8/(4*2)").
render_case(sub(sub(num(1),num(2)),num(3)),                     "1-2-3").
render_case(sub(num(1),sub(num(2),num(3))),                     "1-(2-3)").
render_case(add(num(1),add(num(2),num(3))),                     "1+(2+3)").
render_case(add(add(num(1),num(2)),num(3)),                     "1+2+3").
render_case(num(0),                                             "0").
render_case(num(105),                                           "105").
render_case(sub(add(num(1),num(2)),num(3)),                     "1+2-3").
render_case(add(sub(num(1),num(2)),num(3)),                     "1-2+3").
render_case(sub(num(1),add(num(2),num(3))),                     "1-(2+3)").
render_case(mul(num(1),mul(num(2),num(3))),                     "1*(2*3)").
render_case(div(mul(num(8),num(4)),num(2)),                     "8*4/2").
render_case(div(num(8),div(num(4),num(2))),                     "8/(4/2)").
render_case(mul(add(num(1),num(2)),add(num(3),num(4))),         "(1+2)*(3+4)").
render_case(sub(mul(num(2),add(num(5),num(3))),div(num(8),num(4))), "2*(5+3)-8/4").

test_case(Name, Goal) :-
    render_case(Tree, Expected),
    format(atom(Name), 'render_expr: ~w', [Expected]),
    Goal = ( render_expr(Tree, S), string(S), S == Expected ).

test_case('render_expr: matches independent renderer on all trees of [1,2,3,4]',
    forall(expression([1,2,3,4], T, _),
           ( render_expr(T, S), to_oracle(T, O),
             oracle_text(O, 0, A), atom_string(A, S) ))).
test_case('render_expr: distinct trees of [1,1,1,1] give distinct strings',
    ( findall(S, ( expression([1,1,1,1], T, _), render_expr(T, S) ), Ss),
      length(Ss, N), sort(Ss, U), length(U, N) )).

% ======================================================================
% Oracle self-check against the specification
% ======================================================================

test_case('oracle: reproduces the three PDF examples',
    ( pdf_4253(Expected),
      oracle_equations([4,2,5,3], O1), O1 == Expected,
      oracle_equations([2,3,4], O2), O2 == [],
      oracle_equations([2,4,8], O3), O3 == ["2*4=8"] )).

% ======================================================================
% generate_equation/2
% ======================================================================

test_case('generate_equation: first answer for [4,2,5,3] is a PDF equation string',
    ( pdf_4253(Expected), generate_equation([4,2,5,3], E),
      string(E), memberchk(E, Expected) )).
test_case('generate_equation: every answer for [4,2,5,3] is in the PDF list',
    ( pdf_4253(Expected),
      forall(generate_equation([4,2,5,3], E),
             ( string(E), memberchk(E, Expected) )) )).
test_case('generate_equation: backtracking gives the PDF set with no duplicates',
    ( pdf_4253(Expected),
      findall(E, generate_equation([4,2,5,3], E), Raw),
      length(Raw, 7), sort(Raw, Sorted), Sorted == Expected )).
test_case('generate_equation: exactly one "=" and no spaces',
    forall(generate_equation([4,2,5,3], E),
           ( split_string(E, "=", "", Parts), length(Parts, 2),
             \+ sub_string(E, _, _, _, " ") ))).
test_case('generate_equation: numbers keep the input order',
    forall(generate_equation([2,1,3,0,1], E),
           ( string_chars(E, Cs), digit_chars(Cs, Ds),
             Ds == ['2','1','3','0','1'] ))).

% No-solution and too-short inputs ([2,2,2] and [1,2,12] hand-checked:
% no equation exists, and [1,2,12] must not join digits into 12=12).
generate_fail_list([2,3,4]).
generate_fail_list([]).
generate_fail_list([7]).
generate_fail_list([1,0]).
generate_fail_list([2,2,2]).
generate_fail_list([1,2,12]).

test_case(Name, \+ generate_equation(L, _)) :-
    generate_fail_list(L),
    format(atom(Name), 'generate_equation: fails cleanly for ~w', [L]).

test_case(Name, Goal) :-
    oracle_list(L),
    format(atom(Name), 'generate_equation: no duplicates, matches oracle for ~w', [L]),
    Goal = ( findall(E, generate_equation(L, E), Raw),
             msort(Raw, M), sort(Raw, S), M == S,
             oracle_equations(L, O), S == O ).

% ======================================================================
% all_equations/2
% ======================================================================

test_case('all_equations: PDF example [4,2,5,3]',
    ( pdf_4253(Expected), all_equations([4,2,5,3], Es), Es == Expected )).
test_case('all_equations: PDF example [2,3,4] gives []',
    ( all_equations([2,3,4], Es), Es == [] )).
test_case('all_equations: PDF example [2,4,8]',
    ( all_equations([2,4,8], Es), Es == ["2*4=8"] )).
test_case('all_equations: [] gives []', ( all_equations([], Es), Es == [] )).
test_case('all_equations: [7] gives []', ( all_equations([7], Es), Es == [] )).

% Hand-checked exact results.
test_case('all_equations: [0,0] gives ["0=0"]',
    ( all_equations([0,0], Es), Es == ["0=0"] )).
test_case('all_equations: [1,1] gives ["1=1"] (repeated numbers)',
    ( all_equations([1,1], Es), Es == ["1=1"] )).
test_case('all_equations: [0,0,0] excludes 0/0',
    ( all_equations([0,0,0], Es),
      Es == ["0*0=0", "0+0=0", "0-0=0", "0=0*0", "0=0+0", "0=0-0"] )).
test_case('all_equations: [6,3,2]',
    ( all_equations([6,3,2], Es), Es == ["6/3=2", "6=3*2"] )).
test_case('all_equations: multi-digit [10,2,5]',
    ( all_equations([10,2,5], Es), Es == ["10/2=5", "10=2*5"] )).
test_case('all_equations: [1,2,12] gives [] (no digit joining)',
    ( all_equations([1,2,12], Es), Es == [] )).

% Specific inclusions and exclusions.
test_case('all_equations: negative sides 1-3=1-3',
    ( all_equations([1,3,1,3], Es), memberchk("1-3=1-3", Es) )).
test_case('all_equations: negative intermediates and divisor 2=(1-3)/(0-1)',
    ( all_equations([2,1,3,0,1], Es), memberchk("2=(1-3)/(0-1)", Es) )).
test_case('all_equations: inexact intermediate 7/2*2=7 excluded',
    ( all_equations([7,2,2,7], Es), \+ memberchk("7/2*2=7", Es) )).
test_case('all_equations: 4/(2-2)=0 excluded, 4*(2-2)=0 kept',
    ( all_equations([4,2,2,0], Es),
      \+ memberchk("4/(2-2)=0", Es), memberchk("4*(2-2)=0", Es) )).
test_case('all_equations: zero dividend 0/4=0 kept',
    ( all_equations([0,4,0], Es), memberchk("0/4=0", Es) )).
test_case('all_equations: distinct groupings for [1,2,3,6] all present',
    ( all_equations([1,2,3,6], Es),
      forall(member(E, ["1+2+3=6", "1+(2+3)=6", "1*2*3=6", "1*(2*3)=6"]),
             memberchk(E, Es)) )).
test_case('all_equations: repeated numbers 2+2=2*2',
    ( all_equations([2,2,2,2], Es), memberchk("2+2=2*2", Es) )).

test_case(Name, Goal) :-
    oracle_list(L),
    format(atom(Name), 'all_equations: strings, sorted, unique, matches oracle for ~w', [L]),
    Goal = ( all_equations(L, Es), maplist(string, Es),
             sort(Es, S), S == Es,
             oracle_equations(L, O), Es == O ).

% ======================================================================
% count_equations/2
% ======================================================================

count_case([4,2,5,3], 7).
count_case([2,3,4],   0).
count_case([2,4,8],   1).
count_case([],        0).
count_case([7],       0).
count_case([1,1],     1).
count_case([0,0,0],   6).
count_case([6,3,2],   2).
count_case([2,2,2],   0).

test_case(Name, Goal) :-
    count_case(L, Expected),
    format(atom(Name), 'count_equations: ~w gives ~w', [L, Expected]),
    Goal = ( count_equations(L, N), N == Expected ).

test_case(Name, Goal) :-
    oracle_list(L),
    format(atom(Name), 'count_equations: equals length of all_equations for ~w', [L]),
    Goal = ( count_equations(L, N), all_equations(L, Es),
             length(Es, M), N =:= M ).

test_case('count_equations: rejects a wrong bound count',
    \+ count_equations([4,2,5,3], 6)).