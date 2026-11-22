% eval_op(+Op, +A, +B, -Result)
% Result is the integer value of applying the binary operator Op to the
% integers A and B. Op is one of the atoms +, -, *, /.
% Division succeeds only when B is nonzero and B divides A exactly;
% otherwise eval_op/4 fails. Any other operator fails (no matching clause).
eval_op(+, A, B, Result) :-
    Result is A + B.
eval_op(-, A, B, Result) :-
    Result is A - B.
eval_op(*, A, B, Result) :-
    Result is A * B.
eval_op(/, A, B, Result) :-
    B =\= 0,                 % checked first: A mod 0 would raise an error
    A mod B =:= 0,           % exact divisibility, integer arithmetic only
    Result is A // B.        % safe: the remainder is already known to be 0

% expression(+Numbers, -Tree, -Value)
% Tree is a binary expression tree that uses every integer of Numbers
% exactly once, in the given order, and Value is its integer value.
% Leaves are num(N); inner nodes are add/2, sub/2, mul/2, div/2.
% Every division node must be exact with a nonzero divisor (eval_op/4).
% Enumerates every valid tree on backtracking; fails for [].

% Base case: a single number is a leaf whose value is the number itself.
expression([N], num(N), N).

% Recursive case: split Numbers into two nonempty consecutive parts,
% build an expression for each, then join them with one operator.
expression(Numbers, Tree, Value) :-
    append(LeftNums, RightNums, Numbers),
    LeftNums  = [_|_],                 % left part nonempty
    RightNums = [_|_],                 % right part nonempty
    expression(LeftNums,  LeftTree,  LeftValue),
    expression(RightNums, RightTree, RightValue),
    member(Op-Tree, [ (+)-add(LeftTree, RightTree),
                      (-)-sub(LeftTree, RightTree),
                      (*)-mul(LeftTree, RightTree),
                      (/)-div(LeftTree, RightTree) ]),
    eval_op(Op, LeftValue, RightValue, Value).

% split_nonempty(+List, -Left, -Right)
% Left and Right are nonempty lists that, joined in order, give List,
% so Left is a proper nonempty prefix of List and Right is the rest.
% A list of length N >= 2 has exactly N-1 such splits, enumerated on
% backtracking from the shortest Left to the longest. Fails if N < 2.
split_nonempty(List, Left, Right) :-
    append(Left, Right, List),
    Left  = [_|_],                     % reject the split [] + List
    Right = [_|_].                     % reject the split List + []

% precedence(+Tree, -Level)
% Level is the binding strength of Tree's outermost node:
% 1 for add/sub, 2 for mul/div, 3 for a single number num/1.
% A higher Level binds tighter. Only the top functor is inspected;
% subtrees are ignored and nothing is evaluated. Fails for any other term.
precedence(add(_, _), 1).
precedence(sub(_, _), 1).
precedence(mul(_, _), 2).
precedence(div(_, _), 2).
precedence(num(_),    3).


% render_expr(+Tree, -String)
% String is the canonical, space-free SWI-Prolog string for the expression
% Tree. A left child is wrapped in parentheses only if its top operator
% binds less tightly than its parent's; a right child is wrapped if it
% binds equally or less tightly. Numbers are never wrapped, so every
% distinct tree gives a distinct string.

% Base case: a numeric leaf is written in decimal, without parentheses.
render_expr(num(N), String) :-
    number_string(N, String).

% Recursive case: render both children, wrap them as the rules require,
% then join left, operator symbol and right.
render_expr(Tree, String) :-
    member(Tree-Symbol, [ add(Left, Right)-(+),
                          sub(Left, Right)-(-),
                          mul(Left, Right)-(*),
                          div(Left, Right)-(/) ]),
    precedence(Tree,  Parent),
    precedence(Left,  LeftLevel),
    precedence(Right, RightLevel),
    render_expr(Left,  LeftRaw),
    render_expr(Right, RightRaw),
    (   LeftLevel < Parent                      % left: strictly lower only
    ->  format(string(LeftText), "(~w)", [LeftRaw])
    ;   LeftText = LeftRaw
    ),
    (   RightLevel =< Parent                    % right: equal or lower
    ->  format(string(RightText), "(~w)", [RightRaw])
    ;   RightText = RightRaw
    ),
    format(string(String), "~w~w~w", [LeftText, Symbol, RightText]).

    % generate_equation(+List, -Equation)
% Equation is a canonical, space-free SWI-Prolog string "L=R", where L is
% an expression over a nonempty prefix of List, R is an expression over
% the remaining nonempty suffix, every number is used once in order, and
% both sides have the same integer value. Further equations are produced
% on backtracking. Fails (finitely) if List has fewer than two elements
% or no valid equation exists.
generate_equation(List, Equation) :-
    split_nonempty(List, LeftNums, RightNums),        % position of '='
    expression(LeftNums,  LeftTree,  LeftValue),
    expression(RightNums, RightTree, RightValue),
    LeftValue =:= RightValue,                         % both sides equal
    render_expr(LeftTree,  LeftString),
    render_expr(RightTree, RightString),
    format(string(Equation), "~w=~w", [LeftString, RightString]).
