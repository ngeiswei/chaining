% lib_possibly_lt.pl
%
% A companion to the standard-order comparison @< that is sound on non-ground
% terms.
%
% MeTTa call:  (@<? A B)          -> true / false
% Prolog call: possibly_lt(A, B)  -> boolean
%
% (@<? A B) is true iff there is some substitution of the variables in A and B
% under which A @< B holds in the standard order of terms.  In other words, it
% is the "may precede" / "possibly less than" relation: e.g. (f @< $x) is false
% for the current instantiation, but (@<? f $x) is true because $x can be bound
% to g.
%
% The relation is built on SWI-Prolog's partial_compare/3 (introduced in
% 10.1.16), which distinguishes a stable decision from one that depends on a
% variable.  A stable '<' or an 'undecided' outcome means A can be made less
% than B; a stable '>' or '=' rules it out.  If partial_compare/3 is not
% available we fall back to a portable reconstruction for acyclic terms.
%
% Register the operator with PeTTa as usual:
%
%   !(translatePredicate (consult "./lib_possibly_lt.pl"))
%   !(import_prolog_function @<?)

'@<?'(A, B, R) :-
    (   possibly_lt(A, B)
    ->  R = true
    ;   R = false
    ).

% possibly_lt(+A, +B) is the Prolog-facing name of the same relation.
possibly_lt(A, B) :-
    partial_compare_(O, A, B),
    (   O == (<)
    ->  true
    ;   O = undecided(_, _)
    ).

% ---------------------------------------------------------------------------
% Use SWI-Prolog's partial_compare/3 when present (>= 10.1.16), otherwise the
% local reconstruction below.
% ---------------------------------------------------------------------------

partial_compare_(O, A, B) :-
    (   has_partial_compare
    ->  partial_compare(O, A, B)
    ;   partial_compare_port(O, A, B)
    ).

has_partial_compare :-
    (   current_predicate(system:partial_compare/3)
    ;   current_predicate(partial_compare/3)
    ),
    !.

% ---------------------------------------------------------------------------
% Portable reconstruction of partial_compare/3 for acyclic terms.
%
% It mirrors the standard order, but stops at the first pair whose comparison
% is not stable and reports it as undecided(Sub1, Sub2).
% ---------------------------------------------------------------------------

partial_compare_port(O, A, B) :-
    acyclic_term(A),
    acyclic_term(B),
    pcompare(O, A, B).

pcompare(O, A, B) :-
    (   A == B
    ->  O = (=)
    ;   var(A)
    ->  O = undecided(A, B)
    ;   var(B)
    ->  O = undecided(A, B)
    ;   number(A), number(B)
    ->  compare(O, A, B)
    ;   string(A), string(B)
    ->  compare(O, A, B)
    ;   atom(A), atom(B)
    ->  compare(O, A, B)
    ;   atomic(A), atomic(B)
    ->  compare(O, A, B)          % different atomic kinds: stable
    ;   compound(A), compound(B)
    ->  pcompare_compound(O, A, B)
    ;   compare(O, A, B)          % mixed atomic/compound: stable
    ).

pcompare_compound(O, A, B) :-
    functor(A, FA, AA),
    functor(B, FB, AB),
    (   AA < AB
    ->  O = (<)
    ;   AA > AB
    ->  O = (>)
    ;   FA == FB
    ->  A =.. [FA|As],
        B =.. [FB|Bs],
        pcompare_list(O, As, Bs)
    ;   compare(O, FA, FB)        % same arity, different name: stable
    ).

pcompare_list(O, [X|Xs], [Y|Ys]) :-
    pcompare(O1, X, Y),
    (   O1 == (=)
    ->  pcompare_list(O, Xs, Ys)
    ;   O = O1
    ).
