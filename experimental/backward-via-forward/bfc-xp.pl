%% The following does not work with SICStus Prolog, instead one needs
%% to emulate it, see
%% https://stackoverflow.com/questions/65599137/simulating-occurs-check-error-in-sicstus-prolog
:- set_prolog_flag(occurs_check, true).

lt(X, Y, true) :- X < Y.
lt(X, Y, false) :- Y >= X.
plus(X, Y, Z) :- Z is X + Y.
minus(X, Y, Z) :- Z is X - Y.
empty(_) :- fail.

'obc-gtz'(_,
               [:, 'ax1', [to, A, [to, B, A]]],
               ['MkSized', 1, [:, 'ax1', [to, A, [to, B, A]]]]).

'obc-gtz'(_,
               [ :,
                 'ax2',
                 [ to,
                   [to, A, [to, B, C]],
                   [to, [to, A, B], [to, A, C]]
                 ]
               ],
               [ 'MkSized',
                 1,
                 [ :,
                   'ax2',
                   [ to,
                     [to, A, [to, B, C]],
                     [to, [to, A, B], [to, A, C]]
                   ]
                 ]
               ]).

'obc-gtz'(_,
               [:, 'ax3', [to, [to, [neg, A], [neg, B]], [to, B, A]]],
               [ 'MkSized',
                 1,
                 [:, 'ax3', [to, [to, [neg, A], [neg, B]], [to, B, A]]]
               ]).

'obc-gtz'(A, [:, [mp, B, C], D], E) :-
    lt(2, A, F),
    (   F==true
    ->  E=['MkSized', G, [:, [mp, B, C], D]],
        H=['MkSized', I, [:, B, [to, J, D]]],
        minus(A, 2, K),
        obc(K, [:, B, [to, J, D]], H),
        L=['MkSized', M, [:, C, J]],
        minus(A, 1, N),
        minus(N, I, O),
        obc(O, [:, C, J], L),
        plus(I, M, P),
        plus(P, 1, G)
    ;   empty(E)
    ).

obc(A, [:, B, C], D) :-
    lt(0, A, E),
    (   E==true
    ->  'obc-gtz'(A, [:, B, C], D)
    ;   empty(D)
    ).

%% jarr
%% obc(13, [:, P, [to, [to, [to, phi, psi], chi], [to, psi, chi]]], A).

%% imim1
%% obc(15, [:, P, [to, [to, phi, psi], [to, [to, psi, chi], [to, phi, chi]]]], A).

%% loowoz
%% obc(19, [:, P, [to, [to, [to, phi, psi], [to, phi, chi]], [to, [to, psi, phi], [to, psi, chi]]]], A).

%% loolin
%% obc(26, [:, P, [to, [to, [to, phi, psi], [to, psi, phi]], [to, psi, phi]]], A).
