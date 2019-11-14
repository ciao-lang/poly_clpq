:- module(poly_clpq, [], [assertions, regtypes, basicmodes]).

:- doc(title, "Closed Rational Polyhedra based on CLP(Q)").
:- doc(author, "Jose F. Morales (implementation)").

:- doc(module, "This module implements a (rational, closed) polyhedra
   manipulation library based on CLP(Q) operations.

   The algorithms for the convex hull (@pred{convhull/6}) and project
   (@var{project/3}) operations are based on the paper:

   @begin{verbatim}
   \"Computing convex hulls with a linear solver\", Florence Benoy,
   Andy King, Frédéric Mesnard.  TPLP 5(1-2): 259-271 (2005).
   @end{verbatim}

   This implementation is guaranteed to work for closed polyhedra
   (containing only non-strict inequalities).

   Examples:

@begin{verbatim}
?- use_module(library(poly_clpq)).

yes
?- convhull([X=0,Y=0],[X=1,Y=1],C1),
   convhull(C1,[X=1,Y=0],C2),
   convhull(C2,[X=0,Y=1],C3),
   project([X], C3, C4),
   widen(C4,[X>=0,X=<2],C5).

C1 = [Y>=0,Y=<1,X=Y],
C2 = [X=<1,Y=<X,Y>=0],
C3 = [X=<1,Y=<1,X>=0,Y>=0],
C4 = [X=<1,X>=0],
C5 = [X>=0] ? 

yes
@end{verbatim}

").

% NOTE: Given an integer variable @var{X}, it is possible to
%   approximate rational polyhedra to integer domains as follows:
% 
%   @begin{itemize}
%   @item @tt{X>B} is replaced by @tt{X>=B+1}
%   @item @tt{X<B} is replaced by @tt{X+1=<B}
%   @end{itemize}
%   
%   which is sound when using rational polyhedra to approximate integer
%   domains.
%
% NOTE: Soundness is not guaranteed in the CLP(R) version of the
%   libraries, due to CLP(R) use of floating point numbers (which may
%   lose precision and result in unsound approximations).
%
%   See this paper for more details about this topic:
%     "A Sound Floating-Point Polyhedra Abstract Domain. Liqian Chen,
%     Antoine Mine, and Patrick Cousot. APLAS'08"
%     http://lqchen.github.io/APLAS08_fppol.pdf

:- use_package(library(clpq)).
:- use_module(library(terms_vars), [term_variables/2]).

:- doc(hide, dump_constraints/3).

% ---------------------------------------------------------------------------

:- export(polyhedron/1).
:- regtype polyhedron/1 # "A polyhedron (list representing a
   conjunction of constraints).".
:- doc(polyhedron/1, "@includedef{polyhedron/1}").
polyhedron([]).
polyhedron([C|Cs]) :- constraint(C), polyhedron(Cs).

:- export(constraint/1).
:- regtype constraint/1 # "A linear equality or (non-strict) inequality.".
:- doc(constraint/1, "@includedef{constraint/1}").
constraint(fail).
constraint(A = B) :- linexp(A), linexp(B).
constraint(A >= B) :- linexp(A), linexp(B).
constraint(A =< B) :- linexp(A), linexp(B).

:- export(linexp/1).
:- regtype linexp/1 # "A linear expression.".
:- doc(linexp/1, "@includedef{linexp/1}").
% TODO: var/1 and ground/1 are not regtypes
linexp(  X) :- var(X).
linexp(N*X) :- ground(N), var(X).
linexp( -X) :- linexp(X).
linexp(A+B) :- linexp(A), linexp(B).
linexp(A-B) :- linexp(A), linexp(B).
linexp(  N) :- ground(N).

% ---------------------------------------------------------------------------

:- export(project/3).
:- pred project(+Vars, +X, -Y) :: list(term) * polyhedron * polyhedron 
   # "@var{Y} is the projection of @var{X} to variables @var{Vars}".

project(Vars, X, Y) :-
    to_clpq(X, Cxs),
    project_(Vars, Cxs, Cys),
    from_clpq(Cys, Y).

project_(Vars, Cxs, Cys) :-
    copy_term(Vars-Cxs, CpyVars-CpyCxs),
    clpq_meta(CpyCxs),
    dump_ground(CpyVars, Vars, Vars2, Cys, Cys0),
    dump_constraints(Vars2, YVars, Cys0),
    Vars = YVars. % map back to the original vars

dump_ground([], [], [], Cs, Cs).
dump_ground([CpyVar|CpyVars], [Var|Vars], [Var2|Vars2], Cs, Cs0) :-
    ( ground(CpyVar) ->
        Cs = [Var .=. CpyVar|Cs1]
    ; Var2 = CpyVar, Cs = Cs1
    ),
    dump_ground(CpyVars, Vars, Vars2, Cs1, Cs0).

:- export(convhull/3).
:- pred convhull(+X, +Y, -Z) :: polyhedron * polyhedron * polyhedron
   # "@var{Z} is the convex hull of @var{X} and @var{Y}".

convhull(X, Y, Z) :-
    to_clpq(X, Cxs),
    to_clpq(Y, Cys),
    convhull_(Cxs, Cys, Czs),
    from_clpq(Czs, Z).

convhull_(Cxs, Cys, Czs) :-
    % Get all variables
    term_variables((Cxs,Cys), Vars),
    % Do copies of Cxs and Cys
    copy_term(Vars-Cxs, XVars-Cxs2),
    copy_term(Vars-Cys, YVars-Cys2),
    % All points between Cxs and Cys (with Sig1, Sig2 aux vars)
    scale(Cxs2, Sig1, [], C1s),
    scale(Cys2, Sig2, C1s, C2s),
    add_vect(XVars, YVars, ZVars, C2s, C3s),
    project_(ZVars, [Sig1 .>=. 0, Sig2 .>=. 0, Sig1+Sig2 .=. 1|C3s], Czs),
    %
    Vars = ZVars. % map back to the original vars

scale([], _, Cs, Cs).
scale([C1|C1s], Sig, C2s, C3s) :-
    C1 =.. [RelOp, A1, B1],
    C2 =.. [RelOp, A2, B2],
    mulexp(A1, Sig, A2),
    mulexp(B1, Sig, B2),
    scale(C1s, Sig, [C2|C2s], C3s).

mulexp(  X,   _,     X) :- var(X), !.
mulexp(N*X,   _,   N*X) :- ground(N), var(X), !.
mulexp( -X, Sig,    -Y) :- !, mulexp(X, Sig, Y).
mulexp(A+B, Sig,   C+D) :- !, mulexp(A, Sig, C), mulexp(B, Sig, D).
mulexp(A-B, Sig,   C-D) :- !, mulexp(A, Sig, C), mulexp(B, Sig, D).
mulexp(  N, Sig, N*Sig) :- ground(N).

add_vect([], [], [], Cs, Cs).
add_vect([U|Us], [V|Vs], [W|Ws], C1s, C2s) :-
    add_vect(Us, Vs, Ws, [W .=. U+V|C1s], C2s).

% ---------------------------------------------------------------------------
% Standard widening (Cousot and Halbwachs)
%
%   "P. Cousot and N. Halbwachs. Automatic Discovery of Linear Constraints
%    among Variables of a Program. In Principles of Programming Languages,
%    pages 84–97, Tucson, Arizona, USA, January 1978. ACM."
%
% Intuitively, given successive steps P1 and P2 in the fixpoint
% computation, P3=widen(P1,P2) is defined by all P1 constraints
% safisfied by all points in P2 (constraints entailed by P2).

:- export(widen/3).
:- pred widen(+X, +Y, -Z) :: polyhedron * polyhedron * polyhedron
   # "@var{Z} is the (standard) widening of @var{X} and @var{Y}
      (used to accelerate and guarantee convergence of the fixpoint
      computation)".

widen(X, Y, Z) :-
    to_clpq(X, Cxs),
    to_clpq(Y, Cys),
    widen_(Cxs, Cys, Czs),
    from_clpq(Czs, Z).

widen_(_,[],[]) :- !.
widen_([],_,[]) :- !.
widen_(Cxs,Cys,Czs) :-
    % TODO: copy_term/2 is not needed (we could assert positions, undo, and filter)
    copy_term((Cxs,Cys),(CopyCxs,CopyCys)),
    clpq_meta(CopyCys),
    filter_entailed(CopyCxs,Cxs,Czs).

% Remove each constrain from OrigC that is not entailed by
% the constrain store (we check entailment on C).
filter_entailed([],[],[]).
filter_entailed([C|Cs],[OrigC|OrigCs],[OrigC|Cs2]) :-
    clpq_entailed([C]),!,
    filter_entailed(Cs,OrigCs,Cs2).
filter_entailed([_|Cs],[_|OrigCs],Cs2) :-
    filter_entailed(Cs,OrigCs,Cs2).

% ---------------------------------------------------------------------------

% NOTE: Be aware that the dimension of the polyhedron is dynamically
%   obtained from the variables. Missing variables in one side are
%   implicitly unbound on the other side.
%
%   E.g.
%     contains([X>=Y,Y=0],[X>=1]). --> no (since Y is unbound)
%     contains([X>=0],[X>=1]).     --> yes
%
%   If we wish Y on the first argument to be existentially quantified,
%   we can use project/3 to eliminate it.
%
%     project([X], [X>=Y,Y=0], B), entails([X>=1], B). --> yes (OK)

:- export(contains/2).
:- pred contains(+X, +Y) :: polyhedron * polyhedron
   # "@var{X} contains @var{Y}".
contains(X, Y) :-
    to_clpq(Y, Cys),
    to_clpq(X, Cxs),
    \+ (clpq_meta(Cys), \+ clpq_entailed(Cxs)).

% ---------------------------------------------------------------------------

:- export(is_empty/1).
:- pred is_empty(+X) :: polyhedron # "@var{B} is empty".
is_empty(X) :-
    contains([fail], X).
    % to_clpq(X, Cxs),
    % \+ clpq_meta(Cxs).

:- export(is_universe/1).
:- pred is_universe(+X) :: polyhedron # "@var{B} is a universe".
is_universe(X) :-
    contains(X, []).
    % to_clpq(X, Cxs),
    % \+ \+ clpq_entailed(Cxs).

% ---------------------------------------------------------------------------
% Transform between constrains and CLP(Q) constraints

from_clpq([], []).
from_clpq([X|Xs], [Y|Ys]) :-
    ( from_clpq_(X,Y) -> true
    ; throw(error(unknown_clpq(X), poly_clpq:from_clpq/2))
    ),
    from_clpq(Xs,Ys).

from_clpq_(A.=.B, A=B).
from_clpq_(A.>=.B, A>=B).
from_clpq_(A.=<.B, A=<B).

to_clpq([], []).
to_clpq([X|Xs], [Y|Ys]) :-
    ( to_clpq_(X, Y) -> true
    ; throw(error(cannot_map_to_clpq(X), poly_clpq:to_clpq/2))
    ),
    to_clpq(Xs, Ys).

to_clpq_(fail, 0.=.1).
to_clpq_(A=B, A.=.B).
to_clpq_(A>=B, A.>=.B).
to_clpq_(A=<B, A.=<.B).

% ---------------------------------------------------------------------------

% TODO: missing simplification predicate
% This works as a simplification: (for closed polyhedra!)
%   simplify(A,B) :- convhull_(A,A,B).
% Project works but it seems to keep some unsimplified (lazy?)
%   project([A,B,C,D],[A.>=.1+B,A.>=.2+B,A.>=.3+B,D.>=.C],P). % simpl
%   project([A,B,C,D],[D.>=.C,A.>=.1+B,A.>=.2+B,A.>=.3+B],P). % no simpl (but detects inconsistencies!)

% TODO: check implementation of entailment and projection
%
% @INPROCEEDINGS{Iremia97entailmentand,
%     author = {Fred Mesnard Iremia and Fred Mesnard},
%     title = {Entailment and projection for CLP(B) and CLP(Q) in SICStus Prolog},
%     booktitle = {1st International Workshop on Constraint Reasoning For Constraint Programming},
%     year = {1997}
% }

