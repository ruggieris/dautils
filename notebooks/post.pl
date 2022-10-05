paths([], [], []).
paths([V|Vs], [L|Ls], [R|Rs]) :-
	path(V, R, L, _),
	paths(Vs, Ls, Rs).
	
exp2cons([], _, []).
exp2cons([E|Es], Vars, [O|Os]) :-
	exp2con(E, Vars, O),
	exp2cons(Es, Vars, Os).

exp2con(N*X, Vars, N*VX) :- !,
	number(N), exp2con(X, Vars, VX).

exp2con(X*N, Vars, N*VX) :- !,
	number(N), exp2con(X, Vars, VX).

exp2con(X+Y, Vars, VX+VY) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(X-Y, Vars, VX-VY) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(X=Y, Vars, VX=VY) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(X=<Y, Vars, VX=<VY) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(X<Y, Vars, VX<VY) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(X>=Y, Vars, VY=<VX) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).
	
exp2con(X>Y, Vars, VY<VX) :- !,
	exp2con(X, Vars, VX), exp2con(Y, Vars, VY).

exp2con(var(I, V), Vars, VX) :- !,
	instance(N, I),
	nth0(N, Vars, INST),
	feature(P, V),
	nth0(P, INST, VX).

exp2con(X, _, X) :-
	number(X), !.

%%%%%%% basic operations on linear systems
%  satisfiable, entails, equivalent
%
% :- equivalent([X =< Y+3],[-3*Y =< -3*X+9]).
%%%%%%%%%%%%%%

equivalent(S, C) :-
	entails(S, C),
	entails(C, S).

entails(S, C) :-
	copy_term(S-C, S1-C1),
	tell_cs(S1),
	is_entailed(C1).

is_entailed([]).
is_entailed([C|Cs]) :- 
	entailed(C),
	is_entailed(Cs).

satisfiable(P) :-
	copy_term(P, CopyP),
	tell_cs(CopyP).	

is_constant(V, P, C) :-
	copy_term(V-P, CopyV-CopyP),
	tell_cs(CopyP),
	sup(CopyV, C), 
	inf(CopyV, C).

tell_cs([]).
tell_cs([C|Cs]) :-  
	{C}, 
	tell_cs(Cs).
	
tells_cs([]).
tells_cs([C|Cs]) :-  
	tell_cs(C),
	tells_cs(Cs).
	
%%%%%%% utilities

lengths([], _).
lengths([V|Vs], N) :-
	length(V, N),
	lengths(Vs, N).

cls :- write('\33\[2J').

:- set_prolog_flag(toplevel_print_options, [quoted(true), portray(true)]). % to print full list
:- set_prolog_flag(answer_write_options,[max_depth(0)]). % to print full list
