exp2conAll([], _, _, []).
exp2conAll([E|Es], XF, XCF, [O|Os]) :-
	exp2con(E, XF, XCF, O),
	exp2conAll(Es, XF, XCF, Os).

exp2con(N*X, XF, XCF, N*VX) :- !,
	number(N), exp2con(X, XF, XCF, VX).

exp2con(X*N, XF, XCF, N*VX) :- !,
	number(N), exp2con(X, XF, XCF, VX).

exp2con(X+Y, XF, XCF, VX+VY) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X-Y, XF, XCF, VX-VY) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X=Y, XF, XCF, VX=VY) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X=<Y, XF, XCF, VX=<VY) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X<Y, XF, XCF, VX<VY) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X>=Y, XF, XCF, VY=<VX) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).
	
exp2con(X>Y, XF, XCF, VY<VX) :- !,
	exp2con(X, XF, XCF, VX), exp2con(Y, XF, XCF, VY).

exp2con(X, _, _, X) :-
	number(X), !.

exp2con(X, XF, XCF, VX) :-
	ground(X), 
    atom_length(X, L),
    L2 is L-2,
   (sub_atom(X, L2, 2, 0, 'CF') -> 
		sub_atom(X, 0, L2, _, X2), feature(P, X2), nth0(P, XCF, VX);
		feature(P, X), nth0(P, XF, VX) ).


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
	
%%%%%%% utilities

cls :- write('\33\[2J').

:- set_prolog_flag(toplevel_print_options, [quoted(true), portray(true)]). % to print full list
:- set_prolog_flag(answer_write_options,[max_depth(0)]). % to print full list
