#!/usr/bin/env wolframscript
(* ::Package:: *)

(*A script for computing the trace radical of the TL/Brauer algebras (but could be adapted)*)


<<Planalg`


(*Configuration*)
strandNumber = 4;
virtual = True;
Clear[c];
c = -2;


(*Initialization*)
basis = TLMakeBasis[c,strandNumber,strandNumber,Virtual->virtual];
n = Length[basis];
vars = a/@Range[n];
vec = vars.basis;
trace[x_] := c^strandNumber * PTr[x]


(*Main computation*)
relation[x_]:=trace[vec**x];
groeb = GroebnerBasis[relation/@basis,vars]


(*This part only works if groeb is a list of *linear* equations*)
vectorize[term_]:= Coefficient[term,#]&/@vars;
basis.#&/@NullSpace[vectorize/@groeb]
