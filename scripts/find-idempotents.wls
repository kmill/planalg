#!/usr/bin/env wolframscript
(* ::Package:: *)

(* This script finds the indecomposable idempotents of the enomorphism algebra
with the specified basis. It may require tweaking the assumptions of FullSimplify
when computing soln. *)

<<Planalg`

(* Basis of our endomorphism algebra *)
basis = FlowMakeBasis[Q,2,2]


(* Generate a generic vector v in the algebra *)
coeffs = Array[a,Length@basis]
v = Plus@@Table[a[i] basis[[i]], {i,1,Length[basis]}]

u = v**v-v
relations = Coefficient[(u)[[4]],#[[4]]]&/@basis


(* Solve for each relation being zero *)
(* Might require some assumptions on the parameters of the category
e.g Q > 1 for flow. *)
soln = FullSimplify[Solve[relations == (0&)/@relations,coeffs],Assumptions->Q>1]


vecs = Union[Simplify[((soln/.{(_->y_):>y}//FullSimplify)/.{{0,0,0,0}->Nothing})]]


idems = basis.#&/@Complement[vecs//FullSimplify,Union[Plus@@@Tuples[vecs,2]]//FullSimplify]
