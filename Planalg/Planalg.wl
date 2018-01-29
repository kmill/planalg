(* ::Package:: *)

BeginPackage["Planalg`"];


ClearAll["Planalg`*", "Planalg`*`*", "Planalg`*`*`*"];


(* ::Section:: *)
(*Utilities*)


ImpartLinearity::usage="Makes a certain pattern into a linear operator that absorbs
linear combinations.";

QuantumInt::usage="QuantumInt[q, n] gives [n]_q.";

SetPartitions::usage="SetPartitions[list] gives all set partitions of list.
SetPartitions[n] = SetPartitions[Range[n]].";

Gramian::usage="Gramian[basis] gives the Gram matrix for the basis.";


Begin["`Private`"];

ImpartLinearity[head_,patfn_,resfn_]:=Module[{x1,x2},
	head /: patfn[x1_] + patfn[x2_] := resfn[x1+x2];
	head /: coeff_ patfn[x1:_] /; FreeQ[coeff, _head] := resfn[coeff x1];
	];

QuantumInt[q_, n_Integer] := Plus@@Table[q^(n-1-2i), {i, 0, n-1}];

SetPartitions[{}] := {{}};
SetPartitions[{x_,xs___}] :=
	Map[Sequence@@{
			Prepend[#,{x}],
			Sequence@@ReplaceList[#,{a___,is_,b___}:>{a,Prepend[is,x],b}]}&,
		SetPartitions[{xs}]];
SetPartitions[n_Integer] := SetPartitions[Range[n]];

(*Adapted from a one-liner by acl and Mr.Wizard at
https://mathematica.stackexchange.com/questions/7887/best-way-to-create-symmetric-matrices *)
CreateSymmetric[f_Function, basis_] :=
	With[{upper = Table[f@@basis[[{i,j}]], {i,Length@basis}, {j,i}]},
		Join[upper, Rest /@ Flatten[upper, {2}], 2]];

Gramian[basis_List] := CreateSymmetric[PTr[#1**PDual@#2]&, basis];

End[];


(* ::Section:: *)
(*Monoidal category*)


(* ::Text:: *)
(*Each category needs to implement NonCommutativeMultiply (**) for the composition operation.*)
(**)
(*Each monoidal category needs to implement CircleTimes (\[CircleTimes], typed as ESC c * ESC). Be careful that ** has higher precedence than \[CircleTimes].  The tensor operation is bottom-to-top if you imaging composition as being horizontal.*)


SetAttributes[CircleTimes, {Flat, OneIdentity, Protected}];


(* ::Section:: *)
(*Trace*)


PTr::usage="PTr[element of homset]. Calculates a trace depending on the category.";


(* ::Section:: *)
(*Dual*)


PDual::usage="PDual[element of homset]. Calculates a dual depending
on the category.";


(* ::Section:: *)
(*(Virtual) Temperley-Lieb category*)


(* ::Text:: *)
(*The Temperley-Lieb category over c is all \[DoubleStruckCapitalC][c]-linear combinations of non-overlapping properly embedded paths in a disk.  Free loops take the value c.*)
(**)
(*The virtual Temperley-Lieb category, a.k.a. the Brauer category, allows overlapping paths.*)


TL::usage="TL[c,m,n,linear combination of products of P's with
poly(c) coefficients], with n boundary vertices on the right and m on the left.";
P::usage="P[i,j] represents an undirected path between i and j.";

SimplifyTL::usage="SimplifyTL[x] takes all TL subexpressions in x and
collects basis terms.";

TLId::usage="TLId[c,n] gives the identity in TL[c,n,n,...].";
TLE::usage="TLE[c,n,i] gives the generator e_i.";

JWProjector::usage="JWProjector[q,n] gives the TLc Jones-Wenzl Projector
in TL[-q-q^-1,n,n,...]";

TLMakeBasis::usage="TLMakeBasis[c,m,n,Virtual->boolean] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c). Virtual is false by default.";
Options[TLMakeBasis] = {Virtual->False};


Begin["`Private`TL`"];

ImpartLinearity[TL, TL[c_,m_,n_,#]&, TL[c,m,n,#]&];

ClearAll[P];
SetAttributes[P, {Orderless}];
P[i_, i_] := P[];
P /: P[i_,j_] P[i_,k_] := P[j,k];
P /: P[i_,j_]^2 := P[];

tlEliminateLoops[c_, v_] := Expand[v, _P] /. P[] -> c;

ClearAll[SimplifyTL];
Module[{PComb},
	SetAttributes[PComb, {Orderless}];
	PComb /: PComb[ps1___] PComb[ps2___] := PComb[ps1, ps2];

	SimplifyTL[TL[c_, m_, n_, v_]] := TL[c, m, n,
		Collect[(tlEliminateLoops[c, v] /. p_P:>PComb@p), _PComb, FullSimplify] /.
			p_PComb:>Times@@p
	];
];

(*Markov trace*)
PTr[TL[c_, m_, m_, v_]] := tlEliminateLoops[c, v Times@@Table[P[i,i+m],{i,m}]]/c^m;

tlRenumber[v_, f_Function] := v /. p_P:>(f/@p);

PDual[TL[c_,m_,n_,v_]] := TL[c, n, m, tlRenumber[v, If[#<=n, #+m, #-n]&]];
	
TL /: TL[c_, m1_, n1_, v1_] \[CircleTimes] TL[c_, m2_, n2_, v2_] :=
	TL[c, m1+m2, n1+n2,
		tlRenumber[v1, If[#<=n1, #, #+n2]&]
		* tlRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

TL /: TL[c_, l_, m_, v2_] ** TL[c_, m_, n_, v1_] :=
	TL[c, l, n,
		tlRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* tlRenumber[v1, If[#<=n, #, #+l]&]
	] // SimplifyTL; (* must simplify to eliminate internal vertices *)

TLId[c_, n_] := TL[c, n, n, Times@@Table[P[i, i+n], {i, n}]];

TLE[c_,n_,i_] /; i<n := TL[c, n, n,
	Times@@Table[If[j==i || j==i+1, Nothing, P[j, j+n]], {j, n}]
	* P[i,i+1] P[i+n,i+n+1]
];

JWProjector[q_, n_] /; n<=1 := TLId[-QuantumInt[q, 2], n];
JWProjector[q_, n_] := JWProjector[q, n] = With[
	{c = -QuantumInt[q, 2],
	 p = JWProjector[q, n-1]},
	p \[CircleTimes] TLId[c,1]
	+ (QuantumInt[q,n-1]/QuantumInt[q,n])
	* (p \[CircleTimes] TLId[c,1]) ** TLE[c, n, n-1] ** (p \[CircleTimes] TLId[c,1])
	// SimplifyTL
];

tlMakePic[m_,n_,diag_] := Graphics[Join[
	{LightRed, EdgeForm[Thin], Rectangle[{0, 0}, {Max[m, n], Max[m, n]+1}],
		Black},
	tlMakePathPic[m, n, #]&/@diag
]];
tlMakePathPic[m_,n_,P[i_,j_]] := With[{
	d = 2 Abs[If[i<=n,i,i-n]-If[j<=n,j,j-n]]/3,
	w = Max[m,n]},
	
	Which[
	i<=n&&j<=n,
	BezierCurve[{{w,i},{w-d,i},{w-d,j},{w,j}}],

	i<=n,
	BezierCurve[{{w,i},{w-d,i},{d,j-n},{0,j-n}}],

	True,
	BezierCurve[{{0,i-n},{d,i-n},{d,j-n},{0,j-n}}]
]];

TL /: MakeBoxes[t:TL[c_, m_, n_, v_], f:StandardForm] := Module[{PComb},
	SetAttributes[PComb, {Orderless}];
	PComb /: PComb[ps1___] PComb[ps2___] := PComb[ps1, ps2];
	With[{v2 = Expand[v,_P]
			/.{p_P:>PComb@p}
			/.{p_PComb:>tlMakePic[m,n,List@@p]}},
		With[{box = RowBox[{"TL", "[", RowBox[{
				MakeBoxes[c,f], ",", MakeBoxes[m,f], ",", MakeBoxes[n,f],",",
				MakeBoxes[v2, f]
			}], "]"}]},
			InterpretationBox[box, t]]]];

tlAllPairs[{}] := {1};
tlAllPairs[{x_,xs___}] :=
	ReplaceList[{xs}, {a___,y_,b___} :> Sequence@@(P[x,y] tlAllPairs[{a,b}])];
tlAllPairs[n_Integer] := tlAllPairs[Range[n]];

tlPlanPairs[{}] := {1};
tlPlanPairs[l_List] /; OddQ[Length[l]] = {};
tlPlanPairs[{x_,xs___}] :=
	ReplaceList[{xs}, {a___,y_,b___} :>
		Sequence@@(P[x,y] Times@@@Tuples[{tlPlanPairs[{a}], tlPlanPairs[{b}]}])];

TLMakeBasis[c_,m_,n_,OptionsPattern[]] := 
	If[OptionValue[Virtual],
		TL[c,m,n,#]&/@tlAllPairs[m+n],
		TL[c,m,n,#]&/@tlPlanPairs[Join[Range[n], Range[n+m, n+1, -1]]]
	];

End[];


(* ::Section:: *)
(*Flow category*)


Flow::usage="Flow[Q,m,n,linear combination of products of FV's with poly(Q)
coefficients], with n boundary vertices on the right and m on the left.";
FV::usage="FV[i,j,...] is a vertex incident to i,j,....";

FlowMakeBasis::usage="FlowMakeBasis[Q,m,n,Virtual->boolean] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c). Virtual is true by default.";
Options[FlowMakeBasis] = {Virtual->True};

FlowId::usage="Flow[Q,m] is the identity in Flow[Q,m,m,...].";


Begin["`Private`Flow`"];

ImpartLinearity[Flow, Flow[Q_,m_,n_,#]&, Flow[Q,m,n,#]&];

ClearAll[FPart];
SetAttributes[FV, {Orderless}];
FV[] = 1;
FV[_] = 0;
FV[a_,a_,bs___] := FLoop[] FV[bs];
FV /: FV[a_, b___] FV[a_, c___] := FV[b, c] - FV[b] FV[c];
FV /: FV[a_, b___]^2 := FV[b, b] - FV[b]^2;

flEliminateLoops[Q_, v_] := Expand[v, _FV] /. FLoop[] -> Q - 1;

Module[{FComb},
	SetAttributes[FComb, {Orderless}];
	FComb /: FComb[fvs1___] FComb[fvs2___] := FComb[fvs1, fvs2];
	
	SimplifyFlow[Flow[Q_,m_,n_,v_]] := Flow[Q, m, n,
		Collect[(flEliminateLoops[Q, v] /. fv_FV:>FComb@fv), _FComb, FullSimplify]
			/. comb_FComb:>Times@@comb
	];
];
	
PTr[Flow[Q_,m_,m_,v_]] :=
	flEliminateLoops[Q, v Times@@Table[FV[i,i+m],{i,m}]]/(Q-1)^m;

flRenumber[v_, f_Function] := v /. fv_FV:>(f/@fv);

PDual[Flow[Q_,m_,n_,v_]] :=
	Flow[Q, n, m, flRenumber[v, If[#<=n, #+m, #-n]&]];

Flow /: Flow[Q_,m1_,n1_,v1_] \[CircleTimes] Flow[Q_,m2_,n2_,v2_] :=
	Flow[Q, m1, n2,
		flRenumber[v1, If[#<=n1, #, #+n2]&]
		* flRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

Flow /: Flow[Q_,l_,m_,v2_] ** Flow[Q_,m_,n_,v1_] :=
	Flow[Q, l, n,
		flRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* flRenumber[v1, If[#<=n, #, #+l]&]
	] // SimplifyFlow;

FlowId[Q_, n_] := Flow[Q, n, n, Times@@Table[FV[i, i+n], {i, n}]];

flMakePic[m_,n_,diag_List] := Graphics[Join[
	{LightRed, EdgeForm[Thin], Rectangle[{0, 0}, {2, Max[m,n]+1}], Black},
	Join@@MapIndexed[flMakeVertPic[m, n, #2[[1]]/(1+Length@diag)*(1+Max[m,n]), #1]&,
		diag, {1}]
]];
flMakeVertPic[m_,n_,y_,v_FV] := With[{
	ipt = If[#<=n, {2,#}, {0,#-n}]&},
	Append[Line[{ipt[#],{1,y}}]&/@List@@v, Disk[{1,y}, 0.08]]
];
Flow /: MakeBoxes[fl:Flow[Q_,m_,n_,v_], f:StandardForm] := Module[{FComb},
	SetAttributes[FComb, {Orderless}];
	FComb /: FComb[fvs1___] FComb[fvs2___] := FComb[fvs1, fvs2];
	With[{v2 = Expand[v,_FV]
			/.{fv_FV:>FComb@fv}
			/.{fc_FComb:>flMakePic[m,n,List@@fc]}},
		With[{box = RowBox[{"Flow", "[", RowBox[{
				MakeBoxes[Q,f], ",", MakeBoxes[m,f], ",", MakeBoxes[n,f], ",",
				MakeBoxes[v2,f]
			}], "]"}]},
			InterpretationBox[box, t]
		]]];

(*Computes all elements that correspond to planar graphs.*)
flPlanarPartitions[{}] = {1};
flPlanarPartitions[{s_,ss___}] :=
	Map[Function[rest,
		With[{
			this = Prepend[rest, s],
			split = Select[SplitBy[{ss}, MemberQ[rest,#]&],
						!IntersectingQ[rest,#]&]},
			If[AnyTrue[split, Length[#]<2&],
				Nothing,
				Sequence@@(FV@@this Times@@@Tuples[flPlanarPartitions/@split])]]]
	, Subsets[{ss}, {1,Length@{ss}}]];

FlowMakeBasis[Q_,m_,n_,OptionsPattern[]] :=
	If[OptionValue[Virtual],
		Map[Flow[Q,m,n,Times@@FV@@@#]&,
			Select[SetPartitions[m+n], AllTrue[#, Length[#]>1&]&]],
		Flow[Q,m,n,#]&/@flPlanarPartitions[Join[Range[n],Range[n+m,n+1,-1]]]
	];

End[];


(* ::Section:: *)
(*Deligne partition category*)


DP::usage="DP[t,m,n,linear combination of DS's over \[DoubleStruckCapitalC](t)]";
DS::usage="DS[...] is a subset of m+n";

SimplifyDP::usage="SimplifyDP[DP[...]] puts the DP into normal form.";

DPId::usage="DPId[t,n] gives the identity in DP[t,n,n,...].";

DPMakeBasis::usage="DPMakeBasis[t,m,n] gives a basis for DP[t,m,n,...].";


Begin["`Private`DP`"];

ImpartLinearity[DP, DP[t_,m_,n_,#]&, DP[t,m,n,#]&];

(*These rules make sense in the context of how composition works. DS[] will appear
when there is an internal partition.*)
SetAttributes[DS, {Orderless}];
DS /: DS[a_, xs___] DS[a_, ys___] := DS[xs, ys];
DS[a_,a_,xs___] := DS[xs];
DS /: _DS^2 = DS[];

SetAttributes[DPart,{Orderless}];
DPart /: DPart[ss1___] DPart[ss2___] := DPart[ss1, ss2];

dpEliminateEmpties[t_,v_] := Expand[v, _DS] /. DS[] -> t;

SimplifyDP[DP[t_,m_,n_,v_]] := DP[t,m,n,
	Collect[(dpEliminateEmpties[t, v] /. d_DS:>DPart@d), _DPart, FullSimplify]
	 /. d_DPart:>Times@@d
];

(*TODO should this be normalized?*)
PTr[DP[t_,m_,m_,v_]] := dpEliminateEmpties[t, v Times@@Table[DS[i,i+m],{i,m}]]/t^m;

dsRenumber[v_, f_Function] := v /. d_DS:>(f/@d);

PDual[DP[t_,m_,n_,v_]] := DP[t,n,m,dsRenumber[v, If[#<=n, #+m, #-n]&]];

DP /: DP[t_, m1_, n1_, v1_] \[CircleTimes] DP[t_, m2_, n2_, v2_] :=
	DP[t, m1+m2, n1+n2,
		dsRenumber[v1, If[#<=n1, #, #+n2]&]
		* dsRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

DP /: DP[t_, l_, m_, v2_] ** DP[t_, m_, n_, v1_] :=
	DP[t, l, n,
		dsRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* dsRenumber[v1, If[#<=n, #, #+l]&]
	] // SimplifyDP; (* must simplify to eliminate internal partitions *)

DPId[t_, n_] := DP[t, n, n, Times@@Table[DS[i, i+n], {i, n}]];

dpMakePic[m_,n_,diag_List] := Graphics[Join[
	{LightRed, EdgeForm[Thin], Rectangle[{0, 0}, {2, Max[m,n]+1}], Black},
	Join@@MapIndexed[dpMakeVertPic[m, n, #2[[1]]/(1+Length@diag)*(1+Max[m,n]), #1]&,
		diag, {1}]
]];
dpMakeVertPic[m_,n_,y_,v_DS] := With[{
	ipt = If[#<=n, {2,#}, {0,#-n}]&},
	Append[Line[{ipt[#],{1,y}}]&/@List@@v, Disk[{1,y}, 0.08]]
];
DP /: MakeBoxes[fl:DP[t_,m_,n_,v_], f:StandardForm] :=
	With[{v2 = Expand[v,_DS]
			/.{fv_DS:>DPart@fv}
			/.{fc_DPart:>dpMakePic[m,n,List@@fc]}},
		With[{box = RowBox[{"DP", "[", RowBox[{
				MakeBoxes[t,f], ",", MakeBoxes[m,f], ",", MakeBoxes[n,f], ",",
				MakeBoxes[v2,f]
			}], "]"}]},
			InterpretationBox[box, t]
		]];

DPMakeBasis[t_,m_,n_] := DP[t,m,n,Times@@DS@@@#]&/@SetPartitions[m+n];

End[];


(* ::Section:: *)
(*Planar diagrams*)


PD::usage="PD[planar diagram elements..]";
V::usage="V[i,j,..] is a flat vertex in a PD with edge labels i,j,.. in
counterclockwise order.";
X::usage="X[i,j,k,l] is a crossing with V[i,k] the understrand and V[j,l]
the overstrand.";
VirtX::usage="VirtX[i,j,k,l] is a virtual crossing of V[i,k] and V[j,l].";


Begin["`Private`PD`"];

End[];


(* ::Section:: *)
(*Abstract category*)


AbId::usage="AbId[n] is an abstract identity element.";
AbB::usage="AbB[m,n] is a braid from m\[CircleTimes]n to n\[CircleTimes]m."
AbBInv::usage="AbBInv[m,n] is the inverse of AbB[n,m].";
AbCup::usage="AbCup[n] is nested cups from 0 to n\[CircleTimes]n.";
AbCap::usage="AbCap[n] is nested caps from n\[CircleTimes]n to 0.";
AbV::usage="AbV[m,n] is a degree-(m+n) vertex from n to m.";


Begin["`Private`Ab`"];

DecomposeAbB[AbB[n_,0]|AbBInv[n_,0]|AbB[0,n_]|AbBInv[0,n_]] := AbId[n];
DecomposeAbB[AbB[1,1]] = AbB[1,1];
DecomposeAbB[AbB[n_,m_]] :=

DecomposeBraids[x_]

End[];


(* ::Section:: *)
(*End of definitions*)


Print["Loaded ",$Context];
EndPackage[];
