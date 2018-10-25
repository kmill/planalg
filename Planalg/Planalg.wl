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


Begin["`Private`"];

ImpartLinearity[head_,patfn_,resfn_]:=With[{x1=Unique["x1"], x2=Unique["x2"]},
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

End[];


(* ::Section:: *)
(*Monoidal category*)


(* ::Text:: *)
(*Each category needs to implement NonCommutativeMultiply (**) for the composition operation.*)
(**)
(*Each monoidal category needs to implement CircleTimes (\[CircleTimes], typed as ESC c * ESC). Be careful that ** has higher precedence than \[CircleTimes].  The tensor operation is bottom-to-top if you imaging composition as being horizontal.*)


Unprotect[CircleTimes];
ClearAll[CircleTimes];
SetAttributes[CircleTimes, {Flat, OneIdentity}];
Protect[CircleTimes];


(* ::Subsection:: *)
(*Objects*)


PLeft::usage="PLeft[element of homset]. Gives left object.";
PRight::usage="PRight[element of homset]. Gives right object.";

Begin["`Private`Monoidal`"];
PLeft[ncm_NonCommutativeMultiply] := PLeft@First@ncm;
PLeft[tens_CircleTimes] := Plus@@(PLeft/@tens);

PRight[ncm_NonCommutativeMultiply] := PRight@Last@ncm;
PRight[tens_CircleTimes] := Plus@@(PRight/@tens);
End[];

PCoeffs::usage="PCoeffs[cat] gives a list of {coefficient,simple element} pairs.
What this means depends on the category.";
PSimplify::usage="PSimplify[cat] puts the hom into a normal form.";


(* ::Subsection:: *)
(*Trace*)


PTr::usage="PTr[element of homset]. Calculates a trace depending on the category.";
Options[PTr] = {Normalized->False};


(* ::Subsection:: *)
(*Dual*)


PDual::usage="PDual[element of homset]. Calculates a dual depending
on the category.";


(* ::Subsection:: *)
(*Scalars*)


PScalar::usage="PScalar[element of (0,0)homset]. Extracts scalar value.";


(* ::Subsection:: *)
(* Functions *)


Gramian::usage="Gramian[basis] gives the Gram matrix for the basis.";
Options[Gramian] = {Trace->PTr, Dual->PDual};


Begin["`Private`Cats`"];

(*Adapted from a one-liner by acl and Mr.Wizard at
https://mathematica.stackexchange.com/questions/7887/best-way-to-create-symmetric-matrices *)
CreateSymmetric[f_Function, basis_] :=
	With[{upper = Table[f@@basis[[{i,j}]], {i,Length@basis}, {j,i}]},
		Join[upper, Rest /@ Flatten[upper, {2}], 2]];

Gramian[basis_List, OptionsPattern[]] := With[
	{tr = OptionValue[Trace], dual = OptionValue[Dual]},
	CreateSymmetric[tr[#1**dual@#2]&, basis]
];

End[];


(* ::Section:: *)
(*Planar diagrams*)


PD::usage="PD[planar diagram elements..]";
V::usage="V[i,j,..] is a flat vertex in a PD with edge labels i,j,.. in
counterclockwise order.";
X::usage="X[i,j,k,l] is a crossing with V[i,k] the understrand and V[j,l]
the overstrand.";
VirtX::usage="VirtX[i,j,k,l] is a virtual crossing of V[i,k] and V[j,l].";

P::usage="P[i,j] is a path from i to j. For oriented diagrams, the path is oriented.";
Xp::usage="Xp[i,j,k,l] is a crossing with P[i,k] the understrand
and P[l,j] the overstrand.";
Xm::usage="Xm[i,j,k,l] is a crossing with P[i,k] the understrand
and P[j,l] the overstrand.";


Begin["`Private`PD`"];

End[];


(* ::Subsection:: *)
(*Example data*)


FlatVertG::usage = "FlatVertG[name] gets an example planar diagram for a flat vertex graph";


Begin["`Private`PD`"];
FlatVertG["K3_1"] = PD[X[3,1,4,6],X[1,2,5,4],X[2,3,6,5]];
FlatVertG["loop"] = PD[V[1,1]];
FlatVertG["theta"] = PD[V[1,2,3],V[1,3,2]];
FlatVertG["handcuff"] = PD[V[1,1,2],V[2,3,3]];
FlatVertG["wedge"] = PD[V[1,1,2,2]];
FlatVertG["wedgeover"] = PD[X[1,4,3,2],V[1,2,3,4]];
FlatVertG["linked_handcuff"] = PD[X[7,1,6,2],X[3,7,2,5],V[1,3,4],V[4,5,6]];
FlatVertG["k4"] = PD[V[1,2,4],V[2,3,5],V[3,1,6],V[4,5,6]];
FlatVertG["k33"] = PD[X[9,6,5,11], V[1,4,5], V[1,6,2], V[2,7,3], V[3,8,4], V[7,9,10], V[8,10,11]];
FlatVertG["k5"] = PD[V[1,2,3,4],V[4,7,12,13],V[13,17,19,20],V[20,18,14,8],V[8,9,5,1],X[6,2,5,10], X[11,7,3,6], X[16,17,12,11], X[19,16,15,18], X[14,15,10,9]];
FlatVertG["K3_1_tunneled"] = PD[X[4,1,5,8], X[5,1,6,2], X[3,8,2,7], V[7,6,9], V[4,3,9]];
FlatVertG["L4_1"] = PD[X[6,1,7,2], X[3,8,2,7], X[8,3,5,4], X[4,5,1,6]];
End[];


(* ::Section:: *)
(*Abstract category*)


(* ::Text:: *)
(*This is supposed to be an abstract braided monoidal category with integer objects, but for simplicity the generator  object is self-dual.*)


AbId::usage="AbId[n] is an abstract identity element.";
AbB::usage="AbB[] is a braid from 1\[CircleTimes]1 to 1\[CircleTimes]1. (Right-handed crossing.)";
AbBInv::usage="AbBInv[] is the inverse of AbB[].";
AbTrans::usage="AbTrans[] is a transpose. (Virtual crossing.)";
AbCup::usage="AbCup[] is a cup from 0 to 1\[CircleTimes]1.";
AbCap::usage="AbCap[] is a cap from 1\[CircleTimes]1 to 0.";
AbV::usage="AbV[m,n] is a degree-(m+n) vertex from n to m.";

FromPD::usage="FromPD[pd] converts a planar diagram to a categorical expression.";
Options[FromPD]={Left->{}, Right->{}};

AbGraphForm::usage="AbGraphForm[v] displays v in a 2D form.";


Begin["`Private`Ab`"];

AbId /: AbId[n_] \[CircleTimes] AbId[m_] := AbId[n+m];
AbId /: AbId[0] \[CircleTimes] v_ := v;
AbId /: v_ \[CircleTimes] AbId[0] := v;

AbQ[_AbId|_AbB|_AbBInv|_AbTrans|_AbCup|_AbCap|_AbV] = True;
AbQ[_] = False;

PLeft[AbId[n_]] := n;
PLeft[_AbB|_AbBInv|_AbTrans] := 2;
PLeft[_AbCup] := 2;
PLeft[_AbCap] := 0;
PLeft[AbV[m_,n_]] := m;

PRight[AbId[n_]] := n;
PRight[_AbB|_AbBInv|_AbTrans] := 2;
PRight[_AbCup] := 0;
PRight[_AbCap] := 2;
PRight[AbV[m_,n_]] := n;

splitFrontier::badSplit="Invalid split for splitFrontier.";

splitFrontier[frontier_List, p_List] := Replace[
	SplitBy[frontier, MemberQ[p,#]&], {
		{} :> {0, {}, 0, #&, 0},
		{a_}/;IntersectingQ[a,p] :> {0, a, 0, #&, 0},
		{a_,b_}/;IntersectingQ[a,p] :> {0, a, Length@b, Join[#,b]&, 0},
		{a_,b_}/;IntersectingQ[b,p] :> {Length@a, b, 0, Join[a,#]&, 0},
		{a_,b_,c_}/;IntersectingQ[b,p] :> {Length@a, b, Length@c, Join[a,#,c]&, 0},
		{a_,b_,c_}/;IntersectingQ[a,p] :> (* have to rotate *)
			If[Length[a] <= Length[c],
				{Length@b, Join[c,a], 0, Join[b,#]&, Length[a]},
				{0, Join[c,a], Length@b, Join[#,b]&, -Length[c]}],
		_ :> (Message[splitFrontier::badSplit]; $Failed)
	}];

calculateOpp[splitF_, p_] :=
	Reverse[Join@@Reverse@Select[SplitBy[List@@p, MemberQ[splitF[[2]],#]&],
								!IntersectingQ[splitF[[2]],#]&]];

convert[frontier_List, v_V] :=
	With[{f=splitFrontier[frontier, List@@v]},
		With[{opp=calculateOpp[f, v]},
			{f[[4]][opp], f[[5]],
				AbId[f[[1]]] \[CircleTimes] AbV[Length@opp, Length@f[[2]]] \[CircleTimes] AbId[f[[3]]]}
	]];

activateX[{False,False,False,False},_] =
	(AbId[1] \[CircleTimes] AbB[] \[CircleTimes] AbId[1]) ** (AbCup[] \[CircleTimes] AbCup[]);
activateX[{True,False,False,False}|{False,False,True,False},_] =
	(AbId[1] \[CircleTimes] AbB[]) ** (AbCup[] \[CircleTimes] AbId[1]);
activateX[{False,True,False,False}|{False,False,False,True},_] =
	(AbB[] \[CircleTimes] AbId[1]) ** (AbId[1] \[CircleTimes] AbCup[]);
activateX[{True,True,False,False}|{False,False,True,True},_] = AbBInv[];
activateX[{False,True,True,False}|{True,False,False,True},_] = AbB[];
activateX[{True,True,True,False}|{True,False,True,True},_] =
	(AbCap[] \[CircleTimes] AbId[1]) ** (AbId[1] \[CircleTimes] AbB[]);
activateX[{False,True,True,True}|{True,True,False,True},_] =
	(AbId[1] \[CircleTimes] AbCap[]) ** (AbB[] \[CircleTimes] AbId[1]);
activateX[{True,True,True,True},1|3] =
	(AbCap[] \[CircleTimes] AbCap[]) ** (AbId[1] \[CircleTimes] AbB[] \[CircleTimes] AbId[1]);
activateX[{True,True,True,True},2|4] =
	(AbCap[] \[CircleTimes] AbCap[]) ** (AbId[1] \[CircleTimes] AbBInv[] \[CircleTimes] AbId[1]);

convert[frontier_List, x_X] :=
	With[{
		f=splitFrontier[frontier, List@@x],
		xf=MemberQ[frontier,#]&/@List@@x
	},
	{f[[4]][calculateOpp[f, x]], f[[5]],
		AbId[f[[1]]]
			\[CircleTimes] activateX[xf, If[Length@f[[2]] > 0,
								First@FirstPosition[x, f[[2,1]]]]]
			\[CircleTimes] AbId[f[[3]]]}
	];

activateVirtX[0] = (AbId[1] \[CircleTimes] AbTrans[] \[CircleTimes] AbId[1]) ** (AbCup[] \[CircleTimes] AbCup[]);
activateVirtX[1] = (AbId[1] \[CircleTimes] AbTrans[]) ** (AbCup[] \[CircleTimes] AbId[1]);
activateVirtX[2] = AbTrans[];
activateVirtX[3] = (AbCup[] \[CircleTimes] AbId[1]) ** (AbId[1] \[CircleTimes] AbTrans[]);
activateVirtX[4] = (AbCap[] \[CircleTimes] AbCap[]) ** (AbId[1] \[CircleTimes] AbTrans[] \[CircleTimes] AbId[1]);

convert[frontier_List, x_VirtX] :=
	With[{
		f=splitFrontier[frontier, List@@x],
		xc=Count[x,_?(MemberQ[frontier,#]&)] },
		
	{f[[4]][calculateOpp[f,x]], f[[5]],
		AbId[f[[1]]] \[CircleTimes] activateVirtX[xc] \[CircleTimes] AbId[f[[3]]]}
	];

activatePPath[0] = AbCup[];
activatePPath[1] = AbId[1];
activatePPath[2] = AbCap[];

convert[frontier_List, p_P] :=
	With[{
		f=splitFrontier[frontier, List@@p],
		pc=Count[p,_?(MemberQ[frontier,#]&)]},
	{f[[4]][calculateOpp[f,p]], f[[5]],
		AbId[f[[1]]] \[CircleTimes] activatePPath[pc] \[CircleTimes] AbId[f[[3]]]}
	];

(*For re-routing i inlets on the bottom side around the right to the top side.*)
rotNCMmul[a_, b_,left_, 0] := a ** b;
rotNCMmul[a_,b_,left_,i_] /;i>0 := rotNCMmul[a,
	(AbCap[]\[CircleTimes]AbId[left])**(AbId[1]\[CircleTimes]b\[CircleTimes]AbId[1]) ** AbCup[],
	left, i-1];
rotNCMmul[a_,b_,left_,i_] /;i<0 := rotNCMmul[a,
	(AbId[left]\[CircleTimes]AbCap[])**(AbId[1]\[CircleTimes]b\[CircleTimes]AbId[1]) ** AbCup[],
	left, i+1];

FromPD::incomplete="Incomplete planar diagram.";
FromPD::problem="The tangle wanted to snake around the right-hand boundary edges. This
might be a problem with Planalg?";
FromPD[pd_PD, OptionsPattern[]] := Module[{make, fresh},
	make[val_, OptionValue[Left], PD[]] := val;
	make[_, _, PD[]] := (Message[FromPD::incomplete]; $Failed);
	make[val_, frontier_, rest_] := With[{
		pos=First@Ordering[Length@Complement[List@@#, frontier]+Length@Complement[frontier, List@@#]&/@rest,1]
		},(*Print["make",{frontier, rest[[pos]], rest}];*)
		With[{c=convert[frontier, rest[[pos]]]},
			If[c[[2]] != 0 && Length@OptionValue[Right] != 0,
				Message[FromPD::problem]; Return[$Failed]];
			make[rotNCMmul[c[[3]], val, Length@frontier, c[[2]]], c[[1]], Delete[rest, pos]]]];
	fresh = Max[List@@@List@@pd]+1;
	make[NonCommutativeMultiply[], OptionValue[Right], pd //. {
		h_[a___,i_,b___,i_,c___]:>With[{j=fresh++},Sequence@@{P[i,j],h[a,i,b,j,c]}]
	}]//Replace[#,{NonCommutativeMultiply[v_]:>v}]&
];

MakeBoxes[AbGraphForm[v_], StandardForm] := Module[{make},
	make[mult_NonCommutativeMultiply] :=
		GridBox[{make/@List@@mult},
			RowAlignments->Center, ColumnLines->True];
	make[tens_CircleTimes] := GridBox[{make[#]}&/@Reverse[List@@tens],
								RowLines->True];
	make[val_] := MakeBoxes[val, StandardForm];
	make[v]
];

End[];


(* ::Section:: *)
(*(Virtual) Temperley-Lieb category*)


(* ::Text:: *)
(*The Temperley-Lieb category over c is all \[DoubleStruckCapitalC][c]-linear combinations of non-overlapping properly embedded paths in a disk.  Free loops take the value c.*)
(**)
(*The virtual Temperley-Lieb category, a.k.a. the Brauer category, allows overlapping paths.*)


TL::usage="TL[c,m,n,linear combination of products of P's with
poly(c) coefficients], with n boundary vertices on the right and m on the left.";
TP::usage="TP[i,j] represents an undirected path between i and j.";

TLId::usage="TLId[c,n] gives the identity in TL[c,n,n,...].";
TLE::usage="TLE[c,n,i] gives the generator e_i.";

JWProjector::usage="JWProjector[q,n] gives the TLc Jones-Wenzl Projector
in TL[-q-q^-1,n,n,...]";

TLMakeBasis::usage="TLMakeBasis[c,m,n,Virtual->boolean] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c). Virtual is false by default.";
Options[TLMakeBasis] = {Virtual->False};

TLPermutation::usage="TLPermutation[c,n,perm] gives the (virtual) Temperley-Lieb
element associated to the permutation mapping {1,2,...,n} to perm.";

KauffmanBracket::usage="KauffmanBracket[pd,A] or KauffmanBracket[abstract,A] is
a functor from the abstract category to TL.  It gives the (unnormalized) Kauffman
bracket for scalar-valued diagrams.";

YamadaPoly::usage="YamadaPoly[pd,A] or YamadaPoly[abstract,A] is a functor from
the abstract category to TL, coloring edges with the second Jones-Wenzl projector.";


Begin["`Private`TL`"];

ImpartLinearity[TL, TL[c_,m_,n_,#]&, TL[c,m,n,#]&];

PLeft[TL[_,m_,n_,_]] := m;
PRight[TL[_,m_,n_,_]] := n;

PScalar[TL[_,0,0,val_]] := val;

ClearAll[TP];
SetAttributes[TP, {Orderless}];
TP[i_, i_] := TP[];
TP /: TP[i_,j_] TP[i_,k_] := TP[j,k];
TP /: TP[i_,j_]^2 := TP[];

tlEliminateLoops[c_, v_] := Expand[v, _TP] /. TP[] -> c;

SetAttributes[PComb, {Orderless}];
PComb /: PComb[ps1___] PComb[ps2___] := PComb[ps1, ps2];

PSimplify[TL[c_, m_, n_, v_]] := TL[c, m, n,
	Collect[(tlEliminateLoops[c, v] /. p_TP:>PComb@p), _PComb, Identity] /.
		p_PComb:>Times@@p];

PCoeffs[tl_TL] :=
	Replace[PSimplify@tl, TL[c_,m_,n_,v_]:>
		Replace[v/.p_TP:>PComb@p, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. pc_PComb :> {co, TL[c,m,n,Times@@pc]}]&,{t1,terms}]]];

(*Markov trace*)
PTr[TL[c_, m_, m_, v_], OptionsPattern[]] := With[
	{norm=If[OptionValue[Normalized], c^-m, 1]},
	norm tlEliminateLoops[c, v Times@@Table[TP[i,i+m],{i,m}]]
];

tlRenumber[v_, f_Function] := Expand[v, _TP] /. p_TP:>(f/@p);

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
	] // PSimplify; (* must simplify to eliminate internal vertices *)

TLId[c_, n_] := TL[c, n, n, Times@@Table[TP[i, i+n], {i, n}]];

TLE[c_,n_,i_] /; i<n := TL[c, n, n,
	Times@@Table[If[j==i || j==i+1, Nothing, TP[j, j+n]], {j, n}]
	* TP[i,i+1] TP[i+n,i+n+1]
];

JWProjector[q_, n_] /; n<=1 := TLId[-QuantumInt[q, 2], n];
JWProjector[q_, n_] := JWProjector[q, n] = With[
	{c = -QuantumInt[q, 2],
	 p = JWProjector[q, n-1]},
	p \[CircleTimes] TLId[c,1]
	+ (QuantumInt[q,n-1]/QuantumInt[q,n])
	* (p \[CircleTimes] TLId[c,1]) ** TLE[c, n, n-1] ** (p \[CircleTimes] TLId[c,1])
	// PSimplify
];

tlMakePic[m_,n_,diag_] := Graphics[Join[
	{LightRed, EdgeForm[Thin], Rectangle[{0, 0}, {Max[m, n], Max[m, n]+1}],
		Black},
	tlMakePathPic[m, n, #]&/@diag
]];
tlMakePathPic[m_,n_,TP[i_,j_]] := With[{
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

TL /: MakeBoxes[t:TL[c_, m_, n_, v_], f:StandardForm] :=
	With[{v2 = Expand[v,_TP]
			/.{p_TP:>PComb@p}
			/.{p_PComb:>tlMakePic[m,n,List@@p]}},
		With[{box = RowBox[{"TL", "[", RowBox[{
				MakeBoxes[c,f], ",", MakeBoxes[m,f], ",", MakeBoxes[n,f],",",
				MakeBoxes[v2, f]
			}], "]"}]},
			InterpretationBox[box, t]]];

tlAllPairs[{}] := {1};
tlAllPairs[{x_,xs___}] :=
	ReplaceList[{xs}, {a___,y_,b___} :> Sequence@@(TP[x,y] tlAllPairs[{a,b}])];
tlAllPairs[n_Integer] := tlAllPairs[Range[n]];

tlPlanPairs[{}] := {1};
tlPlanPairs[l_List] /; OddQ[Length[l]] = {};
tlPlanPairs[{x_,xs___}] :=
	ReplaceList[{xs}, {a___,y_,b___} :>
		Sequence@@(TP[x,y] Times@@@Tuples[{tlPlanPairs[{a}], tlPlanPairs[{b}]}])];

TLMakeBasis[c_,m_,n_,OptionsPattern[]] := 
	If[OptionValue[Virtual],
		TL[c,m,n,#]&/@tlAllPairs[m+n],
		TL[c,m,n,#]&/@tlPlanPairs[Join[Range[n], Range[n+m, n+1, -1]]]
	];

TLPermutation::lengthError="Permutation is not the correct length.";
TLPermutation[c_,n_,perm_] := 
	If[n==Length@perm,
		TL[c,n,n,Product[TP[k,#[[k]]+n],{k,1,n}]]&@perm,
		Message[TLPermutation::lengthError]; $Failed	
	];

KauffmanBracket::abv="Cannot handle vertices when colored by weight-1.";
KauffmanBracket[v_] := Module[{A},
	With[{kb=KauffmanBracket[v,A]/.{A->#}}, kb&]];
KauffmanBracket[pd_PD, A_] := KauffmanBracket[FromPD[pd], A];
KauffmanBracket[cat_,A_] := With[{q2=QuantumInt[A^2,2]},
	cat /. {
		AbId[n_] :> TLId[-q2, n],
		AbB[] :> A TLId[-q2, 2] + A^-1 TLE[-q2, 2, 1],
		AbBInv[] :> A^-1 TLId[-q2, 2] + A TLE[-q2, 2, 1],
		AbTrans[] :> TL[-q2,2,2,TP[1,4]TP[2,3]],
		AbCup[] :> TL[-q2,2,0,TP[1,2]],
		AbCap[] :> TL[-q2,0,2,TP[1,2]],
		_AbV /; Message[KauffmanBracket::abv] :> $Failed
	}]//PSimplify;

sndcol[A_,0] := JWProjector[A^(1/2),0];
sndcol[A_,1] := JWProjector[A^(1/2),2];
sndcol[A_,n_] := CircleTimes@@Table[JWProjector[A^(1/2),2],n];

circToBdr[m_,n_,i_] := If[i <= n, i, m+n+1-(i-n)];

YamadaPoly[v_] := Module[{A}, With[{t=YamadaPoly[v,A]/.{A->#}}, t&]];
YamadaPoly[pd_PD, A_] := YamadaPoly[FromPD[pd], A];
YamadaPoly[cat_, A_] := With[{q2=QuantumInt[A^(1/2),2]},
	cat /. {
		AbId[n_] :> sndcol[A,n],
		AbB[] :> sndcol[A,2]**KauffmanBracket[
			(AbId[1]\[CircleTimes] AbB[] \[CircleTimes] AbId[1])
			** (AbB[] \[CircleTimes] AbB[])
			** (AbId[1]\[CircleTimes] AbB[] \[CircleTimes] AbId[1]) ,A^(1/4)],
		AbBInv[] :> sndcol[A,2]**KauffmanBracket[
			(AbId[1]\[CircleTimes] AbBInv[] \[CircleTimes] AbId[1])
			** (AbBInv[] \[CircleTimes] AbBInv[])
			** (AbId[1]\[CircleTimes] AbBInv[] \[CircleTimes] AbId[1]) ,A^(1/4)],
		AbTrans[] :> sndcol[A,2]**TL[-q2,4,4,TP[1,7]TP[2,8]TP[3,5]TP[4,6]],
		AbCup[] :> (sndcol[A,1]\[CircleTimes]TLId[-q2,2])**TL[-q2,4,0,TP[1,4]TP[2,3]],
		AbCap[] :> TL[-q2,0,4,TP[1,4]TP[2,3]]**(sndcol[A,1]\[CircleTimes]TLId[-q2,2]),
		AbV[m_,n_] :> sndcol[A,m]
			** TL[-q2,2 m, 2 n,
				(-q2)^((m+n)/2-1) Times@@Table[
					TP[circToBdr[2m,2n,2i],circToBdr[2m,2n,Mod[2i+1,2(m+n),1]]],{i,m+n}]]
			** sndcol[A,n]
	}]//PSimplify;

End[];


(* ::Section:: *)
(*Flow category*)


Flow::usage="Flow[Q,m,n,linear combination of products of FV's with poly(Q)
coefficients], with n boundary vertices on the right and m on the left.";
FV::usage="FV[i,j,...] is a vertex incident to i,j,....";

FlowMakeBasis::usage="FlowMakeBasis[Q,m,n,Virtual->boolean] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c). Virtual is true by default.";
Options[FlowMakeBasis] = {Virtual->True, Cuttable->False};

FlowId::usage="Flow[Q,m] is the identity in Flow[Q,m,m,...].";

FlowPoly::usage="FlowPoly[PD or abstract cat, Q] is a functor to the flow category.";
QFlowPoly::usage="QFlowPoly[PD or abstract cat, q] is a functor to the flow category
evaluated at q+1+\!\(\*SuperscriptBox[\(q\), \(-1\)]\).";

FlowFlip::usage="FlowFlip[flow] is an involution by flipping
all the indices on each side.";

FlowPermutation::usage="FlowPermutation[Q, perm] gives the (virtual) flow algebra
element associated to the permutation mapping {1,2,...,n} to perm.";

TLToFlow::usage="TLToFlow[tl] embeds (virtual) TL[c,n,m] in Flow[c+1,n,m].";

FlowAProj::usage="FlowAProj[Flow[Q,n,r,...]] projects onto the A_{n,r} module.";


Begin["`Private`Flow`"];

ImpartLinearity[Flow, Flow[Q_,m_,n_,#]&, Flow[Q,m,n,#]&];

PLeft[Flow[_,m_,n_,_]] := m;
PRight[Flow[_,m_,n_,_]] := n;

PScalar[Flow[_,0,0,val_]] := val;

SetAttributes[FV, {Orderless}];
FV[] = 1;
FV[_] = 0;
FV[a_,a_,bs___] := FLoop[] FV[bs];
FV /: FV[a_, b___] FV[a_, c___] := FV[b, c] - FV[b] FV[c];
FV /: FV[a_, b___]^2 := FV[b, b] - FV[b]^2;

flEliminateLoops[Q_, v_] := Expand[v, _FV] /. FLoop[] -> Q - 1;

SetAttributes[FComb, {Orderless}];
FComb /: FComb[fvs1___] FComb[fvs2___] := FComb[fvs1, fvs2];

PSimplify[Flow[Q_,m_,n_,v_]] := Flow[Q, m, n,
	Collect[(flEliminateLoops[Q, v] /. fv_FV:>FComb@fv), _FComb, Identity] /.
		comb_FComb:>Times@@comb];

PCoeffs[fl_Flow] :=
	Replace[PSimplify@fl, Flow[Q_,m_,n_,v_]:>
		Replace[v/.f_FV:>FComb@f, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. fc_FComb :> {co, Flow[Q,m,n,Times@@fc]}]&,{t1,terms}]]];
	
PTr[Flow[Q_,m_,m_,v_], OptionsPattern[]] := With[
	{norm=If[OptionValue[Normalized], (Q-1)^-m, 1]},
	norm flEliminateLoops[Q, v Times@@Table[FV[i,i+m],{i,m}]]
];

flRenumber[v_, f_Function] := Expand[v, _FV] /. fv_FV:>(f/@fv);

PDual[Flow[Q_,m_,n_,v_]] :=
	Flow[Q, n, m, flRenumber[v, If[#<=n, #+m, #-n]&]];

FlowFlip[Flow[Q_,m_,n_,v_]] :=
	Flow[Q, m, n, flRenumber[v, If[#<=n, n+1-#, m+1-(#-n)+n]&]];

FlowPermutation::permError="Invalid permutation";
FlowPermutation[Q_,perm_] /; Sort[perm] == Range@Length@perm :=
	With[{n = Length@perm},
		Flow[Q, n, n,
			Product[FV[k, perm[[k]]+n], {k,1,n}]]];
FlowPermutation[_,_] := (Message[FlowPermutation::permError]; $Failed);

TLToFlow[TL[c_,m_,n_,v_]] := Flow[c+1, m, n, v/.p_TP:>FV@@p];

Flow /: Flow[Q_,m1_,n1_,v1_] \[CircleTimes] Flow[Q_,m2_,n2_,v2_] :=
	Flow[Q, m1+m2, n1+n2,
		flRenumber[v1, If[#<=n1, #, #+n2]&]
		* flRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

Flow /: Flow[Q_,l_,m_,v2_] ** Flow[Q_,m_,n_,v1_] :=
	Flow[Q, l, n,
		flRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* flRenumber[v1, If[#<=n, #, #+l]&]
	] // PSimplify;

FlowId[Q_, n_] := Flow[Q, n, n, Times@@Table[FV[i, i+n], {i, n}]];

flMakePic[m_,n_,diag_List] := Graphics[Join[
	{LightBlue, EdgeForm[Thin], Rectangle[{0, 0}, {2, Max[m,n]+1}], Black},
	Join@@MapIndexed[flMakeVertPic[m, n, #2[[1]]/(1+Length@diag)*(1+Max[m,n]), #1]&,
		diag, {1}]
]];
flMakeVertPic[m_,n_,y_,v_FV] := With[{
	ipt = If[#<=n, {2,#}, {0,#-n}]&},
	Append[Line[{ipt[#],{1,y}}]&/@List@@v, Disk[{1,y}, 0.08]]
];
Flow /: MakeBoxes[fl:Flow[Q_,m_,n_,v_], f:StandardForm] :=
	With[{v2 = Expand[v,_FV]
			/.{fv_FV:>FComb@fv}
			/.{fc_FComb:>flMakePic[m,n,List@@fc]}},
		With[{box = RowBox[{"Flow", "[", RowBox[{
				MakeBoxes[Q,f], ",", MakeBoxes[m,f], ",", MakeBoxes[n,f], ",",
				MakeBoxes[v2,f]
			}], "]"}]},
			InterpretationBox[box, fl]
		]];

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

FlowMakeBasis[Q_,m_,n_,OptionsPattern[]] := Module[{joiner},
	If[OptionValue[Cuttable],
		joiner[idxs_] := With[{
				right=Select[idxs, #<=n&], left=Select[idxs, #>n&]},
			Which[
				right=={}, FV@@left,
				left=={}, FV@@right,
				True, FV[m+n+1, Sequence@@right] FV[m+n+1, Sequence@@left]]];
		,
		joiner[idxs_] := FV@@idxs;
	];
	If[OptionValue[Virtual],
		Map[Flow[Q,m,n,Times@@(joiner/@#)]&,
			Select[SetPartitions[m+n], AllTrue[#, Length[#]>1&]&]],
		Flow[Q,m,n,#]&/@flPlanarPartitions[Join[Range[n],Range[n+m,n+1,-1]]]
	]];

FlowAProj[Flow[Q_,n_,r_,v_]]:=Flow[Q, n, r,
	v /. {
		fv_FV /; Count[fv, i_/;i<=r]>1 :> 0
	}];

FlowPoly::notquantum="Use QFlowPoly for the version with crossings.";
FlowPoly[v_] := Module[{Q}, With[{t=FlowPoly[v,Q]/.{Q->#}}, t&]];
FlowPoly[pd_PD, Q_] := FlowPoly[FromPD[pd], Q];
FlowPoly[cat_, Q_] := (cat /. {
		AbId[n_] :> FlowId[Q, n],
		AbB[]|AbBInv[] /; Message[FlowPoly::notquantum] :> $Failed,
		AbTrans[] :> Flow[Q,2,2,FV[1,4]FV[2,3]],
		AbCup[] :> Flow[Q,2,0,FV[1,2]],
		AbCap[] :> Flow[Q,0,2,FV[1,2]],
		AbV[m_,n_] :> Flow[Q,m,n,FV@@Range[m+n]]
	})//PSimplify;

QFlowPoly[v_] := Module[{q}, With[{t=QFlowPoly[v,q]/.{q->#}}, t&]];
QFlowPoly[pd_PD, q_] := QFlowPoly[FromPD[pd], q];
QFlowPoly[cat_, q_] := With[{Q=q+2+q^-1},
	(cat /. {
		AbId[n_] :> FlowId[Q, n],
		AbB[] :> q FlowId[Q,2] + q^-1 Flow[Q,2,2,FV[1,2]FV[3,4]] - Flow[Q,2,2,FV[1,2,3,4]],
		AbBInv[] :> q^-1 FlowId[Q,2] + q Flow[Q,2,2,FV[1,2]FV[3,4]] - Flow[Q,2,2,FV[1,2,3,4]],
		AbTrans[] :> Flow[Q,2,2,FV[1,4]FV[2,3]],
		AbCup[] :> Flow[Q,2,0,FV[1,2]],
		AbCap[] :> Flow[Q,0,2,FV[1,2]],
		AbV[m_,n_] :> Flow[Q,m,n,FV@@Range[m+n]]
	})]//PSimplify;

End[];


(* ::Section:: *)
(*BFlow category*)


(* ::Text:: *)
(*This is an invariant of virtual graphs, but the same as the flow polynomial for planar graphs.*)


BFlow::usage="BFlow[Q,m,n,linear combination of BFV's with poly(Q)
coefficients], with n boundary vertices on the right and m on the left.";
BFV::usage="BFV[i,j,...] is a flat vertex incident to i,j,... in that order.";

BFlowMakeBasis::usage="BFlowMakeBasis[Q,m,n] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c).";

BFlowId::usage="BFlow[Q,m] is the identity in BFlow[Q,m,m,...].";

BPermutation::usage="BPermutation[Q,n,perm] gives the BFlow
element associated to the permutation mapping {1,2,...,n} to perm.";


Begin["`Private`BFlow`"];

ImpartLinearity[BFlow, BFlow[Q_,m_,n_,#]&, BFlow[Q,m,n,#]&];

PLeft[BFlow[_,m_,n_,_]] := m;
PRight[BFlow[_,m_,n_,_]] := n;

PScalar[BFlow[_,0,0,val_]] := val;

BFV[] = 1;
BFV[_] = 0;
BFV[as___,x_,bs___,x_,cs___] := BFQ[] BFV[cs,as]BFV[bs] - BFV[as,bs,cs];
BFV /: BFV[as___,x_,bs___] BFV[cs___,x_,ds___] :=
	BFV[as, ds, cs, bs] - BFV[as, bs] BFV[cs, ds];
BFV /: (v_BFV)^2 := v v;
BFV[a_,bs__] /; AnyTrue[{bs}, #<a&] := 
	BFV@@RotateLeft[{a,bs},First@Ordering[{bs},1]];

bflEliminateLoops[Q_, v_] := Expand[v, _BFV] /. BFQ[] -> Q;

SetAttributes[BFComb, {Orderless}];
BFComb /: BFComb[fvs1___] BFComb[fvs2___] := BFComb[fvs1, fvs2];

PSimplify[BFlow[Q_,m_,n_,v_]] := BFlow[Q, m, n,
	Collect[(bflEliminateLoops[Q, v] /. fv_BFV:>BFComb@fv), _BFComb, Identity] /.
		comb_BFComb:>Times@@comb];

PCoeffs[fl_BFlow] :=
	Replace[PSimplify@fl, BFlow[Q_,m_,n_,v_]:>
		Replace[v/.f_BFV:>BFComb@f, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. fc_BFComb :> {co, BFlow[Q,m,n,Times@@fc]}]&,{t1,terms}]]];

bflComponents[b_BFlow] := {#[[1]], #[[2]], Count[#[[2]], _BFV, Infinity]}&/@ PCoeffs[b];

PTr[b:BFlow[Q_,m_,m_,v_], OptionsPattern[]] :=
	If[OptionValue[Normalized],
		Plus@@(#[[1]] PTr[#[[2]]] Q^#[[3]]&/@bflComponents[b]), (*TODO*)
		bflEliminateLoops[Q, Expand[v Times@@Table[BFV[i,i+m],{i,m}],_BFV]]];

bflRenumber[v_, f_Function] := Expand[v, _BFV] /. fv_BFV:>(f/@fv);

PDual[BFlow[Q_,m_,n_,v_]] :=(*todo: check if move rule in*)
	BFlow[Q, n, m, bflRenumber[v, If[#<=n, #+m, #-n]&]]/.{b_BFV:>Reverse[b]};

BFlow /: BFlow[Q_,m1_,n1_,v1_] \[CircleTimes] BFlow[Q_,m2_,n2_,v2_] :=
	BFlow[Q, m1+m2, n1+n2,
		bflRenumber[v1, If[#<=n1, #, #+n2]&]
		* bflRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

BFlow /: BFlow[Q_,l_,m_,v2_] ** BFlow[Q_,m_,n_,v1_] :=
	BFlow[Q, l, n,
		bflRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* bflRenumber[v1, If[#<=n, #, #+l]&]
	] // PSimplify;

BFlowId[Q_, n_] := BFlow[Q, n, n, Times@@Table[BFV[i, i+n], {i, n}]];

permutePartition[partition_List]:= Module[{perm},
	ReplaceAll[
		Flatten@Outer[perm[##]&,
			Sequence@@((Prepend[First@#]/@Permutations@Rest@#)&/@partition),1],
		p_perm:>List@@p]];

BFlowMakeBasis[Q_,m_,n_] :=
	Map[BFlow[Q,m,n,Times@@BFV@@@#]&,
		Sequence@@permutePartition[#]&/@
		Select[SetPartitions[m+n], AllTrue[#, Length[#]>1&]&]];

BPermutation::lengthError="Permutation is not the correct length.";
BPermutation[Q_,perm_] := With[{n=Length@perm},
	BFlow[Q,n,n,Product[BFV[k,#[[k]]+n],{k,1,n}]]&@perm];

End[];


(* ::Section:: *)
(*Y category*)


(* ::Text:: *)
(*This is a quantum invariant of virtual spatial graphs. For usual spatial graphs, it is the Yamada polynomial.  For virtual graphs, it is BFlow (the S polynomial) evaluated at Q=(q^(1/2)+q^(-1/2))^2.*)


Y::usage="Y[q,m,n,linear combination of Y's with poly(Q)
coefficients], with n boundary vertices on the right and m on the left.";
YV::usage="YV[i,j,...] is a ribbon vertex incident to i,j,... in that order.";
YX::usage="YX[a,b,c,d] is a crossing.";

YMakeBasis::usage="BFlowMakeBasis[Q,m,n] gives a basis for the
homset from n to m over \[DoubleStruckCapitalC](c).";

YId::usage="YId[q,m] is the identity in Y[q,m,m,...].";


Begin["`Private`Y`"];

ImpartLinearity[Y, Y[q_,m_,n_,#]&, Y[q,m,n,#]&];

PLeft[Y[_,m_,n_,_]] := m;
PRight[Y[_,m_,n_,_]] := n;

PScalar[Y[_,0,0,val_]] := val;

YV[] = 1;
YV[_] = 0;
YV[as___,x_,bs___,x_,cs___] := (YQ[]+2+YQ[]^-1)YV[cs,as]YV[bs] - YV[as,bs,cs];
YV /: YV[as___,x_,bs___] YV[cs___,x_,ds___] :=
	YV[as, ds, cs, bs] - YV[as, bs] YV[cs, ds];
YV /: (v_YV)^2 := v v;
YV[a_,bs__] /; AnyTrue[{bs}, #<a&] := 
	YV@@RotateLeft[{a,bs},First@Ordering[{bs},1]];

YX[a_,b_,c_,d_] := YQ[] YV[a,b]YV[c,d] + YQ[]^-1 YV[a,d]YV[b,c] - YV[a,b,c,d];

yEliminateLoops[q_, v_] := Expand[v, _YV] /. YQ[] -> q;

SetAttributes[YComb, {Orderless}];
YComb /: YComb[fvs1___] YComb[fvs2___] := YComb[fvs1, fvs2];

PSimplify[Y[q_,m_,n_,v_]] := Y[q, m, n,
	Collect[(yEliminateLoops[q, v] /. fv_YV:>YComb@fv), _YComb, Identity] /.
		comb_YComb:>Times@@comb];

PCoeffs[fl_Y] :=
	Replace[PSimplify@fl, Y[q_,m_,n_,v_]:>
		Replace[v/.f_YV:>YComb@f, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. fc_YComb :> {co, Y[q,m,n,Times@@fc]}]&,{t1,terms}]]];
	
PTr[Y[q_,m_,m_,v_], OptionsPattern[]] := 
	yEliminateLoops[q, Expand[v Times@@Table[YV[i,i+m],{i,m}],_YV]];

yRenumber[v_, f_Function] := Expand[v, _YV] /. fv_YV:>(f/@fv);

PDual[Y[q_,m_,n_,v_]] :=
	BFlow[q, n, m, yRenumber[v, If[#<=n, #+m, #-n]&]]/.{b_YV:>Reverse[b]};

Y /: Y[Q_,m1_,n1_,v1_] \[CircleTimes] BFlow[Q_,m2_,n2_,v2_] :=
	Y[Q, m1+m2, n1+n2,
		yRenumber[v1, If[#<=n1, #, #+n2]&]
		* yRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

Y /: Y[Q_,l_,m_,v2_] ** Y[Q_,m_,n_,v1_] :=
	Y[Q, l, n,
		yRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* yRenumber[v1, If[#<=n, #, #+l]&]
	] // PSimplify;

YId[Q_, n_] := Y[Q, n, n, Times@@Table[YV[i, i+n], {i, n}]];

permutePartition[partition_List]:= Module[{perm},
	ReplaceAll[
		Flatten@Outer[perm[##]&,
			Sequence@@((Prepend[First@#]/@Permutations@Rest@#)&/@partition),1],
		p_perm:>List@@p]];

YMakeBasis[Q_,m_,n_] :=
	Map[Y[Q,m,n,Times@@YV@@@#]&,
		Sequence@@permutePartition[#]&/@
		Select[SetPartitions[m+n], AllTrue[#, Length[#]>1&]&]];

End[];


(* ::Section:: *)
(*YF category*)


(* ::Text:: *)
(*This is the Fleming-Mellor invariant of virtual spatial graphs.*)


YF::usage="YF[q,m,n,linear combination of Y's with poly(Q)
coefficients], with n boundary vertices on the right and m on the left.";
YFV::usage="YV[i,j,...] is a ribbon vertex incident to i,j,... in that order.";
YFX::usage="YX[a,b,c,d] is a crossing.";


Begin["`Private`YF`"];

ImpartLinearity[YF, YF[q_,m_,n_,#]&, YF[q,m,n,#]&];

PLeft[YF[_,m_,n_,_]] := m;
PRight[YF[_,m_,n_,_]] := n;

PScalar[YF[_,0,0,val_]] := val;

SetAttributes[YFV,{Orderless}];

YFV[] = 1;
YFV[_] = 0;
HoldPattern[YFV[x_,x_,as___]] := (YFQ[]+1+YFQ[]^-1)YFV[as];
YFV /: HoldPattern[YFV[x_,as___] YFV[x_,bs___]] :=
	YFV[as, bs] - YFV[as] YFV[bs];
YFV /: (v_YFV)^2 := v v;

YFX[a_,b_,c_,d_] := YFQ[] YFV[a,b]YFV[c,d] + YFQ[]^-1 YFV[a,d]YFV[b,c] - YFV[a,b,c,d];

yEliminateLoops[q_, v_] := Expand[v, _YFV] /. YFQ[] -> q;

SetAttributes[YComb, {Orderless}];
YComb /: YComb[fvs1___] YComb[fvs2___] := YComb[fvs1, fvs2];

PSimplify[YF[q_,m_,n_,v_]] := YF[q, m, n,
	Collect[(yEliminateLoops[q, v] /. fv_YFV:>YComb@fv), _YComb, Identity] /.
		comb_YComb:>Times@@comb];

PCoeffs[fl_YF] :=
	Replace[PSimplify@fl, YF[q_,m_,n_,v_]:>
		Replace[v/.f_YFV:>YComb@f, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. fc_YComb :> {co, YF[q,m,n,Times@@fc]}]&,{t1,terms}]]];
	
PTr[YF[q_,m_,m_,v_], OptionsPattern[]] := 
	yEliminateLoops[q, Expand[v Times@@Table[YFV[i,i+m],{i,m}],_YFV]];

yRenumber[v_, f_Function] := Expand[v, _YFV] /. fv_YFV:>(f/@fv);

PDual[YF[q_,m_,n_,v_]] :=
	BFlow[q, n, m, yRenumber[v, If[#<=n, #+m, #-n]&]]/.{b_YFV:>Reverse[b]};

YF /: YF[Q_,m1_,n1_,v1_] \[CircleTimes] BFlow[Q_,m2_,n2_,v2_] :=
	YF[Q, m1+m2, n1+n2,
		yRenumber[v1, If[#<=n1, #, #+n2]&]
		* yRenumber[v2, If[#<=n2, #+n1, #+n1+m1]&]
	];

YF /: YF[Q_,l_,m_,v2_] ** YF[Q_,m_,n_,v1_] :=
	YF[Q, l, n,
		yRenumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* yRenumber[v1, If[#<=n, #, #+l]&]
	] // PSimplify;

End[];


(* ::Section:: *)
(*Deligne partition category*)


DP::usage="DP[t,m,n,linear combination of DS's over \[DoubleStruckCapitalC](t)]";
DS::usage="DS[...] is a subset of m+n";

DPId::usage="DPId[t,n] gives the identity in DP[t,n,n,...].";

DPMakeBasis::usage="DPMakeBasis[t,m,n,AllowSingletons->True] gives a basis
for DP[t,m,n,...].";
Options[DPMakeBasis] = {AllowSingletons->True};


Begin["`Private`DP`"];

ImpartLinearity[DP, DP[t_,m_,n_,#]&, DP[t,m,n,#]&];

PLeft[DP[_,m_,n_,_]] := m;
PRight[DP[_,m_,n_,_]] := n;

PScalar[DP[_,0,0,val_]] := val;

(*These rules make sense in the context of how composition works. DS[] will appear
when there is an internal partition.*)
SetAttributes[DS, {Orderless}];
DS /: DS[a_, xs___] DS[a_, ys___] := DS[xs, ys];
DS[a_,a_,xs___] := DS[xs];
DS /: DS[a_, xs___]^2 := DS[xs, xs];

SetAttributes[DPart,{Orderless}];
DPart /: DPart[ss1___] DPart[ss2___] := DPart[ss1, ss2];

dpEliminateEmpties[t_,v_] := Expand[v, _DS] /. DS[] -> t;

PSimplify[DP[t_,m_,n_,v_]] := DP[t,m,n,
	Collect[(dpEliminateEmpties[t, v] /. d_DS:>DPart@d), _DPart, Identity]
	 /. d_DPart:>Times@@d
];

PCoeffs[dp_DP] :=
	Replace[PSimplify@dp, {DP[_,_,_,0]:>{},
		DP[t_,m_,n_,v_]:>
		Replace[v/.ds_DS:>DPart@ds, HoldPattern[Plus[t1_,terms___]|t1:Except[0]]:>
			Map[Replace[#,co_. dc_DPart :> {co, DP[t,m,n,Times@@dc]}]&,{t1,terms}]]}];

(*TODO should this be normalized?*)
PTr[DP[t_,m_,m_,v_], OptionsPattern[]] := With[
	{norm = If[OptionValue[Normalized], t^-m, 1]},
	norm dpEliminateEmpties[t, v Times@@Table[DS[i,i+m],{i,m}]]
];

dsRenumber[v_, f_Function] := Expand[v, _DS] /. d_DS:>(f/@d);

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
	] // PSimplify; (* must simplify to eliminate internal partitions *)

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

DPMakeBasis[t_,m_,n_,OptionsPattern[]] := Map[
	If[OptionValue[AllowSingletons] || AllTrue[#,Length[#]>=2&],
		DP[t,m,n,Times@@DS@@@#],
		Nothing]&,
	SetPartitions[m+n]];

End[];


(* ::Section:: *)
(*End of definitions*)


Print["Loaded ",$Context];
EndPackage[];
