(* ::Package:: *)

BeginPackage["Planalg`HOMFLYPT`", {"Planalg`"}];
ClearAll["Planalg`HOMFLYPT`*", "Planalg`HOMFLYPT`*`*"];


(* ::Text:: *)
(*This is a version of a planar algebra for the HOMFLY polynomial where*)


(* ::Item:: *)
(*a Right - a^-1 Left = z Zero*)


(* ::Item:: *)
(*Unknot = (a-a^-1)/z*)


(* ::Item:: *)
(*Disjoint unions are multiplicative*)


(* ::Text:: *)
(*The boundary edges are numbered in increasing order from the bottom right up, then from the top left down; counterclockwise.*)


(* ::Text:: *)
(*This is the parameterization used by the Knot Atlas.  We normalize the trace (and PScalar) by the value of the unknot so that the value of the unknot is 1.*)


(* ::Text:: *)
(*PDual is a reflection plus orientation reversal, with no change in coefficients.*)


(* ::Section:: *)
(*HOMFLY-PT polynomial*)


HOMFLYPT::usage="HOMFLYPT[a,z,left signs, right signs, diagrams]";
HD::usage="HD[i1,j1, i2,j2, i3,j3, ... strands from top to bottom]";

Hright[a_,z_]:=HOMFLYPT[a,z,{1,1},{1,1},HD[1,3, 2,4]];
Hzero[a_,z_]:=HOMFLYPT[a,z,{1,1},{1,1},HD[1,4, 2,3]];
Hleft[a_,z_]:=a^2 Hright[a,z] - z a Hzero[a,z];

Hid::usage="Hid[a,z,s] gives identity with signs given by s";

Hunknot::usage="Hunknot[a,z] gives the scalar for an unknot connect summand.";
Hunknot[a_,z_] := (a-a^-1)/z;

Hmirror::usage="Hmirror[_HOMFLYPT] does a->a^{-1}, z->-z,
and reverses all the crossing types";
Hreverse::usage="Hreverse[_HOMFLYPT] reverses the orientations of each arc";


Begin["`Private`HOMFLYPT`"];

ImpartLinearity[HOMFLYPT, HOMFLYPT[a_,z_,sl_,sr_,#]&, HOMFLYPT[a,z,sl,sr,#]&];

PLeft[HOMFLYPT[_,_,sl_,sr_,_]] := sl;
PRight[HOMFLYPT[_,_,sl_,sr_,_]] := sr;
PScalar[HOMFLYPT[a_,z_,{},{},val_]] := concretizeVars[a,z,val]/Hunknot[a,z];

concretizeVars[a_,z_,exp_] := exp/.{Ha[]->a,Hz[]->z};

(* Create a list of {coeff,HD} pairs from a linear combination. *)
(* A sort of inverse to Plus@@Times@@@ *)
uncomb[0] = {};
uncomb[coeff_. d_HD] := {{coeff, d}};
uncomb[x_Plus] := Replace[#, coeff_. d_HD:>{coeff, d}]& /@ (List@@x);

(* extract path i from HD *)
hp[d_HD, i_Integer] := {d[[2i-1]],d[[2i]]};

(* take path number i and lift it over path i-1.  1<i\[LessEqual]#paths *)
hlift[diag_HD, i_Integer] := With[{p1 = hp[diag,i], p2=hp[diag,i-1]},
	(*p1 is lower than p2*)
	With[{a=p1[[1]],b=p1[[2]], c=p2[[1]],d=p2[[2]]},
		Plus@@Map[Function[df,
				df[[1]] * Join[diag[[;;2i-4]],df[[2]],diag[[2i+1;;]]]],
			Which[ (* by drawing out all possible diagrams. *)
					(* changes in second term are for normalization only*)
				a<c<b<d || d<a<c<b,
					{{Ha[]^2,HD[a,b,c,d]}, {-Hz[] Ha[],HD[a,d,c,b]}},
				c<b<d<a || b<d<a<c,
					{{Ha[]^2,HD[a,b,c,d]}, {-Hz[] Ha[],HD[c,b,a,d]}},
				a<d<b<c || d<b<c<a,
					{{Ha[]^-2,HD[a,b,c,d]}, {Hz[] Ha[]^-1,HD[a,d,c,b]}},
				b<c<a<d || c<a<d<b,
					{{Ha[]^-2,HD[a,b,c,d]}, {Hz[] Ha[]^-1,HD[c,b,a,d]}},
				True, {{1,HD[a,b,c,d]}}
			]]]];

hlower[diag_HD, i_Integer] := hlift[diag, i+1];

Module[{hnormalize1},
	hnormalize1[exp_] :=
		ReplaceAll[exp,
			d_HD :> Replace[FirstPosition[Table[Min[hp[d,i]] > Min[hp[d,i+1]],
											{i,1,Length@d/2-1}],
								True], {
				_Missing -> d,
				{i_Integer} :> hnormalize1[hlift[d,i+1]]
			}]];
	hnormalize[exp_] := Collect[hnormalize1@exp, _HD];
];

(*get pair id (as understood by hp) that contains endpoint s*)
hstrandidx[d_HD, s_Integer] := Floor[(1+FirstPosition[d,s][[1]])/2];

(*Lift lower thing until strands with a and b are next to each other. returns lin.comb.*)
hnextify[exp_,a_Integer,b_Integer] :=
	ReplaceAll[exp, d_HD :>
		With[{i=hstrandidx[d,a], j=hstrandidx[d,b]},
			Which[
				i+1<j, hnextify[hlift[d,j], a, b],
				j+1<i, hnextify[hlift[d,i], a, b],
				True, d]]];

(*assumes a and b are next to each other in boundary. returns lin.comb.*)
(*assumes nothing about orientations of a and b other than they are opposite.*)
hconnect[exp_,a_Integer,b_Integer] :=
	ReplaceAll[hnextify[exp,a,b], d_HD :>
		With[
			{i=hstrandidx[d,a], j=hstrandidx[d,b]},
			If[i==j,
				Hunknot[Ha[],Hz[]] Join[d[[;;2i-2]], d[[2i+1;;]]],
				With[{k=Min[i,j]},
					Join[
						d[[;;2k-2]],
						(*know a,b have different orientations*)
						If[d[[2k-1]]==a || d[[2k-1]]==b,
							HD[d[[2k+1]], d[[2k]]],
							HD[d[[2k-1]], d[[2k+2]]]
						],
						d[[2k+3;;]]
					]
				]
			]]];

(* second argument is connection plan. each pair must be next to each other
   in boundary and have opposite orientations (in unspecified order) *)
hjoin[exp_, {}] := exp;
hjoin[exp_, {{a_,b_},rest___}] :=
	hjoin[Collect[hconnect[exp, a, b], _HD], {rest}];

HOMFLYPT /: HOMFLYPT[a_,z_,s1_,s2_,v1_] ** HOMFLYPT[a_,z_,s2_,s3_,v2_] :=
	HOMFLYPT[a, z, s1, s3, concretizeVars[a,z,hnormalize[
		With[{v1shift =
				ReplaceAll[hnormalize@v1, d_HD :>
					ReplaceAll[d, i_Integer :> i+Length@s2+Length@s3]]},
			ReplaceAll[
				hjoin[
					Plus@@Flatten@Outer[#1[[1]]*#2[[1]]*Join[#2[[2]],#1[[2]]] &,
						uncomb[v1shift], uncomb[hnormalize@v2], 1],
					Table[{Length@s3+Length@s2-i+1, i+Length@s2+Length@s3},
						{i,Length@s2}]],
				d_HD :> ReplaceAll[d, i_Integer :>
							If[i <= Length@s3, i, i-2 Length@s2]]]
		]]]];

HOMFLYPT /: HOMFLYPT[a_,z_,sl1_,sr1_,v1_] \[CircleTimes] HOMFLYPT[a_,z_,sl2_,sr2_,v2_] :=
	HOMFLYPT[a,z,Join[sl1,sl2],Join[sr1,sr2],
		hnormalize[Plus@@Flatten@
		Outer[#1[[1]]*#2[[1]]*Join[
				ReplaceAll[#1[[2]], i_Integer :>
					If[i <= Length@sr1, i, i+Length@sr2+Length@sl2]],
				ReplaceAll[#2[[2]], i_Integer :> i+Length@sr1]
			] &,
			uncomb[hnormalize@v1],uncomb[hnormalize@v2], 1]]];

PSimplify[HOMFLYPT[a_,z_,sl_,sr_,x_]] := HOMFLYPT[a,z,sl,sr,
	concretizeVars[a,z,hnormalize@x]];

PTr[HOMFLYPT[a_,z_,s_,s_,x_]] :=
	ReplaceAll[
		concretizeVars[a,z,
			hjoin[x, Table[{i+Length@s, Length@s+1-i}, {i,Length@s}]]],
		{ HD[] -> 1 }] / Hunknot[a,z];

PDual[HOMFLYPT[a_,z_,sl_,sr_,x_]] :=
	HOMFLYPT[a,z,sr,sl,
		hnormalize@
		ReplaceAll[x, d_HD :>
			With[{d2=ReplaceAll[d, i_Integer :> Length@sl+Length@sr+1 - i]},
				HD@@Table[d2[[i+1-2*Mod[i+1,2]]], {i,Length@d2}]
			]]];

PCoeffs[HOMFLYPT[a_,z_,sl_,sr_,x_]] :=
	{#[[1]],HOMFLYPT[a,z,sl,sr,#[[2]]]}&/@uncomb[concretizeVars[a,z,hnormalize[x]]]

Hid[a_,z_,{}] := HOMFLYPT[a,z,{},{},HD[]];
Hid[a_,z_,{1,s___}] := HOMFLYPT[a,z,{1},{1},HD[1,2]]\[CircleTimes]Hid[a,z,{s}];
Hid[a_,z_,{-1,s___}] := HOMFLYPT[a,z,{-1},{-1},HD[2,1]]\[CircleTimes]Hid[a,z,{s}];

Hmirror[HOMFLYPT[a_,z_,sl_,sr_,x_]] :=
	HOMFLYPT[a,z,sl,sr, x/. {
		a -> a^-1,
		z -> -z,
		d_HD :> Join@@Reverse@Partition[d,2]
	}];
Hreverse[HOMFLYPT[a_,z_,sl_,sr_,x_]] :=
	HOMFLYPT[a,z,-sl,-sr, x/. {
		d_HD :> HD@@Table[d[[i+1-2*Mod[i+1,2]]], {i,Length@d}]
	}];

hMakePic[sl_List,sr_List,d_HD] := Interpretation[
	With[{m=Length@sl,n=Length@sr},
		Graphics[{
			White,Rectangle[{0,0},{Max[m,n],Max[m,n]+1}],Black,
			Arrowheads[0.15],
			Table[hMakePathPic[i,m,n,hp[d,i]], {i,Length@d/2,1,-1}],
			Transparent,EdgeForm[Thin],Rectangle[{0,0}, {Max[m,n],Max[m,n]+1}]
		}]],
	d];

Module[{mkline},
	mkline[g_] := {
		Thickness[0.1],White,g,Thickness[Medium],Black,Arrow@g
	};
hMakePathPic[depth_,m_,n_,{a_,b_}] := With[{
		d = 2 Abs[If[a<=n,a,m+1-(a-n)]-If[b<=n,b,m+1-(b-n)]]/3,
		w = Max[m,n]
	},
	Which[
		a<=n && b<=n,
		mkline@BezierCurve[{{w,a},{w-d,a},{w-d,b},{w,b}}],

		a<=n,
		mkline@BezierCurve[{{w,a},{w-d,a},{d,m+1-(b-n)},{0,m+1-(b-n)}}],
		
		b<=n,
		mkline@BezierCurve[{{0,m+1-(a-n)},{d,m+1-(a-n)},{w-d,b},{w,b}}],

		True,
		mkline@BezierCurve[{{0,m+1-(a-n)},{d,m+1-(a-n)},{d,m+1-(b-n)},{0,m+1-(b-n)}}]
	]];
];

HOMFLYPT /: MakeBoxes[hom:HOMFLYPT[a_,z_,sl_,sr_,exp_], f:StandardForm] :=
	With[{exp2 = concretizeVars[a,z,hnormalize[exp]] /. d_HD:>hMakePic[sl,sr,d]},
	With[{box = RowBox[{"HOMFLYPT", "[",
			RowBox[{MakeBoxes[a,f], ",", MakeBoxes[z,f], ",",
				MakeBoxes[sl,f], ",", MakeBoxes[sr,f], ",",
				MakeBoxes[exp2,f]
			}],
			"]"}]},
		InterpretationBox[box, hom]]];

End[];


EndPackage[];
