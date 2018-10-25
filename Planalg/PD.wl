(* ::Package:: *)

BeginPackage["Planalg`PD`", {"Planalg`"}];
ClearAll["Planalg`PD`*", "Planalg`PD`*`*"];

tref=PD[Xp[1,5,2,4],Xp[5,3,6,2],Xp[3,1,4,6]];
fig8=PD[Xm[1,6,2,7],Xm[5,2,6,3],Xp[3,1,4,8],Xp[7,5,8,4]];

toFrag::usage="";
fragRot::usage="";
contiguousQ::usage="";
contiguousBdry::usage="";
findBest::usage="";
doJoins::usage="";

PDRot::usage="PDRot[elt, n] represents rotating element n counterclockwise";
PDJoin::usage="PDJoin[elt1, elt2, n] represents joining elements along n inner edges";

MakePDComp::usage="MakePDComp[pd]";


(* ::Text:: *)
(*Convert an (un)oriented PD into a categorical composition.  This is a tree of Xp, Xm, P, PDRot, and PDJoin.  It is meant to be converted to whatever category one might be interested in.*)


Begin["`Private`"];

toFrag[pd_PD] :=
	List@@pd /. {
		x_Xp :> frag[List@@x, Xp[]],
		x_Xm :> frag[List@@x, Xm[]],
		p_P :> frag[List@@p, P[]]
	};

(* rotate counter-clockwise by n *)
(*fragRot[frag[bdry_, PDRot[x_,m_]], n_] := fragRot[frag[RotateLeft[bdry,m],x], n+m];*)
fragRot[frag[bdry_, x_], n_] := With[{m=Mod[n,Length@bdry,-Floor[Length@bdry/2]]},
	If[m==0,
		frag[bdry, x],
		frag[RotateRight[bdry, n],
			PDRot[x,m]]]];

(* check if the elts form a contiguous region in bdry,
   which is taken to be a cyclic list.
   Assume elts is non-empty. *)
contiguousQ[bdry_,elts_] := Length@SplitBy[bdry, MemberQ[elts,#]&] <= 3;
(* returns {bdry in elts, rest of boundary}, after cyclic shift *)
contiguousBdry[bdry_,elts_] := With[{spl=SplitBy[bdry, MemberQ[elts,#]&]},
	Replace[spl, {
		{m_} :> {m,{}},
		{m1_,m2_} :> If[MemberQ[m1,elts[[1]]], {m1,m2}, {m2,m1}],
		{m1_,m2_,m3_} :> If[MemberQ[m1,elts[[1]]] || MemberQ[m3,elts[[1]]],
							{Join[m3,m1],m2},
							{m2,Join[m3,m1]}],
		_ :> Return[$Failed]
	}]];

(* put decomposed boundaries into form where sb1\[Equal]Reverse[sb2], if possible *)
tryMakeReversed[{sb1_,rb1_},{sb2_,{}}] := With[{pos=First@FirstPosition[sb2, sb1[[1]]]},
	{{sb1,rb1},{RotateLeft[sb2,pos],{}}}];
tryMakeReversed[{sb1_,{}},{sb2_,rb2_}] := With[{pos=First@FirstPosition[sb1, sb2[[1]]]},
	{{RotateLeft[sb1,pos],{}}, {sb2,rb2}}];
tryMakeReversed[b1_,b2_] := {b1,b2};

(* determine shared boundary, if one exists. *)
sharedBdry::incompatibleBoundaries="The boundaries have a shared component that is
not planar.";
sharedBdry[bdry1_, bdry2_] := With[{shared=bdry1\[Intersection]bdry2},
	If[Length@shared>0 && contiguousQ[bdry1, shared] && contiguousQ[bdry2, shared],
		With[{bs=tryMakeReversed[contiguousBdry[bdry1, shared],
								contiguousBdry[bdry2, shared]]},
			If[Not@SameQ[bs[[1,1]], Reverse[bs[[2,1]]]],
				Message[sharedBdry::incompatibleBoundaries]];
			bs],
		Null]];

(*returns best match[shared bdry x, shared bdry y, x, y] or nomatch[] *)
findBest[frs_List] :=
	Replace[
		MaximalBy[ReplaceList[frs, {
				{frs1___, x:frag[xb_,_], frs2___, y:frag[yb_,_], frs3___} :>
					With[{sb=sharedBdry[xb,yb]},
						If[SameQ[Null, sb],
							Nothing,
							match[Length@sb[[1,1]], sb, x, y]]]
			}], First, UpTo[1]], {
		{} :> nomatch[],
		{match[_, {sbx_,sby_}, x_, y_]} :> match[sbx[[1]], sby[[1]], x, y],
		_ :> Return[$Failed]
	}];

(* rotate boundary so that the shared boundary is all the way to the right or left *)
fragRotBdryToRight[sb_, f:frag[bdry_,x_]] :=
	With[{pos=First@FirstPosition[bdry,sb[[-1]]]},
		fragRot[f,-pos]];
fragRotBdryToLeft[sb_, f:frag[bdry_,x_]] :=
	With[{pos=First@FirstPosition[bdry,sb[[1]]]},
		fragRot[f,1-pos]];

(* create PDJoin representing the join of two fragments; n is number of edges to glue *)
fragJoin[frag[bx_,x_],frag[by_,y_], n_] :=
	frag[bx[[;;-n-1]]~Join~by[[n+1;;]], PDJoin[x,y,n]];

(* find best matches and join up *)
fragJoin[frs_List] :=
	Replace[findBest[frs], {
		match[sbx_, sby_, x_, y_] :>
			Append[
				Cases[frs,Except[x|y]],
				fragJoin[
					fragRotBdryToRight[sbx, x],
					fragRotBdryToLeft[sby, y],
					Length@sbx]],
		nomatch[] -> Null
	}];

doJoins[frs_List] :=
	Replace[fragJoin[frs], {
		Null -> frs,
		frs2_List :> doJoins[frs2]
	}];

fragRotMin[f:frag[bdry_,x_]] :=
	With[{pos=First@Ordering[bdry,1]},
		fragRot[f,1-pos]];

MakePDComp[pd_PD] := With[{joins=doJoins[toFrag[pd]]},
	With[{empties=Cases[joins, frag[{},_]],
		nonempties=SortBy[fragRotMin/@Cases[joins, Except[frag[{},_]]], Min[#[[1]]]&]
		},
		Replace[Fold[fragJoin[#1,#2,0]&, Join[empties,nonempties]], {
			frag[_,x_] :> x,
			_ :> Return[$Failed]
		}]]];

End[];


EndPackage[];
