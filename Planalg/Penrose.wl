(* ::Package:: *)

BeginPackage["Planalg`Penrose`", {"Planalg`"}];
ClearAll["Planalg`Penrose`*", "Planalg`Penrose`*`*"];


(* ::Section:: *)
(*sl(N) polynomial*)


SL::usage="SL[N,m,n,linear combinations of SLV]";
SLV::usage="SLV[+-1,i,j,...]";


Begin["`Private`SL`"];

ImpartLinearity[SL, SL[N_,m_,n_,#]&, SL[N,m,n,#]&];

PLeft[SL[_,m_,n_,_]] := m;
PRight[SL[_,m_,n_,_]] := n;
PScalar[SL[_,0,0,val_]] := val;

SLV /: SLV[s_, as___,x_,bs___] SLV[t_, cs___,x_,ds___] :=
	(SLV[s t, as,ds,cs,bs] + t SLV[s t, bs,as,Sequence@@Reverse[{ds,cs}]]
	- SLV[s,as,bs]SLV[t,cs,ds]);
SLV /: (v_SLV)^2 := v v;
SLV[s_] := If[s>0, 2, 0];
SLV[_,_] = 0;
SLV[s_, as___,x_,bs___,x_,cs___] :=
	(SLN[]^2/2)(SLV[s,as,cs]SLV[1,bs] + SLV[-s,as,cs]SLV[-1,bs]) - SLV[s,as,bs,cs];

slEliminateVars[N_, v_] := Expand[v, _SLV] /. SLN[] -> N;

HoldPattern[normalize[SLV[s_, x_]]] := SLV[s,x];
HoldPattern[normalize[SLV[s_, bs___]]] := With[{
	least = RotateLeft[{bs}, -1+First@Ordering[{bs},1]]},
	With[{least2 = Prepend[Reverse[least[[2;;]]], least[[1]]]},
		If[least[[2]] < least2[[2]],
			SLV[s,Sequence@@least],
			s SLV[s,Sequence@@least2]]]];

SetAttributes[Comb, {Orderless}];
Comb /: Comb[fvs1___] Comb[fvs2___] := Comb[fvs1, fvs2];

PSimplify[SL[N_,m_,n_,v_]] := SL[N,m,n,
	Collect[(slEliminateVars[N,v] /. fv_SLV:> Comb[normalize[fv]]), _Comb, Identity] /.
		comb_Comb:>Times@@comb];

renumber[v_, f_Function] := Expand[v, _SLV] /. HoldPattern[SLV[s_,xs___]]:>SLV[s,Sequence@@Map[f,{xs}]];

SL /: SL[N_,l_,m_,v2_] ** SL[N_,m_,n_,v1_] :=
	SL[N, l,n,
		renumber[v2, If[#<=m, #+l+n, #-m+n]&]
		* renumber[v1, If[#<=n, #, #+l]&]
	]//PSimplify;

PTr[b:SL[N_,m_,m_,v_], OptionsPattern[]] :=
	slEliminateVars[N, Expand[v Times@@Table[SLV[+1,i,i+m],{i,m}],_SLV]];
PDual[SL[N_,m_,n_,v_]] :=
	SL[N,n,m, renumber[v, If[#<=n,#+m,#-n]&]/.
		{HoldPattern[SLV[s,xs___]]:>SLV[s,Sequence@Reverse[{xs}]]}];

End[];


EndPackage[];
