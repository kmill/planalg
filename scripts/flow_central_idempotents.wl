(* ::Package:: *)

(* ::Text:: *)
(*Calculate primitive central idempotents in Flow[Q,n,n] (virtual or not)*)


<<Planalg`

(*Symmetrize with respect to dihedral action.*)
FSymmetrize[f_Flow]:=PSimplify[(f+PDual[f]+FlowFlip[f]+PDual[FlowFlip[f]])/4];


(*configuration*)
n=2;
virtual=True;

fbasis=FlowMakeBasis[Q,n,n,Virtual->virtual];
basis=Union[FSymmetrize/@fbasis];
Print["Dimension of Flow[Q,",n,",",n,"] (",If[virtual,"virtual","planar"],"): ",
	Length@fbasis, " with symmetrized dimension ", Length@basis];

(*coefficient variables to solve for*)
coeffs=Array[a,Length@basis];
(*element represented by coeffs*)
elt=coeffs.basis;

(*idempotent-ness*)
idemcs=Union@Expand[Thread[(First/@PCoeffs[elt**elt-elt])==0]];
(*centrality*)
commcs=Union@Expand@Flatten@Map[Thread[First/@PCoeffs[#**elt-elt**#]==0]&,fbasis];

cs=Union[idemcs,commcs];
Print["Length of coefficient equation list: ",Length@cs];
Print["Solving..."]
Print["Solved in ", Timing[solns=Solve[cs,coeffs];][[1]], " seconds"];

solns=FullSimplify[solns,Q>1];

CarefulComplement[set1_,set2_]:=Select[set1,
	Function[elt, !Or@@(True===Reduce[ForAll[Q,Q>1,
		#==elt]]&/@set2)]];

Print["Finding primitives..."];
Print["Found in ", Timing[
primZIdems=With[
	{vecs=Cases[Simplify[coeffs/.solns,Q>1],Except[{0..}]]},
	CarefulComplement[vecs,
		Flatten[Table[vecs[[i]]+vecs[[j]],
			{i,Length@vecs},{j,i+1,Length@vecs}],1]]];
][[1]], " seconds"];
Print["Coefficients of primitive idempotents with respect to symmetrized basis: ",
	primZIdems];

Print["Calculating simplified Flow elements..."];
Print["Calculated in ", Timing[
idems=PSimplify[#.basis]&/@primZIdems//Simplify;
][[1]], " seconds"];

Print["Found ",Length@idems," primitive idempotents:"];
Print[idems];

(* Plus@@(PTr[#,Normalized\[Rule]False]&/@idems)//FullSimplify \[Equal] (Q-1)^n *)
(* Outer[NonCommutativeMultiply,idems,idems]//FullSimplify//MatrixForm *)



