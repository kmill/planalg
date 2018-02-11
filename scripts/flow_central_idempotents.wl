(* ::Package:: *)

(* ::Text:: *)
(*Calculate primitive central idempotents in Flow[Q,n,n] (virtual or not)*)


(*Symmetrize with respect to dihedral action.*)
FSymmetrize[f_Flow]:=PSimplify[f+PDual[f]+FlowFlip[f]+PDual[FlowFlip[f]]];


(*configuration*)
n=2;
virtual=True;

basis=Union[FSymmetrize/@FlowMakeBasis[Q,n,n,Virtual->virtual]];
Print["Dimension of Flow[Q,",n,",",n,"] (",If[virtual,"virtual","planar"],"): ",
	Length@basis];

(*coefficient variables to solve for*)
coeffs=Array[a,Length@basis];
(*element represented by coeffs*)
elt=coeffs.basis;

(*idempotent-ness*)
idemcs=Union@Expand[Thread[(First/@PCoeffs[elt**elt-elt])==0]];
(*centrality*)
commcs=Union@Expand@Flatten@Map[Thread[First/@PCoeffs[#**elt-elt**#]==0]&,basis];

cs=Union[idemcs,commcs];
Print["Length of coefficent equation list: ",Length@cs];
Print["Solving..."]
Print["Solved in ", Timing[solns=Solve[cs,coeffs];][[1]], " seconds"];

primZIdems=With[
	{vecs=Cases[coeffs/.solns//FullSimplify,Except[{0..}]]},
	Complement[vecs,
		FullSimplify@Flatten[Table[vecs[[i]]+vecs[[j]],
			{i,Length@vecs},{j,i+1,Length@vecs}],1]]];
Print["Coefficients of primitive idempotents with respect to symmetrized basis: ",
	primZIdems];

idems=PSimplify[#.basis]&/@primZIdems//FullSimplify;

Print["Primitive idempotents:"];
Print[idems];



