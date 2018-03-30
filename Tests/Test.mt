(* Wolfram Language Test file *)

Test[
	With[{p = JWProjector[q, 5]},
		p ** p - p // PSimplify // Simplify
 	]
	,
	TL[-((1 + q^2)/q), 5, 5, 0]
	,
	TestID->"Test-20180130-E0J4M3"
]

Test[
	With[{gram = Gramian[FlowMakeBasis[Q, 2, 2, Virtual -> False]] /. Q -> (1 + Sqrt[5])/2 + 1},
 		Det[gram]]
	,
	0
	,
	TestID->"Test-20180130-T8H2O2"
]

Test[
	PScalar[YamadaPoly[PD[V[1, 1, 2], V[2, 3, 3]], A]] // Simplify
	,
	0
	,
	TestID->"Test-20180130-H8S6J3"
]

Test[
	YamadaPoly[AbV[2, 1] ** AbV[1, 2] - (AbV[2, 2] - AbCup[] ** AbCap[]), A] // Simplify
	,
	TL[(-1 - A)/Sqrt[A], 4, 4, 0]
	,
	TestID->"Test-20180130-H0X0R3"
]

Test[
	With[{pd = FlatVertG["theta"]},
 		PScalar@YamadaPoly[pd, A] - PScalar@QFlowPoly[pd, A] // FullSimplify]
	,
	0
	,
	TestID->"Test-20180130-C6J0Y5"
]

Test[
	With[{tlb = TLMakeBasis[Q - 1, 3, 3, Virtual -> False]},
		Union@Flatten@Table[TLToFlow[tlb[[i]]] ** TLToFlow[tlb[[j]]] - TLToFlow[tlb[[i]] ** tlb[[j]]] // PSimplify,
			{i, Length@tlb}, {j, Length@tlb}]]
	,
	{Flow[Q, 3, 3, 0]}
	,
	TestID->"Test-20180226-Q3Y2T4"
]