# Planalg

This is a Mathematica package for working with planar algebras and categories.

To use: either

- open Planalg/Planalg.wl in Mathematica and click Run All Code

or either

- copy the Planalg directory to
`$UserBaseDirectory/Applications`

- or add the following line to your
`$UserBaseDirectory/Kernel/init.m` file:
```
    PrependTo[$Path, "a directory that contains the Planalg directory"]
```

Then, evaluate ``<<Planalg` `` in Mathematica to load the application.

## Example

Calculate the determinant of the Gram matrix for the chromatic algebra on three strands:
```
basis = FlowMakeBasis[Q, 3, 3, Virtual -> False];
gram = MakeGramian[basis];
Det[gram] // Factor
```

Calculate using an unnormalized trace
```
TableForm@
 Table[Gramian[FlowMakeBasis[Q, n, 0, Virtual -> True], 
         Trace -> (PTr[#, Normalized -> False] &)] // Det // Factor,
       {n, 2, 6}]
```
