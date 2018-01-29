# Planalg

This is a Mathematica package for working with planar algebras and categories.

To use: either

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
	gram = MakeGramian[bas];
	Det[gram] // Factor
```
