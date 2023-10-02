# Linear Core

Linear type systems guarantee linear resources are used *exactly once*.
Traditionally, using a resource is synonymous with its *syntactic*
occurrence in the program, however, under the lens of *lazy* evaluation,
linearity can be further understood *semantically*, where a
syntactic occurrence of a resource does not necessarily entail
*using* that resource when the program is evaluated.

Semantic linearity is especially necessary in optimising compilers for
languages combining linearity and laziness: optimisations leverage laziness to
heavily rewrite the source program, pushing the interaction of linearity and
laziness to its limit, regardless of the original program typing linearity
conservatively.

We present Linear Core, the first type system that understands semantic
linearity in the presence of laziness, suitable for the Core intermediate
language of the Glasgow Haskell Compiler. We prove Linear Core is both type
safe and that multiple optimising transformations preserve linearity in Linear
Core while failing to do so in Core. We have implemented Linear Core as a
compiler plugin to validate the system against established libraries, including
`linear-base`, in the heart of the compiler.

